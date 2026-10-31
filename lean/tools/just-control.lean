module
/-
# Obend.Slot.PolySlot — the slot's eligibility as the evaluation of one polynomial (experiment E1)

The experiment of `review/SYNTHESIS-20261031.md` §10 E1, with Astra's corrections
(`astra/ASTRA-EVAL-20261031.md`): a candidate's justification is the monomial of its judge token and
its support tokens (`poly`), eligibility is its Boolean evaluation (`usable`), and `read`, `select`,
`resolve` and the stored transition (`advance`) take eligibility from it. The ordered observations
(`Slot.dead`, `Slot.evidence`, the order of the refusal) are the existing lists, unchanged: a
normalized monomial has one token per support and no order (`dup_normal`).

Every theorem of `Slot.lean`, `Slot/World.lean` and `Slot/Integrity.lean` whose statement mentions the
redefined `usable`, `alternatives`, `read`, `select`, `resolve` or `advance` is re-proved below against
these definitions, from the lattice lemmas of `Obend.Just` (`Raw.eval_bool`, `Raw.eval_congr`,
`Mono.eval_zero_tok`), with the originals' pins and `#tooth` mutations. Theorems about `dead`,
`evidence`, `Permanent`, `Reaches`, `RunsR` and the World's laws are untouched by the redefinition and
are not repeated. The integrity statements are mirrored with the redefined `alternatives`/`usable`
(`PIntegrity.*`). The bridges `usable_eq`, `read_eq`, `select_eq`, `advance_eq` show the redefinition
is observationally the original. The dual evaluation of a candidate's polynomial is its judge token
when the judge fails followed by its dead supports, in order (`missing_eq`).

The line counts for the gate are in `lean/docs/REPORT-JUST-20261031.md` §3.
-/
public import Obend.Slot.Integrity
import all Obend.Slot.Integrity
@[expose] public section

namespace Obend.Slot.Control
open Obend.Slot Obend.Slot.World

section
variable {Fact Cand : Type}

def usable (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) : Bool := S.judge c && (S.dead holds c).isEmpty

def alternatives (S : Slot Fact Cand) (holds : Fact → Bool) (cands : List Cand) : List Cand :=
  cands.filter (usable S holds)

def read (S : Slot Fact Cand) (holds : Fact → Bool) : Option Cand → Reading Fact Cand
  | none => .empty
  | some c => if usable S holds c then .usable c (S.evidence holds c)
    else if S.judge c then .blocked c (S.dead holds c) else .rejected c

def select (S : Slot Fact Cand) (holds : Fact → Bool) (order : List Cand) : Except (Refusal Fact Cand) Cand :=
  match alternatives S holds order with
  | c :: _ => .ok c
  | [] => .error (order.map fun c => (c, S.dead holds c))

def resolve {Ix : Type} {Sg : Protocol.Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    (S : Slot Fact Cand) (holds : Fact → Bool) {i : Ix} (body : Cand → Protocol.Prot Sg Hole A i)
    (order : List Cand) : Except (Refusal Fact Cand) (Protocol.Prot Sg Hole A i) :=
  (select S holds order).map body

def advance (S : Slot Fact Cand) (holds : Fact → Bool) (order : List Cand) :
    Option Cand → Except (Refusal Fact Cand) Cand
  | some c => if usable S holds c then .ok c else select S holds order
  | none => select S holds order

/-! ### `Slot.lean` -/

theorem usable_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    usable S holds c = true ↔ S.judge c = true ∧ ∀ f ∈ S.supports c, holds f = true := by
  simp [usable, List.isEmpty_iff, dead_eq_nil_iff]

/-- A dead support is a zero of the monomial. -/
theorem usable_dead (S : Slot Fact Cand) (holds : Fact → Bool) {c : Cand} {f : Fact}
    (hf : f ∈ S.supports c) (hd : holds f = false) : usable S holds c = false := by
  simpa [usable, List.isEmpty_iff, dead_eq_nil_iff] using fun _ => ⟨f, hf, by simp [hd]⟩

theorem read_usable_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    (∃ ev, read S holds (some c) = .usable c ev) ↔ usable S holds c = true := by
  unfold read
  by_cases hu : usable S holds c = true <;> by_cases hj : S.judge c = true <;> simp [hu, hj]

theorem read_blocked_names (S : Slot Fact Cand) (holds : Fact → Bool) {c c' : Cand} {d : List Fact}
    (h : read S holds (some c) = .blocked c' d) :
    c' = c ∧ d ≠ [] ∧ ∀ f, f ∈ d ↔ f ∈ S.supports c ∧ holds f = false := by
  by_cases hu : usable S holds c = true <;> by_cases hj : S.judge c = true <;> simp [read, hu, hj] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, fun hd => hu ((usable_iff S _ c).2 ⟨hj, (dead_eq_nil_iff S _ c).1 hd⟩),
    fun f => mem_dead_iff S _ c f⟩

theorem slot_repair {V : Type} (S : Slot Fact Cand) (holdsAt : V → Fact → Bool)
    (later : V → V → Prop) (v : V) (c : Cand) :
    ((∃ ev, read S (holdsAt v) (some c) = .usable c ev) ↔
        S.judge c = true ∧ ∀ f ∈ S.supports c, holdsAt v f = true) ∧
    (∀ c' d, read S (holdsAt v) (some c) = .blocked c' d →
        d ≠ [] ∧ ∀ f, f ∈ d ↔ f ∈ S.supports c ∧ holdsAt v f = false) ∧
    (∀ f, f ∈ S.supports c → holdsAt v f = false → Permanent holdsAt later f →
        ∀ v', later v v' → S.judge c = true →
          ∃ d, read S (holdsAt v') (some c) = .blocked c d ∧ f ∈ d) ∧
    (∀ c', usable S (holdsAt v) c' = true →
        read S (holdsAt v) (some c') = .usable c' (S.evidence (holdsAt v) c')) := by
  refine ⟨(read_usable_iff S _ c).trans (usable_iff S _ c), fun _ _ h => (read_blocked_names S _ h).2,
    fun f hf hdead hperm v' hv' hj => ?_, fun c' hu => by simp [read, hu]⟩
  have hf' := hperm v v' hv' hdead
  exact ⟨_, by simp [read, usable_dead S _ hf hf', hj], (mem_dead_iff S _ c f).2 ⟨hf, hf'⟩⟩

#tooth slot_repair by mutation read := fun _ _ _ => .empty

theorem select_ok {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {c : Cand}
    (h : select S holds order = .ok c) :
    c ∈ order ∧ usable S holds c = true ∧ ∃ rest, alternatives S holds order = c :: rest := by
  unfold select at h
  split at h <;> cases h
  rename_i rest ha
  have := List.mem_filter.1 (ha ▸ List.mem_cons_self : c ∈ alternatives S holds order)
  exact ⟨this.1, this.2, rest, ha⟩

theorem select_error {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {w : Refusal Fact Cand}
    (h : select S holds order = .error w) :
    (∀ c ∈ order, usable S holds c = false) ∧ w = order.map fun c => (c, S.dead holds c) := by
  unfold select at h
  split at h <;> cases h
  rename_i ha
  exact ⟨fun c hc => by simpa [hc] using List.filter_eq_nil_iff.1 ha c hc, rfl⟩

section
variable {Ix : Type} {Sg : Protocol.Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

theorem resolve_ok {Sl : Slot Fact Cand} {holds : Fact → Bool} {i : Ix}
    {body : Cand → Protocol.Prot Sg Hole A i} {order : List Cand} {f : Protocol.Prot Sg Hole A i}
    (h : resolve Sl holds body order = .ok f) :
    ∃ c rest, alternatives Sl holds order = c :: rest ∧ c ∈ order ∧ usable Sl holds c = true ∧
      f = body c := by
  cases hs : select Sl holds order <;> simp [resolve, hs, Except.map] at h
  obtain ⟨hc, hu, rest, ha⟩ := select_ok hs
  exact ⟨_, rest, ha, hc, hu, h.symm⟩

theorem resolve_error {Sl : Slot Fact Cand} {holds : Fact → Bool} {i : Ix}
    {body : Cand → Protocol.Prot Sg Hole A i} {order : List Cand} {w : Refusal Fact Cand}
    (h : resolve Sl holds body order = .error w) :
    (∀ c ∈ order, usable Sl holds c = false) ∧ w = order.map fun c => (c, Sl.dead holds c) := by
  cases hs : select Sl holds order <;> simp [resolve, hs, Except.map] at h
  exact h ▸ select_error hs

theorem resolve_eq_select (S : Slot Fact Cand) (holds : Fact → Bool) {i : Ix}
    (body : Cand → Protocol.Prot Sg Hole A i) (order : List Cand) :
    resolve S holds body order = (select S holds order).map body := rfl

end

/-! ### The bridges: the redefinition is the original, observation for observation -/

theorem usable_eq (S : Slot Fact Cand) (holds : Fact → Bool) : usable S holds = S.usable holds :=
  funext fun c => Bool.eq_iff_iff.2 ((usable_iff S holds c).trans (Obend.Slot.usable_iff S holds c).symm)

theorem alternatives_eq (S : Slot Fact Cand) (holds : Fact → Bool) :
    alternatives S holds = S.alternatives holds := by
  funext cands; simp [alternatives, Slot.alternatives, usable_eq]

theorem read_eq (S : Slot Fact Cand) (holds : Fact → Bool) : read S holds = S.read holds := by
  funext o
  cases o with
  | none => rfl
  | some c =>
    simp only [read, Slot.read, usable_eq, Slot.usable]
    cases hj : S.judge c <;> cases hd : S.dead holds c <;> simp

theorem select_eq (S : Slot Fact Cand) (holds : Fact → Bool) : select S holds = S.select holds := by
  funext order; unfold select Slot.select; rw [alternatives_eq]; cases S.alternatives holds order <;> rfl

theorem advance_eq (S : Slot Fact Cand) (holds : Fact → Bool) : advance S holds = S.advance holds := by
  funext order o; cases o <;> simp [advance, Slot.advance, usable_eq, select_eq]

end

/-! ### `Slot/World.lean` -/

namespace World
variable {V Fact Cand : Type} [World V Fact]

theorem usable_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    usable S (holdsAt v) c = usable S (holdsAt v') c := by
  unfold usable; rw [dead_congr S c agree]

theorem read_congr (S : Slot Fact Cand) {v v' : V} (c : Cand)
    (agree : ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    read S (holdsAt v) (some c) = read S (holdsAt v') (some c) := by
  have ev : S.evidence (holdsAt v) c = S.evidence (holdsAt v') c :=
    List.map_congr_left fun f hf => by rw [holds_agree S c agree f hf]
  simp only [read, usable_congr S c agree, dead_congr S c agree, ev]

theorem alternatives_congr (S : Slot Fact Cand) {v v' : V} (order : List Cand)
    (agree : ∀ c ∈ order, ∀ f ∈ S.supports c, pin (Fact := Fact) v (cell f) = pin (Fact := Fact) v' (cell f)) :
    alternatives S (holdsAt v) order = alternatives S (holdsAt v') order :=
  List.filter_congr fun c hc => usable_congr S c (agree c hc)

theorem blocked_forever (S : Slot Fact Cand) {v v' : V} (c : Cand) (f : Fact) (hf : f ∈ S.supports c)
    (hr : pin (Fact := Fact) v (cell f) = none) (h : Later (Fact := Fact) v v') (hj : S.judge c = true) :
    ∃ d, read S (holdsAt v') (some c) = .blocked c d ∧ f ∈ d := by
  have hdead := dead_behind_forever f hr h
  exact ⟨_, by simp [read, usable_dead S _ hf hdead, hj], (mem_dead_iff S _ c f).2 ⟨hf, hdead⟩⟩

end World

/-! ### `Slot/Integrity.lean` -/

section
variable {V Fact Cand : Type} [World V Fact]

def slotFiller : Filler V Fact Cand := ⟨fun S v order => select S (holdsAt v) order⟩
def slotAdvance : Advance V Fact Cand := ⟨fun S v order stored => advance S (holdsAt v) order stored⟩

/-- B4, with the redefined `alternatives`. -/
def PIntegrity.contextual (F : Filler V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (v : V) (order : List Cand),
    (∀ c, F.fill S v order = .ok c →
      c ∈ order ∧ S.judge c = true ∧ (∀ f ∈ S.supports c, holdsAt v f = true) ∧
      ∃ rest, alternatives S (holdsAt v) order = c :: rest) ∧
    (∀ w, F.fill S v order = .error w → ∀ c ∈ order,
      ∃ d, (c, d) ∈ w ∧ (∀ f ∈ d, f ∈ S.supports c ∧ holdsAt v f = false) ∧ (d = [] → S.judge c = false))

/-- REPAIR, with the redefined `usable`. -/
def PIntegrity.repair (F : Filler V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (order : List Cand),
    (∀ (v v' : V) (c : Cand) (f : Fact), f ∈ S.supports c → pin (Fact := Fact) v (cell f) = none →
      Later (Fact := Fact) v v' → F.fill S v' order ≠ .ok c) ∧
    (∀ (v : V) (c : Cand), c ∈ order → usable S (holdsAt v) c = true → ∃ c', F.fill S v order = .ok c')

/-- B4′, with the redefined `usable` and `alternatives`. -/
def PIntegrity.transition (A : Advance V Fact Cand) : Prop :=
  ∀ (S : Slot Fact Cand) (v : V) (order : List Cand) (stored : Option Cand),
    (∀ c, stored = some c → usable S (holdsAt v) c = true → A.advance S v order stored = .ok c) ∧
    (∀ c, A.advance S v order stored = .ok c → usable S (holdsAt v) c = true ∧
      (stored = some c ∨ ∃ rest, alternatives S (holdsAt v) order = c :: rest)) ∧
    (∀ w, A.advance S v order stored = .error w →
      (∀ c, stored = some c → usable S (holdsAt v) c = false) ∧
      (∀ c ∈ order, usable S (holdsAt v) c = false) ∧
      ∀ c ∈ order, ∃ d, (c, d) ∈ w ∧ (∀ f ∈ d, f ∈ S.supports c ∧ holdsAt v f = false) ∧
        (d = [] → S.judge c = false))

def PIntegrity (F : Filler V Fact Cand) (A : Advance V Fact Cand) : Prop :=
  PIntegrity.contextual F ∧ PIntegrity.transition A

theorem select_names {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand}
    {w : Refusal Fact Cand} (h : select S holds order = .error w) :
    ∀ c ∈ order, ∃ d, (c, d) ∈ w ∧ (∀ f ∈ d, f ∈ S.supports c ∧ holds f = false) ∧
      (d = [] → S.judge c = false) := by
  obtain ⟨hnone, rfl⟩ := select_error h
  refine fun c hc => ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, fun f hf => (mem_dead_iff S _ c f).1 hf,
    fun hd => ?_⟩
  cases hj : S.judge c
  · rfl
  · simpa [hnone c hc] using (usable_iff S _ c).2 ⟨hj, (dead_eq_nil_iff S _ c).1 hd⟩

theorem repair_of_contextual {F : Filler V Fact Cand} (h : PIntegrity.contextual F) :
    PIntegrity.repair F := by
  refine fun S order => ⟨fun v v' c f hf hr hl hfill => ?_, fun v c hc hu => ?_⟩
  · have live := ((h S v' order).1 c hfill).2.2.1 f hf
    rw [dead_behind_forever f hr hl] at live
    cases live
  · cases answer : F.fill S v order with
    | ok c' => exact ⟨c', rfl⟩
    | error w =>
      obtain ⟨d, -, sound, rejected⟩ := (h S v order).2 w answer c hc
      have ⟨hj, hall⟩ := (usable_iff S _ c).1 hu
      have empty : d = [] := List.eq_nil_iff_forall_not_mem.2 fun f hf => by
        simpa [(sound f hf).2] using hall f (sound f hf).1
      simp [rejected empty] at hj

theorem slotFiller_integrity :
    PIntegrity (slotFiller : Filler V Fact Cand) (slotAdvance : Advance V Fact Cand) := by
  refine ⟨fun S v order => ⟨fun c h => ?_, fun w h => select_names h⟩,
    fun S v order stored => ⟨fun c hs hu => by subst hs; simp [slotAdvance, advance, hu],
      fun c h => ?_, fun w h => ?_⟩⟩
  · obtain ⟨hmem, hu, ha⟩ := select_ok h
    exact ⟨hmem, ((usable_iff S _ c).1 hu).1, ((usable_iff S _ c).1 hu).2, ha⟩
  · cases stored with
    | none => exact (select_ok h).2.1 |> fun hu => ⟨hu, .inr (select_ok h).2.2⟩
    | some c₀ =>
      by_cases hu : usable S (holdsAt v) c₀ = true <;> simp only [slotAdvance, advance, hu] at h
      · cases h; exact ⟨hu, .inl rfl⟩
      · exact ⟨(select_ok h).2.1, .inr (select_ok h).2.2⟩
  · have hsel : select S (holdsAt v) order = .error w ∧ ∀ c, stored = some c → usable S (holdsAt v) c = false := by
      cases stored with
      | none => exact ⟨h, fun _ h => by cases h⟩
      | some c₀ =>
        by_cases hu : usable S (holdsAt v) c₀ = true <;> simp [slotAdvance, advance, hu] at h
        exact ⟨h, fun c hc => by cases hc; simpa using hu⟩
    exact ⟨hsel.2, (select_error hsel.1).1, select_names hsel.1⟩

#tooth slotFiller_integrity by mutation advance := fun _ _ _ _ => .error []

theorem slotFiller_repair : PIntegrity.repair (slotFiller : Filler V Fact Cand) :=
  repair_of_contextual slotFiller_integrity.1

theorem transition_retired {A : Advance V Fact Cand} (hA : PIntegrity.transition A)
    (S : Slot Fact Cand) (order : List Cand) (stored : Option Cand) {v v' : V} {c : Cand} {f : Fact}
    (hf : f ∈ S.supports c) (hr : pin (Fact := Fact) v (cell f) = none) (hl : Later (Fact := Fact) v v') :
    A.advance S v' order stored ≠ .ok c := fun h => by
  simpa [usable_dead S _ hf (dead_behind_forever f hr hl)] using ((hA S v' order stored).2.1 c h).1

theorem select_prefix {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand} {c : Cand}
    (h : select S holds order = .ok c) :
    ∃ pre post, order = pre ++ c :: post ∧ usable S holds c = true ∧ ∀ c' ∈ pre, usable S holds c' = false := by
  induction order with
  | nil => simp [select, alternatives] at h
  | cons x xs ih =>
    by_cases hx : usable S holds x = true
    · simp [select, alternatives, hx] at h
      subst h; exact ⟨[], xs, rfl, hx, by simp⟩
    · have h' : select S holds xs = .ok c := by
        simp only [select, alternatives, List.filter_cons, hx] at h ⊢
        split at h <;> simp_all
      obtain ⟨pre, post, rfl, hc, hpre⟩ := ih h'
      exact ⟨x :: pre, post, rfl, hc, fun c' hc' => by
        rcases List.mem_cons.1 hc' with rfl | hc'
        · simpa using hx
        · exact hpre c' hc'⟩

theorem select_reuse {S : Slot Fact Cand} {holds : Fact → Bool} {pre post : List Cand} {c : Cand}
    (hc : usable S holds c = true) (hpre : ∀ c' ∈ pre, usable S holds c' = false) :
    select S holds (pre ++ c :: post) = .ok c := by
  unfold select alternatives
  rw [List.filter_append, List.filter_eq_nil_iff.2 fun c' h => by simp [hpre c' h],
    List.filter_cons_of_pos hc]
  rfl

#tooth select_reuse by mutation alternatives := fun _ _ _ => []

theorem slotFiller_typed {Tm R : Type} [Calculus Tm] [Obend.Core.Graded R] [Decides R Tm]
    (budget : Budget R) (Ψ : Calculus.Ctx Tm) (A : Calculus.Ty Tm)
    (supports : Tm → List Fact) (v : V) (order : List Tm) (t : Tm)
    (h : (slotFiller : Filler V Fact Tm).fill
      (Calculus.slotOf budget Ψ A supports) v order = .ok t) : Calculus.Typed Ψ t A := by
  obtain ⟨_, hu, _⟩ := select_ok h
  exact (Calculus.slotOf_usable budget Ψ A supports (holdsAt v) t (usable_eq _ _ ▸ hu)).1

theorem slotFiller_uncovered {Tm R : Type} [Calculus Tm] [Obend.Core.Graded R] [Decides R Tm]
    (budget : Budget R) (Ψ : Calculus.Ctx Tm) (A : Calculus.Ty Tm)
    (supports : Tm → List Fact) (v : V) (order : List Tm) (t : Tm)
    (w : Refusal Fact Tm)
    (h : (slotFiller : Filler V Fact Tm).fill
      (Calculus.slotOf budget Ψ A supports) v order = .error w)
    (member : t ∈ order) (live : ∀ f ∈ supports t, holdsAt v f = true) :
    Calculus.admit budget Ψ A t = .error (.uncovered budget.grade) := by
  have refused := (select_error h).1 t member
  have checkFalse : Decides.check budget.grade Ψ t A = false := by
    cases hc : Decides.check budget.grade Ψ t A
    · rfl
    · simpa [refused] using (usable_iff (Calculus.slotOf budget Ψ A supports) _ t).2 ⟨hc, live⟩
  simp [Calculus.admit, checkFalse]

/-! #### The floor, on the toy World -/

def blindRefusal : Filler V Fact Cand :=
  ⟨fun S v order => match alternatives S (holdsAt v) order with
    | c :: _ => .ok c
    | [] => .error []⟩

def churn : Advance V Fact Cand := ⟨fun S v order _ => select S (holdsAt v) order⟩

def sticky : Advance V Fact Cand :=
  ⟨fun S v order stored => match stored with
    | some c => .ok c
    | none => select S (holdsAt v) order⟩

end

theorem toy_repair :
    slotFiller.fill toySlot 0 toyOrder = .ok .alice ∧
    read toySlot (holdsAt 1) (some .alice) = .blocked .alice [.alice] ∧
    slotFiller.fill toySlot 1 toyOrder = .ok .bob :=
  ⟨rfl, rfl, rfl⟩

#tooth toy_repair by mutation toyOrder := []

theorem toy_advance :
    slotAdvance.advance toySlot 0 toyOrder (some .alice) = .ok .alice ∧
    slotAdvance.advance toySlot 1 toyOrder (some .alice) = .ok .bob ∧
    slotAdvance.advance toySlot 0 toyOrder (some .bob) = .ok .bob :=
  ⟨rfl, rfl, rfl⟩

#tooth toy_advance by mutation toyOrder := []

theorem not_integrity_credulousHoles :
    ¬ PIntegrity.contextual (credulousHoles : Filler Nat Member Member) := by
  intro h
  have := ((h toySlot 1 toyOrder).1 .alice rfl).2.2.1 .alice (by simp [toySlot])
  rw [toy_alice_dead] at this
  cases this

#tooth not_integrity_credulousHoles by mutation PIntegrity.contextual := fun {_ _ _} [_] _ => True

theorem not_integrity_firstCandidate :
    ¬ PIntegrity.contextual (firstCandidate : Filler Nat Member Member) := by
  intro h
  have := ((h toySlot 1 toyOrder).1 .alice rfl).2.2.1 .alice (by simp [toySlot])
  rw [toy_alice_dead] at this
  cases this

#tooth not_integrity_firstCandidate by mutation PIntegrity.contextual := fun {_ _ _} [_] _ => True

theorem not_integrity_blindRefusal :
    ¬ PIntegrity.contextual (blindRefusal : Filler Nat Member Member) := by
  intro h
  obtain ⟨d, hd, -⟩ := (h toySlot 1 [.alice]).2 [] rfl .alice (List.mem_singleton.2 rfl)
  cases hd

#tooth not_integrity_blindRefusal by mutation blindRefusal := slotFiller

theorem not_transition_churn : ¬ PIntegrity.transition (churn : Advance Nat Member Member) := by
  intro h
  cases (h toySlot 0 toyOrder (some .bob)).1 .bob rfl rfl

#tooth not_transition_churn by mutation churn := slotAdvance

theorem not_transition_sticky : ¬ PIntegrity.transition (sticky : Advance Nat Member Member) := by
  intro h
  cases ((h toySlot 1 toyOrder (some .alice)).2.1 .alice rfl).1

#tooth not_transition_sticky by mutation sticky := slotAdvance

theorem reuse_needs_prefix :
    select reuseSlot (fun f => f) [false, true] = .ok true ∧
    usable reuseSlot (fun _ => true) true = true ∧
    select reuseSlot (fun _ => true) [false, true] = .ok false :=
  ⟨rfl, rfl, rfl⟩

theorem toy_integrity : PIntegrity (slotFiller : Filler Nat Member Member) slotAdvance :=
  slotFiller_integrity

end Obend.Slot.Control
end
