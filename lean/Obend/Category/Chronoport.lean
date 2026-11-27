module
public import Obend.Category.FiberGrowth

/-!
# Quantifying over a Resequence timeline before and after a chronoport

This models the successful branch of `resequence-rs/src/timeline.rs::chronoport`
at commit `7dc2c3a049a9`. Entity types index *stored* entries, including
inactive ones. Option extends that carrier with one fresh ID. Ticks use Nat:
the model assumes successful capacity/window checks, fresh allocation and
representable `target + 1`. No timewave has advanced after the operation.
Histories below are the Rust event vectors in reverse order. With equal
timestamps an existing event wins over a newly inserted event. The theorems
concern this model; the Rust integration tests exercise its concrete boundary.
-/
public section
namespace Obend.Category.Chronoport
open Obend.Category.Projection
set_option autoImplicit false

universe u v w
variable {E : Type u} {B : Type v} {S : Type w}

inductive Lifecycle where
  | unborn | prebirth | born | dead | chronoporting
  deriving DecidableEq

structure Event (S : Type w) where
  tick : Nat
  phase : Lifecycle
  payload : S
  deriving DecidableEq

/-- First visible event when scanning from greatest timestamp to least. -/
def readAt (q : Nat) : List (Event S) → Option (Event S)
  | [] => none
  | h :: t => if h.tick ≤ q then some h else readAt q t

/-- Rust inserts before all ties in ascending order, hence after ties here. -/
def insertEvent (newEvent : Event S) : List (Event S) → List (Event S)
  | [] => [newEvent]
  | h :: t => if h.tick < newEvent.tick then newEvent :: h :: t
                else h :: insertEvent newEvent t

/-- Exact view change: an inserted event must be visible and strictly newer
than the previous answer. A visible tie preserves the previous answer. -/
def overlay (q : Nat) (m : Event S) (old : Option (Event S)) : Option (Event S) :=
  if m.tick ≤ q then
    match old with
    | none => some m
    | some h => if m.tick ≤ h.tick then some h else some m
  else old

theorem readAt_insert (q : Nat) (m : Event S) (events : List (Event S)) :
    readAt q (insertEvent m events) = overlay q m (readAt q events) := by
  induction events with
  | nil => simp [insertEvent, readAt, overlay]
  | cons h t ih =>
    by_cases newer : h.tick < m.tick
    · by_cases visible : m.tick ≤ q
      · have hv : h.tick ≤ q := by omega
        simp [insertEvent, readAt, overlay, newer, visible, hv, Nat.not_le_of_lt newer]
      · simp [insertEvent, readAt, overlay, newer, visible]
    · by_cases hv : h.tick ≤ q
      · have mv : m.tick ≤ q := by omega
        have tie : m.tick ≤ h.tick := by omega
        simp [insertEvent, readAt, overlay, newer, hv, mv, tie]
      · simpa [insertEvent, readAt, newer, hv] using ih

private theorem mem_insertEvent (x m : Event S) (events : List (Event S)) :
    x ∈ insertEvent m events ↔ x = m ∨ x ∈ events := by
  induction events with
  | nil => simp [insertEvent]
  | cons h t ih =>
    by_cases newer : h.tick < m.tick
    · simp [insertEvent, newer]
    · simp [insertEvent, newer, ih, or_left_comm]

/-- Each Rust entity is born or scheduled with a first event and never has
its complete log cleared. This makes latest-event access total on stored IDs. -/
structure History (S : Type w) where
  latest : Event S
  older : List (Event S)

def History.events (h : History S) := h.latest :: h.older

def History.add (h : History S) (m : Event S) : History S :=
  if h.latest.tick < m.tick then ⟨m, h.events⟩ else ⟨h.latest, insertEvent m h.older⟩

theorem History.events_add (h : History S) (m : Event S) :
    (h.add m).events = insertEvent m h.events := by
  simp only [History.add, History.events, insertEvent]
  split <;> rfl

structure Timeline (E : Type u) (B : Type v) (S : Type w) where
  name : E → B
  history : E → History S

variable (t : Timeline E B S) (src : E) (now target : Nat)

def departure : Event S := ⟨now, .chronoporting, (t.history src).latest.payload⟩
def arrival : Event S := ⟨target + 1, .prebirth, (t.history src).latest.payload⟩

variable [DecidableEq E]

/-- One successful call. The fresh entry starts with one scheduled event.
The source retains its identity and gains a departure event. -/
def chronoport : Timeline (Option E) B S where
  name := FiberGrowth.insert t.name (t.name src)
  history
    | none => ⟨arrival t src target, []⟩
    | some e => if e = src then (t.history e).add (departure t src now) else t.history e

def Timeline.observe (world : Timeline E B S) (q : Nat) (id : E) : Option (Event S) :=
  readAt q (world.history id).events

theorem observe_retained (q : Nat) (e : E) :
    (chronoport t src now target).observe q (some e) =
      if e = src then overlay q (departure t src now) (t.observe q e) else t.observe q e := by
  by_cases eq : e = src
  · simp [chronoport, Timeline.observe, eq, History.events_add, readAt_insert]
  · simp [chronoport, Timeline.observe, eq]

theorem observe_arrival (q : Nat) :
    (chronoport t src now target).observe q none =
      if target + 1 ≤ q then some (arrival t src target) else none := by
  simp [chronoport, Timeline.observe, History.events, readAt, arrival]

/-- Any property witnessed by an actual event of an old ID remains witnessed
in its log, even if that event ceases to be the result of a time-slice read. -/
theorem retained_event (e : E) (x : Event S) (inLog : x ∈ (t.history e).events) :
    x ∈ ((chronoport t src now target).history (some e)).events := by
  by_cases eq : e = src
  · simpa [chronoport, eq, History.events_add, mem_insertEvent] using
      (Or.inr inLog : x = departure t src now ∨ x ∈ (t.history e).events)
  · simpa [chronoport, eq] using inLog

/-! Exact post-port truth of *arbitrary* predicates of a time-indexed read.
The old fiber is queried against its retained observations, corrected at the
departing source. The new disjunct / conjunct accounts for the scheduled copy. -/
theorem exists_observe_iff (q : Nat) (Q : Option (Event S) → Prop) (b : B) :
    existsAlong (chronoport t src now target).name
      (fun id => Q ((chronoport t src now target).observe q id)) b ↔
      (∃ e, t.name e = b ∧ Q (if e = src then overlay q (departure t src now) (t.observe q e)
                              else t.observe q e)) ∨
      (t.name src = b ∧ Q (if target + 1 ≤ q then some (arrival t src target) else none)) := by
  rw [show (chronoport t src now target).name = FiberGrowth.insert t.name (t.name src) from rfl,
      FiberGrowth.exists_insert_iff, existsAlong_iff]
  simp only [observe_retained, observe_arrival]

theorem forall_observe_iff (q : Nat) (Q : Option (Event S) → Prop) (b : B) :
    forallAlong (chronoport t src now target).name
      (fun id => Q ((chronoport t src now target).observe q id)) b ↔
      (∀ e, t.name e = b → Q (if e = src then overlay q (departure t src now) (t.observe q e)
                              else t.observe q e)) ∧
      (t.name src = b → Q (if target + 1 ≤ q then some (arrival t src target) else none)) := by
  rw [show (chronoport t src now target).name = FiberGrowth.insert t.name (t.name src) from rfl,
      FiberGrowth.forall_insert_iff, forallAlong_iff]
  simp only [observe_retained, observe_arrival]

private theorem latest_retained (e : E) :
    ((chronoport t src now target).history (some e)).latest.payload = (t.history e).latest.payload := by
  by_cases eq : e = src
  · subst e
    by_cases newer : (t.history src).latest.tick < now <;>
      simp [chronoport, History.add, departure, newer]
  · simp [chronoport, eq]

/-- Every predicate of the latest payload preserves *both* quantifier answers
at *every* name, whether or not the logged latest tick follows departure.
This uses the fresh payload copy and the payload written to the departure
marker. Merely knowing that one name fiber grew would be insufficient. -/
theorem latest_payload_invariant [DecidableEq B] (Q : S → Prop) (b : B) :
    let w := chronoport t src now target
    (existsAlong w.name (fun e => Q (w.history e).latest.payload) b ↔
       existsAlong t.name (fun e => Q (t.history e).latest.payload) b) ∧
    (forallAlong w.name (fun e => Q (w.history e).latest.payload) b ↔
       forallAlong t.name (fun e => Q (t.history e).latest.payload) b) := by
  dsimp only
  have agree (e : E) (_ : t.name e = b) :
      Q (((chronoport t src now target).history (some e)).latest.payload) ↔
        Q ((t.history e).latest.payload) := by rw [latest_retained]
  by_cases here : t.name src = b
  · subst b
    exact FiberGrowth.unchanged_of_copy t.name src _ _ agree Iff.rfl
  · exact FiberGrowth.unchanged_away t.name (t.name src) b here _ _ agree

/-- Values read elsewhere in the departing name's fiber. These copies and
their logs are untouched by the successful operation. -/
def seenElsewhere (q : Nat) (v : Option (Event S)) : Prop :=
  ∃ e, e ≠ src ∧ t.name e = t.name src ∧ t.observe q e = v

private theorem replace_image_iff {V : Type w} (U : V → Prop) (a b c : V) :
    (∀ v, (U v ∨ a = v) ↔ (U v ∨ b = v ∨ c = v)) ↔
      (U a ∨ b = a ∨ c = a) ∧ (U b ∨ a = b) ∧ (U c ∨ a = c) := by
  constructor
  · intro h
    exact ⟨(h a).mp (.inr rfl), (h b).mpr (.inr (.inl rfl)), (h c).mpr (.inr (.inr rfl))⟩
  · rintro ⟨ha, hb, hc⟩ v
    constructor
    · rintro (same | rfl)
      · exact .inl same
      · exact ha
    · rintro (same | rfl | rfl)
      · exact .inl same
      · exact hb
      · exact hc

/-- Exact test for preserving both quantifiers for *every* predicate on a
time-slice read. The disappearing source value must still occur somewhere;
each value offered by the new source or copy must already have occurred.
Multiplicity, witness identity and the rest of the world are irrelevant. -/
theorem all_reads_iff (q : Nat) :
    let w := chronoport t src now target
    let n := t.name src
    let a := t.observe q src
    let b := overlay q (departure t src now) a
    let c := if target + 1 ≤ q then some (arrival t src target) else none
    let U := seenElsewhere t src q
    ((∀ Q : Option (Event S) → Prop, existsAlong t.name (fun e => Q (t.observe q e)) n ↔
      existsAlong w.name (fun e => Q (w.observe q e)) n) ∧
     (∀ Q : Option (Event S) → Prop, forallAlong t.name (fun e => Q (t.observe q e)) n ↔
      forallAlong w.name (fun e => Q (w.observe q e)) n)) ↔
    (U a ∨ b = a ∨ c = a) ∧ (U b ∨ a = b) ∧ (U c ∨ a = c) := by
  dsimp only
  let w := chronoport t src now target
  let n := t.name src
  let a := t.observe q src
  let b := overlay q (departure t src now) a
  let c := if target + 1 ≤ q then some (arrival t src target) else none
  let U := seenElsewhere t src q
  have oldImage (v) : FiberGrowth.observes t.name (t.observe q) n v ↔ U v ∨ a = v := by
    change (∃ e, t.name e = n ∧ t.observe q e = v) ↔ _
    constructor
    · rintro ⟨e, name, hv⟩
      by_cases hs : e = src
      · subst e; exact .inr hv
      · exact .inl ⟨e, hs, name, hv⟩
    · rintro (⟨e, _, name, hv⟩ | hv)
      · exact ⟨e, name, hv⟩
      · exact ⟨src, rfl, hv⟩
  have newImage (v) : FiberGrowth.observes w.name (w.observe q) n v ↔ U v ∨ b = v ∨ c = v := by
    change existsAlong (chronoport t src now target).name
      (fun id => (chronoport t src now target).observe q id = v) n ↔ _
    rw [exists_observe_iff t src now target q (fun x => x = v) n]
    constructor
    · rintro (⟨e, name, hv⟩ | ⟨_, hv⟩)
      · by_cases hs : e = src
        · subst e; exact .inr (.inl (by simpa [b, a] using hv))
        · exact .inl ⟨e, hs, name, by simpa [hs] using hv⟩
      · exact .inr (.inr hv)
    · rintro (⟨e, hs, name, hv⟩ | hv | hv)
      · exact .inl ⟨e, name, by simpa [hs] using hv⟩
      · exact .inl ⟨src, rfl, by simpa [b, a] using hv⟩
      · exact .inr ⟨rfl, hv⟩
  rw [FiberGrowth.exists_observations_iff, FiberGrowth.forall_observations_iff, and_self]
  apply Iff.trans ?_ (replace_image_iff U a b c)
  constructor
  · intro h v
    exact (oldImage v).symm.trans ((h v).trans (newImage v))
  · intro h v
    exact (oldImage v).trans ((h v).trans (newImage v).symm)

/-- A Born witness can disappear at departure, even though the original ID
survives. The fresh entry is scheduled Prebirth and the source reads its marker. -/
theorem born_witness_lost :
    let t : Timeline Unit Unit Nat := ⟨fun _ => (), fun _ => ⟨⟨0, .born, 7⟩, []⟩⟩
    let Q := fun o : Option (Event Nat) => (o.map Event.phase) = some .born
    let w := chronoport t () 10 5
    existsAlong t.name (fun e => Q (t.observe 10 e)) () ∧
      ¬ existsAlong w.name (fun e => Q (w.observe 10 e)) () := by
  dsimp only
  constructor
  · exact (existsAlong_iff ..).mpr ⟨(), rfl, rfl⟩
  · intro there
    obtain ⟨id, _, h⟩ := (existsAlong_iff ..).mp there
    cases id with
    | none => contradiction
    | some id => cases id; contradiction

end Obend.Category.Chronoport
end
