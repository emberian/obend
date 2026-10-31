module
/-
# Obend.Kind.Proofs — what the kind cell guarantees

* `kind_law_inherited`: whatever an instance's effective law admits, the law of its kind, and of
  every kind on its kind's C4 precedence list, admits; `instance_law_admitted`: so does the
  instance's own law. The kind's law is an ancestor of each instance's law.
* `create_carries`: `create --from K` births an instance carrying `K`'s identity at the registry
  (current there) and `K`'s initial state.
* `kind_stale_iff_blocked`: an instance's kind pin is stale exactly when its slot's read is blocked
  naming it (`Obend.Intention.stale_iff_blocked`, the third instance); `effective_refuses_stale`: a
  stale kind is refused by name before anything is judged; `renew_kind`: renewing re-resolves the
  kind (`Obend.Intention.renew`), and the renewed pin is current and its slot reads usable.
* `dispatch_by_kind`: dispatch reads the instance's kind and nothing else: instances of one kind
  dispatch alike whatever their states, laws or names; `dispatch_sound`: the implementation chosen
  is the first kind on the kind's precedence list that implements the generic.
* `nominal_tooth`: two kinds with the same layout and initial state, two instances in the same state,
  one generic implemented for each kind: the two calls reach the two implementations.
-/
public import Obend.Kind
import all Obend.Kind
public import Obend.Law.Proofs.Inherit
public import Obend.Spec.Proofs.C4
public import Obend.Tactic.Tooth
namespace Obend.Kind

set_option autoImplicit false

open Obend.Core.Term (Term)
open Obend.Core.Data (Data)
open Obend.Law (Admits)

/-! ## The kind reference is an intention -/

/-- **A stale kind is a blocked read** (`Obend.Intention.stale_iff_blocked` at kinds). -/
public theorem kind_stale_iff_blocked (ks : Kinds) (p : KindPin) :
    kindRefs.current ks p = false ↔
      (kindRefs.slot p.name).read (holds ks) (some p) = .blocked p ([p].filter fun f => !holds ks f) :=
  kindRefs.stale_iff_blocked rfl ks

theorem current_kind (ks : Kinds) (p : KindPin) : kindRefs.current ks p = holds ks p := by
  simp [Obend.Intention.current, kindRefs]

/-- **`create --from K` births under `K`.** -/
public theorem create_carries {ks : Kinds} {k name : String} {law : Term} {i : Instance}
    (h : create ks k name law = .ok i) :
    ∃ c, ks.find k = some c ∧ i.kind = ⟨k, c.version⟩ ∧ i.state = c.init ∧ i.name = name ∧ i.law = law ∧
      kindRefs.resolve ks k = .ok i.kind ∧ kindRefs.current ks i.kind = true := by
  unfold create at h
  split at h
  · rename_i c hc
    cases h
    refine ⟨c, hc, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show resolve ks k = _; simp [resolve, hc]
    · rw [current_kind]; simp [holds, hc]
  · cases h

/-- **A revised kind is refused by name**: an instance whose kind pin is not current has no
effective law; the refusal names the pin. -/
public theorem effective_refuses_stale {ks : Kinds} {i : Instance} (h : kindRefs.current ks i.kind = false) :
    effectiveOf ks i = .error (.stale i.kind) := by
  simp [effectiveOf, h]

/-- **Renewing repairs**: an instance's renewed kind is its kind's current version at the registry,
current, its slot's read usable; nothing else of the instance changes. -/
public theorem renew_kind {ks : Kinds} {i i' : Instance} (h : renewKind ks i = .ok i') :
    i'.kind.name = i.kind.name ∧ kindRefs.current ks i'.kind = true ∧
      (kindRefs.slot i.kind.name).read (holds ks) (some i'.kind) =
        .usable i'.kind ((kindRefs.slot i.kind.name).evidence (holds ks) i'.kind) ∧
      i'.name = i.name ∧ i'.law = i.law ∧ i'.state = i.state := by
  unfold renewKind at h
  split at h
  · rename_i p hp
    cases h
    obtain ⟨hr, _, hc⟩ := kindRefs.renew_fill hp
    exact ⟨hr, hc, kindRefs.renew_repairs hp, rfl, rfl, rfl⟩
  · cases h

/-! ## Kind precedence -/

theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ q ∈ l.zip l', f q.1 = .ok q.2
  | [], l', h => by simp
  | a :: l, l', h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i bs hbs
        cases h
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hb
        · exact mapM_ok hbs q hq

theorem mapM_each {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ a ∈ l, ∃ b, f a = .ok b
  | [], _, _ => by simp
  | a :: l, l', h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i bs hbs
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨b, hb⟩
        · exact mapM_each hbs x hx

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hx; cases h; simp at hx; subst hx; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A kind's precedence list starts at the kind, which the registry holds. -/
theorem kindPrecedence_head {ks : Kinds} {n : Nat} {k : String} {l : List String}
    (h : kindPrecedence ks n k = .ok l) : (ks.find k).isSome ∧ ∃ rest, l = k :: rest := by
  cases n with
  | zero => simp [kindPrecedence] at h
  | succ n =>
    simp only [kindPrecedence] at h
    split at h
    · cases h
    · rename_i c hc
      split at h
      · cases h
      · split at h
        · rename_i l' s hl
          cases h
          obtain ⟨rest, hr⟩ := Obend.Spec.C4.linearize_head hl
          exact ⟨by simp [hc], rest, by simpa using hr⟩
        · cases h

/-- Every name on a kind's precedence list is a kind the registry holds. -/
theorem kindPrecedence_found {ks : Kinds} : ∀ {n : Nat} {k : String} {l : List String},
    kindPrecedence ks n k = .ok l → ∀ x ∈ l, (ks.find x).isSome := by
  intro n
  induction n with
  | zero => intro k l h; simp [kindPrecedence] at h
  | succ n ih =>
    intro k l h x hx
    simp only [kindPrecedence] at h
    split at h
    · cases h
    · rename_i c hc
      split at h
      · cases h
      · rename_i lists hlists
        split at h
        · rename_i l' s hl
          cases h
          rcases Obend.Spec.C4.linearize_mem hl x hx with hx | ⟨chain, hch, hxc⟩ | ⟨p, hp, hxp⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp [hc]
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hch; subst hch
            obtain ⟨b, hb⟩ := mapM_each hlists x hxc
            exact (kindPrecedence_head hb).1
          · simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hp
            simp only at hxp
            cases hlk : (c.parents.zip lists).lookup p with
            | none =>
              rw [hlk] at hxp
              simp only [Option.getD_none, List.mem_cons, List.not_mem_nil, or_false] at hxp
              subst hxp
              obtain ⟨b, hb⟩ := mapM_each hlists x hp
              exact (kindPrecedence_head hb).1
            | some L =>
              rw [hlk] at hxp
              have hq := mapM_ok hlists _ (lookup_mem hlk)
              exact ih hq x hxp
        · cases h

theorem lookup_table {ks : Kinds} {i : Instance} {x : String} {c : KindCell} (h : ks.find x = some c) :
    (lawTable ks i).lookup x = some c.law := by
  unfold lawTable
  unfold Kinds.find at h
  generalize ks.cells = cs at h
  induction cs with
  | nil => simp at h
  | cons d ds ih =>
    simp only [List.find?_cons] at h
    by_cases hd : d.name = x
    · simp [hd] at h; subst h; simp [List.lookup, hd]
    · have : (d.name == x) = false := by simp [hd]
      rw [this] at h
      simp only [List.map_cons, List.cons_append, List.lookup]
      have : (x == d.name) = false := by simp [Ne.symm hd]
      rw [this]
      exact ih h

theorem lookup_table_self {ks : Kinds} {i : Instance} (h : (ks.find i.name).isSome = false) :
    (lawTable ks i).lookup i.name = some i.law := by
  unfold lawTable
  unfold Kinds.find at h
  generalize ks.cells = cs at h
  induction cs with
  | nil => simp [List.lookup]
  | cons d ds ih =>
    simp only [List.find?_cons] at h
    by_cases hd : d.name = i.name
    · simp [hd] at h
    · have : (d.name == i.name) = false := by simp [hd]
      rw [this] at h
      simp only [List.map_cons, List.cons_append, List.lookup]
      have : (i.name == d.name) = false := by simp [Ne.symm hd]
      rw [this]
      exact ih h

/-! ## The kind's law is an ancestor of the instance's -/

theorem effectiveOf_ok {ks : Kinds} {i : Instance} {t : Term} (h : effectiveOf ks i = .ok t) :
    kindRefs.current ks i.kind = true ∧ (ks.find i.name).isSome = false ∧
      ∃ lk, kindPrecedence ks ks.depth i.kind.name = .ok lk ∧
        Obend.Law.effectiveVia (instanceGraph i.kind.name lk) (lawTable ks i) i.name [[i.kind.name]] = .ok t := by
  unfold effectiveOf at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · rename_i lk hlk
        split at h
        · rename_i t' ht
          cases h
          exact ⟨by simpa using hc, by simpa using hn, lk, hlk, ht⟩
        · cases h

/-- **The kind's law is an ancestor of each instance's law.** Whatever an instance's effective law
admits, the law of every kind on its kind's precedence list admits, its own kind first. -/
public theorem kind_law_inherited {ks : Kinds} {i : Instance} {t : Term} (h : effectiveOf ks i = .ok t)
    {o n rq : Data} (ha : Admits t o n rq) :
    ∃ lk, kindPrecedence ks ks.depth i.kind.name = .ok lk ∧ lk.head? = some i.kind.name ∧
      ∀ k ∈ lk, ∃ c, ks.find k = some c ∧ Admits c.law o n rq := by
  obtain ⟨_, _, lk, hlk, hev⟩ := effectiveOf_ok h
  have hpar := Obend.Law.effectiveVia_parent hev ha [i.kind.name] (by simp) i.kind.name (by simp)
  obtain ⟨_, rest, hr⟩ := kindPrecedence_head hlk
  refine ⟨lk, hlk, by simp [hr], fun k hk => ?_⟩
  have hf := kindPrecedence_found hlk k hk
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨L, hL, hadm⟩ := hpar k (by simp [instanceGraph, hk])
  rw [lookup_table hc] at hL
  cases hL
  exact ⟨c, hc, hadm⟩

/-- The instance's own law admits what its effective law admits. -/
public theorem instance_law_admitted {ks : Kinds} {i : Instance} {t : Term} (h : effectiveOf ks i = .ok t)
    {o n rq : Data} (ha : Admits t o n rq) : Admits i.law o n rq := by
  obtain ⟨_, hn, lk, _, hev⟩ := effectiveOf_ok h
  obtain ⟨names, hnames, hall⟩ := Obend.Law.effectiveVia_eval hev
  have hhead := (Obend.Law.precedence_ok hnames).1
  obtain ⟨L, hL, hadm⟩ := (hall o n rq).1 ha i.name (List.mem_of_mem_head? hhead)
  rw [lookup_table_self hn] at hL
  cases hL
  exact hadm

/-! ## Dispatch by kind -/

/-- **Dispatch reads the kind and nothing else**: two instances of one kind dispatch every generic
alike, whatever their names, laws and states. -/
public theorem dispatch_by_kind {Body : Type} (ks : Kinds) (impls : List (Impl Body)) (generic : String)
    {i j : Instance} (h : i.kind.name = j.kind.name) :
    dispatch ks impls generic i = dispatch ks impls generic j := by
  simp [dispatch, h]

/-- **Dispatch is the most specific kind's implementation**: the body dispatched is the
implementation for a kind on the instance's kind's precedence list, and no kind before it there
implements the generic. -/
public theorem dispatch_sound {Body : Type} {ks : Kinds} {impls : List (Impl Body)} {generic : String}
    {i : Instance} {b : Body} (h : dispatch ks impls generic i = .ok (some b)) :
    ∃ lk pre k post, kindPrecedence ks ks.depth i.kind.name = .ok lk ∧ lk = pre ++ k :: post ∧
      implFor impls generic k = some b ∧ ∀ k' ∈ pre, implFor impls generic k' = none := by
  unfold dispatch at h
  split at h
  · rename_i lk hlk
    have hf : lk.findSome? (implFor impls generic) = some b := by injection h
    obtain ⟨pre, k, post, hl, hk, hpre⟩ := List.findSome?_eq_some_iff.1 hf
    exact ⟨lk, pre, k, post, hlk, hl, hk, hpre⟩
  · cases h

/-! ## Teeth -/

/-- Two kinds with the same layout and initial state, `Mile` and `Kilo`, each with a law; `Trip`
inherits from `Mile`. -/
def lawAdmit : Term := Obend.Law.law3 Obend.Law.okT

/-- A natural field of a state. -/
def natField : Data → String → Option Nat
  | .record fs, f => match fs.lookup f with
    | some (.natural n) => some n
    | _ => none
  | _, _ => none

def tooth : Kinds := ⟨[
  ⟨"Mile", 1, ["n"], .record [("n", .natural 0)], lawAdmit, []⟩,
  ⟨"Kilo", 1, ["n"], .record [("n", .natural 0)], lawAdmit, []⟩,
  ⟨"Trip", 3, ["n"], .record [("n", .natural 0)], lawAdmit, ["Mile"]⟩]⟩

/-- The registry after `Mile`'s owner revised it. -/
def revised : Kinds := ⟨[
  ⟨"Mile", 2, ["n"], .record [("n", .natural 0)], lawAdmit, []⟩,
  ⟨"Kilo", 1, ["n"], .record [("n", .natural 0)], lawAdmit, []⟩,
  ⟨"Trip", 3, ["n"], .record [("n", .natural 0)], lawAdmit, ["Mile"]⟩]⟩

/-- `show` for each kind: the bodies say which. -/
def shows : List (Impl String) := [⟨"show", "Mile", "miles"⟩, ⟨"show", "Kilo", "kilometres"⟩]

/-- **Two kinds with equal fields are distinguished.** `a` is a `Mile`, `b` a `Kilo`, born in the
same state from kinds with the same layout; `show` reaches each kind's own implementation. A `Trip`
reaches `Mile`'s, its parent's. -/
theorem nominal_tooth :
    ((create tooth "Mile" "a" lawAdmit).toOption.map fun i => natField i.state "n",
      (create tooth "Kilo" "b" lawAdmit).toOption.map fun i => natField i.state "n") = (some (some 0), some (some 0)) ∧
    ((create tooth "Mile" "a" lawAdmit).toOption.bind fun a => (dispatch tooth shows "show" a).toOption) =
      some (some "miles") ∧
    ((create tooth "Kilo" "b" lawAdmit).toOption.bind fun b => (dispatch tooth shows "show" b).toOption) =
      some (some "kilometres") ∧
    ((create tooth "Trip" "t" lawAdmit).toOption.bind fun t => (dispatch tooth shows "show" t).toOption) =
      some (some "miles") ∧
    (kindPrecedence tooth tooth.depth "Trip").toOption = some ["Trip", "Mile"] := by
  decide +kernel

/-- A `Trip` born before `Mile` was revised: its effective law exists at birth; after the revision of
`Mile` it is still current (it pinned `Trip`, not `Mile`), while a `Mile` born before is stale by
name, and renewing it makes it current. -/
theorem stale_tooth :
    ((create tooth "Trip" "t" lawAdmit).toOption.map fun t => (effectiveOf tooth t).toOption.isSome) = some true ∧
    ((create tooth "Mile" "a" lawAdmit).toOption.map fun a =>
      match effectiveOf revised a with | .error (.stale p) => decide (p = ⟨"Mile", 1⟩) | _ => false) = some true ∧
    ((create tooth "Mile" "a" lawAdmit).toOption.bind fun a =>
      (renewKind revised a).toOption.map fun a' => (decide (a'.kind = ⟨"Mile", 2⟩), kindRefs.current revised a'.kind)) =
      some (true, true) := by
  decide +kernel

#tooth dispatch_sound by mutation dispatch := fun _ _ _ _ => .ok none
#tooth effectiveOf_ok by mutation effectiveOf := fun _ _ => .ok lawAdmit
#tooth create_carries by mutation create := fun _ k n l => .ok ⟨n, ⟨k, 0⟩, l, .natural 0⟩

end Obend.Kind
