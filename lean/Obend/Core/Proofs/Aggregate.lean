module
/- The aggregate contract (lane C2, 2026-11-01): how a resourceful aggregate may be dropped,
transferred, split and returned, and what a terminal state owes, as theorems over `Step`, the
typing relation and the machine.

* **Dropped**: never, if it holds a `linear` hypothesis. Every position that discards part of an
  aggregate (a projection's target, an extension's target, a parameter that is not `linear`)
  requires `linearFree` of what it discards (`get_target_linearFree`, `extend_target_linearFree`,
  `transfer_linear`); an aggregate that holds only `affine` hypotheses may be dropped.
* **Transferred**: an argument that uses a `linear` hypothesis goes only to a `linear` parameter
  (`transfer_linear`), which uses it exactly once (`PartialTyping.lambda`'s `fits`).
* **Split**: the destructor passes every field exactly once; its redex and reduct count every
  hypothesis equally (`split_accounts`); on the machine it passes a permutation of the record's
  field addresses (`machine_split_passes_all`).
* **Returned**: along any reduction of a closed program over custody handles, every handle is held
  exactly as often as at the start, so a terminal value owes each handle it was given
  (`terminal_owes`). -/
public import Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Check
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.SubjectReduction

namespace Obend.Core.Proofs.Aggregate
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Machine Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation
open Obend.Core.Proofs.SubjectReduction
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences fieldOccurrences uses_determined)
set_option autoImplicit false

local macro "inv_other" : tactic => `(tactic| (intros; first | trivial | (rename_i e; cases e)))

/-- A destructor's derivation, through conversions. -/
theorem split_inv {a : Assumptions} {Γ : Context} {t f : Term} {names : List String} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.split t names f) T u) :
    ∃ row F tu fu, PartialTyping a Γ t row tu ∧ PartialTyping a Γ f F fu ∧ names.Nodup ∧
      SplitCovers row names = true ∧ u = addUses tu fu := by
  generalize ht : Term.split t names f = t0 at h
  revert ht; revert t f names
  apply PartialTyping.rec
    (motive_1 := fun Γ term _ u _ => ∀ t f names, Term.split t names f = term →
      ∃ row F tu fu, PartialTyping a Γ t row tu ∧ PartialTyping a Γ f F fu ∧ names.Nodup ∧
        SplitCovers row names = true ∧ u = addUses tu fu)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case split =>
    intro Γ t' f' names' row F R tu fu ht hf nodup covers _ _ _ t f names eq
    cases eq; exact ⟨row, F, tu, fu, ht, hf, nodup, covers, rfl⟩
  case conversion =>
    intro Γ term actual expected u _ _ ih t f names eq; exact ih t f names eq
  all_goals inv_other

/-- **Split accounts for every component.** A typed destructor redex and its reduct count every
hypothesis equally (not only the `linear` ones): each field is passed exactly once, none is dropped
and none copied. -/
public theorem split_accounts {a : Assumptions} {Γ : Context} {fields : List (String × Term)}
    {names : List String} {f : Term} {T : Ty} {u : Uses} {values : List Term}
    (typed : PartialTyping a Γ (.split (.record fields) names f) T u)
    (found : splitValues fields names = some values) :
    occurrences Γ.length (applyAll f values) = u := by
  obtain ⟨row, F, tu, fu, ht, hf, nodup, covers, rfl⟩ := split_inv typed
  obtain ⟨distinct, covered⟩ := record_covered ht covers
  have tl := Obend.Core.MachineTyping.source_uses_length ht
  have fl := Obend.Core.MachineTyping.source_uses_length hf
  refine uses_ext (by simp [occurrences_length, addUses, tl, fl]) fun j => ?_
  rw [split_redex_counts Γ.length j f distinct nodup covered found, getD_addUses (tl.trans fl.symm),
    occ_of hf j]
  have := occ_of ht j
  simp only [occurrences] at this
  rw [this]; omega

/-- **Dropped: a projection's target holds no `linear` hypothesis.** -/
public theorem get_target_linearFree {a : Assumptions} {Γ : Context} {t : Term} {name : String} {T : Ty}
    {u : Uses} (h : PartialTyping a Γ (.get t name) T u) : linearFree Γ u = true := by
  generalize ht : Term.get t name = t0 at h
  revert ht; revert t name
  apply PartialTyping.rec
    (motive_1 := fun Γ term _ u _ => ∀ t name, Term.get t name = term → linearFree Γ u = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case get =>
    intro Γ t' _ _ u _ _ _ _ free _ t name eq; cases eq; exact free
  case conversion =>
    intro Γ term actual expected u _ _ ih t name eq; exact ih t name eq
  all_goals inv_other

/-- **Dropped: an extension's target holds no `linear` hypothesis** (the extension may overwrite
the field that holds it). -/
public theorem extend_target_linearFree {a : Assumptions} {Γ : Context} {t : Term}
    {fields : List (String × Term)} {T : Ty} {u : Uses} (h : PartialTyping a Γ (.extend t fields) T u) :
    ∃ tT tu, PartialTyping a Γ t tT tu ∧ linearFree Γ tu = true := by
  generalize ht : Term.extend t fields = t0 at h
  revert ht; revert t fields
  apply PartialTyping.rec
    (motive_1 := fun Γ term _ u _ => ∀ t fields, Term.extend t fields = term →
      ∃ tT tu, PartialTyping a Γ t tT tu ∧ linearFree Γ tu = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case extend =>
    intro Γ t' fields' tT _ tu _ _ hT _ _ _ free _ _ t fields eq; cases eq; exact ⟨tT, tu, hT, free⟩
  case conversion =>
    intro Γ term actual expected u _ _ ih t fields eq; exact ih t fields eq
  all_goals inv_other

/-- **Transferred: only to a `linear` parameter.** An argument that uses a `linear` hypothesis is
passed to a parameter whose quantity is `linear`; every other parameter receives a `linearFree`
argument. -/
public theorem transfer_linear {a : Assumptions} {Γ : Context} {f r : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a Γ (.app f r) T u) :
    ∃ F reuse q D C ru, PartialTyping a Γ r D ru ∧ callable F = .arrow reuse q D C ∧
      (q = .linear ∨ linearFree Γ ru = true) := by
  generalize ht : Term.app f r = t0 at h
  revert ht; revert f r
  apply PartialTyping.rec
    (motive_1 := fun Γ term _ u _ => ∀ f r, Term.app f r = term →
      ∃ F reuse q D C ru, PartialTyping a Γ r D ru ∧ callable F = .arrow reuse q D C ∧
        (q = .linear ∨ linearFree Γ ru = true))
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case application =>
    intro Γ f' r' F A D C fu ru reuse q _ hr shape eqA allowed _ _ f r eq
    cases eq; subst eqA
    refine ⟨F, reuse, q, A, C, ru, hr, shape, ?_⟩
    simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at allowed
    exact allowed.1.2
  case conversion =>
    intro Γ term actual expected u _ _ ih f r eq; exact ih f r eq
  all_goals inv_other

/-- **Returned: a terminal value owes what it was given.** A closed program over `k` custody
handles, within budget, reduces only to terms that hold each handle exactly as often as the
program did: a value it reaches holds them all. -/
public theorem terminal_owes {a : Assumptions} {k : Nat} {t v : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a (custodyContext k) t T u) (safe : safeUses (custodyContext k) u = true)
    (evaluates : Evaluates t v) {j : Nat} (hj : j < k) :
    (occurrences k v).getD j 0 = u.getD j 0 :=
  custody_conserved typed safe evaluates.1 hj

/-! ### The machine's destructor passes every field address once -/

theorem splitValues_pairs' {α : Type} {fields : List (String × α)} :
    ∀ {names : List String} {values : List α}, splitValues fields names = some values →
      ∃ pairs : List (String × α), pairs.map Prod.fst = names ∧ pairs.map Prod.snd = values ∧
        ∀ p ∈ pairs, fields.find? (fun field => field.1 == p.1) = some p
  | [], values, h => by simp [splitValues] at h; subst h; exact ⟨[], rfl, rfl, by simp⟩
  | name :: names, values, h => by
    simp only [splitValues, bind, Option.bind] at h
    split at h
    · cases h
    · rename_i found heq
      obtain ⟨label, body⟩ := found
      simp only at h
      split at h
      · cases h
      · rename_i rest hrest
        simp only [pure, Option.some.injEq] at h
        subst h
        obtain ⟨pairs, hn, hv, hp⟩ := splitValues_pairs' hrest
        have hl : label = name := by have := List.find?_some heq; simpa using this
        subst hl
        refine ⟨(label, body) :: pairs, by simp [hn], by simp [hv], ?_⟩
        intro p hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · exact heq
        · exact hp p hp'

theorem find_of_nodup {α : Type} : ∀ {fields : List (String × α)}, (fields.map Prod.fst).Nodup →
    ∀ {field : String × α}, field ∈ fields → fields.find? (fun f => f.1 == field.1) = some field
  | [], _, _, h => by simp at h
  | head :: rest, nodup, field, member => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp
    · have ne : head.1 ≠ field.1 := fun e => nodup.1 ⟨field, member, e.symm⟩
      simp [ne, find_of_nodup nodup.2 member]

/-- **The machine's destructor drops no field.** When a record value's labels are distinct and the
destructor names them all, the addresses it passes (one indirection cell each) are a permutation of
the record's field addresses: every field is passed exactly once. Typed records have distinct labels
(`PartialTyping.record`), and a covering destructor names every label (`SplitCovers`). -/
public theorem machine_split_passes_all {fields : List (String × Address)} {names : List String}
    {addresses : List Address} (distinct : (fields.map Prod.fst).Nodup) (nodup : names.Nodup)
    (covered : ∀ f ∈ fields, f.1 ∈ names) (found : splitValues fields names = some addresses) :
    addresses.Perm (fields.map Prod.snd) := by
  obtain ⟨pairs, hn, hv, hp⟩ := splitValues_pairs' found
  have pairsNodup : pairs.Nodup := by
    have : (pairs.map Prod.fst).Nodup := hn ▸ nodup
    clear hn hv hp
    induction pairs with
    | nil => exact List.nodup_nil
    | cons p ps ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at this
      exact List.nodup_cons.mpr ⟨fun m => this.1 ⟨p, m, rfl⟩, ih this.2⟩
  have fieldsNodup : fields.Nodup := by
    clear hn hv hp found covered
    induction fields with
    | nil => exact List.nodup_nil
    | cons p ps ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at distinct
      exact List.nodup_cons.mpr ⟨fun m => distinct.1 ⟨p, m, rfl⟩, ih distinct.2⟩
  have perm : pairs.Perm fields := by
    refine (List.perm_ext_iff_of_nodup pairsNodup fieldsNodup).mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact List.mem_of_find?_eq_some (hp x hx)
    · have hname : x.1 ∈ names := covered x hx
      rw [← hn] at hname
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hname
      have := hp y hy
      rw [he, find_of_nodup distinct hx] at this
      cases this; exact hy
  rw [← hv]; exact perm.map Prod.snd

/-- The machine's step at a destructor allocates exactly one cell per passed address, each an
indirection to its field (`bound i` over the passed addresses), and pushes one argument frame per
cell: the step is `allocateFields` over `splitCells`, nothing else. -/
public theorem machine_split_step (heap : Array Cell) (fields : List (String × Address)) (names : List String)
    (function : Term) (environment : Environment) (rest : List Frame) (addresses : List Address)
    (found : splitValues fields names = some addresses) :
    stepRaw ⟨heap, .returned (.record fields), .split names function environment :: rest⟩ =
      let allocated := allocateFields heap addresses (splitCells addresses.length)
      ⟨allocated.1, .evaluate function environment, splitFrames (allocated.2.map Prod.snd) ++ rest⟩ := by
  simp [stepRaw, found]

end Obend.Core.Proofs.Aggregate
