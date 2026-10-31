module
/-
# Obend.Leaf.Residual — no `super` row is left in the vtable

`flatRow` replaces a layer's `super` by the literal record of the flattened row beneath it, and
`resolve` removes that literal only where it stands in projection position, `get {…} p`. A raw term
passing `super` first-class (`f super`) would leave the row literal in the method body, and the leaf
translation would have to materialize it. `superOnlyProjected` is the syntactic check that every
`super` is projected at a member of the row beneath (true of what Elaborate emits); under it, and
with no layer body or seed term writing a record literal of a flagged shape itself, the resolved
vtable contains no record literal of that shape (`vtable_clean`): every super row is gone.

`bad` is the shape predicate on a record's field names; take it to accept the name lists of the
flattened suffix rows (`suffixNames`).
-/
public import Obend.Leaf.Flatten
@[expose] public section
namespace Obend.Leaf
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
set_option autoImplicit false

/-- `t` contains a record literal whose field names `bad` accepts. -/
def recordBad (bad : List String → Bool) : Term → Bool
  | .hole _ σ => σ.attach.any fun x => recordBad bad x.1
  | .bound _ | .nat _ | .boolean _ | .label _ => false
  | .lam b | .reflect b | .metadata b | .project b | .inject _ b | .perform b | .done b | .get b _ =>
    recordBad bad b
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b | .split a _ b =>
    recordBad bad a || recordBad bad b
  | .extend i fs => recordBad bad i || fs.attach.any fun f => recordBad bad f.1.2
  | .record fs => bad (fs.map Prod.fst) || fs.attach.any fun f => recordBad bad f.1.2
  | .ifZero v z s | .ifBool v z s => recordBad bad v || recordBad bad z || recordBad bad s
  | .case sc arms => recordBad bad sc || arms.attach.any fun a => recordBad bad a.1.2
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)
    | (have h := (‹Subtype _›).2
       first | (have := List.sizeOf_lt_of_mem h; omega) | (have := sizeOf_snd_lt_of_mem h; omega))

/-- Every `super` (index `d`, moving under binders) is `get super p` with `p` among `ns`. -/
def superOnlyProjected (ns : List String) (d : Nat) : Term → Bool
  | .hole _ σ => σ.attach.all fun x => superOnlyProjected ns d x.1
  | .bound i => i != d
  | .nat _ | .boolean _ | .label _ => true
  | .lam b => superOnlyProjected ns (d + 1) b
  | .get (.bound i) p => i != d || ns.contains p
  | .reflect b | .metadata b | .project b | .inject _ b | .perform b | .done b | .get b _ =>
    superOnlyProjected ns d b
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b | .split a _ b =>
    superOnlyProjected ns d a && superOnlyProjected ns d b
  | .extend i fs => superOnlyProjected ns d i && fs.attach.all fun f => superOnlyProjected ns d f.1.2
  | .record fs => fs.attach.all fun f => superOnlyProjected ns d f.1.2
  | .ifZero v z s => superOnlyProjected ns d v && superOnlyProjected ns d z && superOnlyProjected ns (d + 1) s
  | .ifBool v z s => superOnlyProjected ns d v && superOnlyProjected ns d z && superOnlyProjected ns d s
  | .case sc arms => superOnlyProjected ns d sc && arms.attach.all fun a => superOnlyProjected ns (d + 1) a.1.2
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)
    | (have h := (‹Subtype _›).2
       first | (have := List.sizeOf_lt_of_mem h; omega) | (have := sizeOf_snd_lt_of_mem h; omega))

/-! ## Lemmas -/

theorem any_attach_fst {α : Type} (l : List α) (g : α → Bool) : (l.attach.any fun x => g x.1) = l.any g := by
  conv => rhs; rw [← List.attach_map_subtype_val l]
  rw [List.any_map]; rfl

theorem all_attach_fst {α : Type} (l : List α) (g : α → Bool) : (l.attach.all fun x => g x.1) = l.all g := by
  conv => rhs; rw [← List.attach_map_subtype_val l]
  rw [List.all_map]; rfl

theorem any_congr_mem {α : Type} {l : List α} {g h : α → Bool} (H : ∀ x ∈ l, g x = h x) :
    l.any g = l.any h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [H a List.mem_cons_self, ih fun x hx => H x (List.mem_cons_of_mem _ hx)]

theorem any_false_iff {α : Type} {l : List α} {g : α → Bool} : l.any g = false ↔ ∀ x ∈ l, g x = false := by
  simp [List.any_eq_false]

theorem all_true_iff {α : Type} {l : List α} {g : α → Bool} : l.all g = true ↔ ∀ x ∈ l, g x = true := by
  simp [List.all_eq_true]

theorem recordBad_rename (bad : List String → Bool) : (t : Term) → ∀ f : Nat → Nat,
    recordBad bad (t.rename f) = recordBad bad t
  | .hole n σ, f => by
    simp only [Term.rename, recordBad, any_attach_fst (g := recordBad bad), List.any_map, Function.comp_def]
    exact any_congr_mem fun x hx => recordBad_rename bad x f
  | .bound i, f | .nat _, f | .boolean _, f | .label _, f => by simp [Term.rename, recordBad]
  | .lam b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .reflect b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .metadata b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .project b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .inject _ b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .perform b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .done b, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .get b _, f => by simp only [Term.rename, recordBad]; exact recordBad_rename bad b _
  | .app a b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .mix a b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .fix a b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .specification a b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .prototype a b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .binary _ a b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .split a _ b, f => by simp only [Term.rename, recordBad, recordBad_rename bad a, recordBad_rename bad b]
  | .ifZero v z s, f => by
    simp only [Term.rename, recordBad, recordBad_rename bad v, recordBad_rename bad z, recordBad_rename bad s]
  | .ifBool v z s, f => by
    simp only [Term.rename, recordBad, recordBad_rename bad v, recordBad_rename bad z, recordBad_rename bad s]
  | .extend i fs, f => by
    simp only [Term.rename, recordBad, recordBad_rename bad i,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), List.any_map, Function.comp_def]
    congr 1
    exact any_congr_mem fun x hx => recordBad_rename bad x.2 f
  | .record fs, f => by
    simp only [Term.rename, recordBad, any_attach_fst (g := fun x : String × Term => recordBad bad x.2),
      List.any_map, Function.comp_def, List.map_map]
    congr 1
    exact any_congr_mem fun x hx => recordBad_rename bad x.2 f
  | .case sc arms, f => by
    simp only [Term.rename, recordBad, recordBad_rename bad sc,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), List.any_map, Function.comp_def]
    congr 1
    exact any_congr_mem fun x hx => recordBad_rename bad x.2 _
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hx; omega)

theorem find_rename (fs : List (String × Term)) (f : Nat → Nat) (p : String) :
    (fs.map fun x => (x.1, x.2.rename f)).find? (·.1 == p) =
      (fs.find? (·.1 == p)).map fun x => (x.1, x.2.rename f) := by
  simp [List.find?_map, Function.comp_def]

theorem resolveGet_rename (t : Term) (p : String) (f : Nat → Nat) :
    resolveGet (t.rename f) p = (resolveGet t p).rename f := by
  cases t with
  | record fs =>
    simp only [Term.rename, resolveGet, find_rename]
    cases fs.find? (·.1 == p) with
    | none => simp [Term.rename]
    | some x => rfl
  | _ => simp [Term.rename, resolveGet]

theorem map_congr_mem {l : List (String × Term)} {g h : Term → Term} (H : ∀ x ∈ l, g x.2 = h x.2) :
    (l.map fun x => (x.1, g x.2)) = l.map fun x => (x.1, h x.2) :=
  List.map_congr_left fun x hx => by rw [H x hx]

/-- Static resolution commutes with renaming. -/
theorem resolve_rename : (t : Term) → ∀ f : Nat → Nat, resolve (t.rename f) = (resolve t).rename f
  | .hole n σ, f => by
    simp only [Term.rename, resolve, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun x hx => resolve_rename x f
  | .bound i, f => by simp [Term.rename, resolve]
  | .nat _, f | .boolean _, f | .label _, f => by simp [Term.rename, resolve]
  | .lam b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .reflect b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .metadata b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .project b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .inject _ b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .perform b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .done b, f => by simp only [Term.rename, resolve, resolve_rename b]
  | .get b p, f => by simp only [Term.rename, resolve, resolve_rename b, resolveGet_rename]
  | .app a b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .mix a b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .fix a b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .specification a b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .prototype a b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .binary _ a b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .split a _ b, f => by simp only [Term.rename, resolve, resolve_rename a, resolve_rename b]
  | .ifZero v z s, f => by simp only [Term.rename, resolve, resolve_rename v, resolve_rename z, resolve_rename s]
  | .ifBool v z s, f => by simp only [Term.rename, resolve, resolve_rename v, resolve_rename z, resolve_rename s]
  | .extend i fs, f => by
    simp only [Term.rename, resolve, resolve_rename i, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun x hx => by rw [resolve_rename x.2 f]
  | .record fs, f => by
    simp only [Term.rename, resolve, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun x hx => by rw [resolve_rename x.2 f]
  | .case sc arms, f => by
    simp only [Term.rename, resolve, resolve_rename sc, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun x hx => by rw [resolve_rename x.2 _]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hx; omega)

/-! ## The theorem -/

theorem recordBad_record {bad : List String → Bool} {fs : List (String × Term)}
    (h : recordBad bad (.record fs) = false) : bad (fs.map Prod.fst) = false ∧ ∀ x ∈ fs, recordBad bad x.2 = false := by
  simp only [recordBad, Bool.or_eq_false_iff,
    any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at h
  exact h

/-- Reading a field of a clean record is clean. -/
theorem resolveGet_clean {bad : List String → Bool} {t : Term} (p : String) (h : recordBad bad t = false) :
    recordBad bad (resolveGet t p) = false := by
  unfold resolveGet
  split
  · rename_i fs
    split
    · rename_i n b hit
      exact (recordBad_record h).2 _ (List.mem_of_find?_eq_some hit)
    · simpa only [recordBad] using h
  · simpa only [recordBad] using h

/-- The hypotheses of `resolve_subst_clean` survive a binder. -/
structure CleanSub (bad : List String → Bool) (ns : List String) (d : Nat) (σ : Nat → Term) : Prop where
  row : ∃ R : List (String × Term), σ d = .record R ∧ R.map Prod.fst = ns ∧
    ∀ e ∈ R, recordBad bad (resolve e.2) = false
  rest : ∀ i, i ≠ d → recordBad bad (resolve (σ i)) = false

theorem CleanSub.lift {bad : List String → Bool} {ns : List String} {d : Nat} {σ : Nat → Term}
    (h : CleanSub bad ns d σ) : CleanSub bad ns (d + 1) (liftSubstitution σ) where
  row := by
    obtain ⟨R, hσ, hn, he⟩ := h.row
    refine ⟨R.map fun x => (x.1, x.2.rename Nat.succ), ?_, ?_, ?_⟩
    · simp only [liftSubstitution, hσ, Term.rename]
    · rw [← hn]; simp [List.map_map, Function.comp_def]
    · intro e he'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
      simp only [resolve_rename, recordBad_rename]
      exact he x hx
  rest := by
    intro i hi
    match i with
    | 0 => simp [liftSubstitution, resolve, recordBad]
    | j + 1 =>
      simp only [liftSubstitution, resolve_rename, recordBad_rename]
      exact h.rest j (by omega)

/-- **Under `superOnlyProjected`, substituting the row record for `super` and resolving leaves no
record of a flagged shape** that the body and the row's resolved entries did not already hold. -/
theorem resolve_subst_clean (bad : List String → Bool) (ns : List String) :
    (b : Term) → ∀ (d : Nat) (σ : Nat → Term), superOnlyProjected ns d b = true → recordBad bad b = false →
      CleanSub bad ns d σ → recordBad bad (resolve (b.substitute σ)) = false
  | .hole n xs, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, all_attach_fst (g := superOnlyProjected ns d), all_true_iff] at hs
    simp only [recordBad, any_attach_fst (g := recordBad bad), any_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, any_attach_fst (g := recordBad bad), any_false_iff,
      List.map_map, List.mem_map, Function.comp_def]
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_subst_clean bad ns x d σ (hs x hx) (hb x hx) hσ
  | .bound i, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, bne_iff_ne, ne_eq] at hs
    simp only [Term.substitute]
    exact hσ.rest i hs
  | .nat _, _, _, _, _, _ | .boolean _, _, _, _, _, _ | .label _, _, _, _, _, _ => by
    simp [Term.substitute, resolve, recordBad]
  | .lam b, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected] at hs
    simp only [recordBad] at hb
    simp only [Term.substitute, resolve, recordBad]
    exact resolve_subst_clean bad ns b (d + 1) _ hs hb hσ.lift
  | .reflect b, d, σ, hs, hb, hσ | .metadata b, d, σ, hs, hb, hσ | .project b, d, σ, hs, hb, hσ
  | .inject _ b, d, σ, hs, hb, hσ | .perform b, d, σ, hs, hb, hσ | .done b, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected] at hs
    simp only [recordBad] at hb
    simp only [Term.substitute, resolve, recordBad]
    exact resolve_subst_clean bad ns b d σ hs hb hσ
  | .get g p, d, σ, hs, hb, hσ => by
    simp only [Term.substitute, resolve]
    by_cases hg : ∃ i, g = .bound i
    · obtain ⟨i, rfl⟩ := hg
      simp only [Term.substitute]
      by_cases hi : i = d
      · subst hi
        simp only [superOnlyProjected, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at hs
        obtain ⟨R, hR, hn, he⟩ := hσ.row
        rw [hR]
        simp only [resolve, resolveGet]
        subst hn
        obtain ⟨x, hx, hxp⟩ := List.mem_map.1 hs
        have hfind : ((R.map fun f => (f.1, resolve f.2)).find? (·.1 == p)).isSome := by
          rw [List.find?_isSome]
          exact ⟨(x.1, resolve x.2), List.mem_map.2 ⟨x, hx, rfl⟩, by simp [hxp]⟩
        split
        · rename_i n b hit
          obtain ⟨y, hy, hyb⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hit)
          simp only [Prod.mk.injEq] at hyb
          rw [← hyb.2]
          exact he y hy
        · rename_i hnone
          rw [hnone] at hfind; cases hfind
      · exact resolveGet_clean p (hσ.rest i hi)
    · have hs' : superOnlyProjected ns d g = true := by
        cases g with
        | bound i => exact absurd ⟨i, rfl⟩ hg
        | _ => simp only [superOnlyProjected] at hs ⊢; try exact hs
      simp only [recordBad] at hb
      exact resolveGet_clean p (resolve_subst_clean bad ns g d σ hs' hb hσ)
  | .app a b, d, σ, hs, hb, hσ | .mix a b, d, σ, hs, hb, hσ | .fix a b, d, σ, hs, hb, hσ
  | .specification a b, d, σ, hs, hb, hσ | .prototype a b, d, σ, hs, hb, hσ
  | .binary _ a b, d, σ, hs, hb, hσ | .split a _ b, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, Bool.and_eq_true] at hs
    simp only [recordBad, Bool.or_eq_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, Bool.or_eq_false_iff]
    exact ⟨resolve_subst_clean bad ns a d σ hs.1 hb.1 hσ, resolve_subst_clean bad ns b d σ hs.2 hb.2 hσ⟩
  | .ifBool v z s, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, Bool.and_eq_true] at hs
    simp only [recordBad, Bool.or_eq_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, Bool.or_eq_false_iff]
    exact ⟨⟨resolve_subst_clean bad ns v d σ hs.1.1 hb.1.1 hσ, resolve_subst_clean bad ns z d σ hs.1.2 hb.1.2 hσ⟩,
      resolve_subst_clean bad ns s d σ hs.2 hb.2 hσ⟩
  | .ifZero v z s, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, Bool.and_eq_true] at hs
    simp only [recordBad, Bool.or_eq_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, Bool.or_eq_false_iff]
    exact ⟨⟨resolve_subst_clean bad ns v d σ hs.1.1 hb.1.1 hσ, resolve_subst_clean bad ns z d σ hs.1.2 hb.1.2 hσ⟩,
      resolve_subst_clean bad ns s (d + 1) _ hs.2 hb.2 hσ.lift⟩
  | .extend i fs, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, Bool.and_eq_true,
      all_attach_fst (g := fun x : String × Term => superOnlyProjected ns d x.2), all_true_iff] at hs
    simp only [recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff, List.map_map,
      List.mem_map, Function.comp_def]
    refine ⟨resolve_subst_clean bad ns i d σ hs.1 hb.1 hσ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_subst_clean bad ns x.2 d σ (hs.2 x hx) (hb.2 x hx) hσ
  | .record fs, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected,
      all_attach_fst (g := fun x : String × Term => superOnlyProjected ns d x.2), all_true_iff] at hs
    simp only [recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff, List.map_map,
      List.mem_map, Function.comp_def]
    refine ⟨hb.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_subst_clean bad ns x.2 d σ (hs x hx) (hb.2 x hx) hσ
  | .case sc arms, d, σ, hs, hb, hσ => by
    simp only [superOnlyProjected, Bool.and_eq_true,
      all_attach_fst (g := fun x : String × Term => superOnlyProjected ns (d + 1) x.2), all_true_iff] at hs
    simp only [recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at hb
    simp only [Term.substitute, resolve, recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff, List.map_map,
      List.mem_map, Function.comp_def]
    refine ⟨resolve_subst_clean bad ns sc d σ hs.1 hb.1 hσ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_subst_clean bad ns x.2 (d + 1) _ (hs.2 x hx) (hb.2 x hx) hσ.lift
termination_by b => sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hx; omega)

/-- Static resolution introduces no record literal: it only selects among the term's own. -/
theorem resolve_clean (bad : List String → Bool) : (t : Term) → recordBad bad t = false →
    recordBad bad (resolve t) = false
  | .hole n xs, h => by
    simp only [recordBad, any_attach_fst (g := recordBad bad), any_false_iff] at h
    simp only [resolve, recordBad, any_attach_fst (g := recordBad bad), any_false_iff, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_clean bad x (h x hx)
  | .bound _, _ | .nat _, _ | .boolean _, _ | .label _, _ => by simp [resolve, recordBad]
  | .lam b, h | .reflect b, h | .metadata b, h | .project b, h | .inject _ b, h | .perform b, h
  | .done b, h => by
    simp only [recordBad] at h
    simp only [resolve, recordBad]
    exact resolve_clean bad b h
  | .get g p, h => by
    simp only [recordBad] at h
    simp only [resolve]
    exact resolveGet_clean p (resolve_clean bad g h)
  | .app a b, h | .mix a b, h | .fix a b, h | .specification a b, h | .prototype a b, h
  | .binary _ a b, h | .split a _ b, h => by
    simp only [recordBad, Bool.or_eq_false_iff] at h
    simp only [resolve, recordBad, Bool.or_eq_false_iff]
    exact ⟨resolve_clean bad a h.1, resolve_clean bad b h.2⟩
  | .ifZero v z s, h | .ifBool v z s, h => by
    simp only [recordBad, Bool.or_eq_false_iff] at h
    simp only [resolve, recordBad, Bool.or_eq_false_iff]
    exact ⟨⟨resolve_clean bad v h.1.1, resolve_clean bad z h.1.2⟩, resolve_clean bad s h.2⟩
  | .extend i fs, h => by
    simp only [recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at h
    simp only [resolve, recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff, List.mem_map]
    refine ⟨resolve_clean bad i h.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_clean bad x.2 (h.2 x hx)
  | .record fs, h => by
    simp only [recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at h
    simp only [resolve, recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff, List.mem_map,
      List.map_map, Function.comp_def]
    refine ⟨h.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_clean bad x.2 (h.2 x hx)
  | .case sc arms, h => by
    simp only [recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff] at h
    simp only [resolve, recordBad, Bool.or_eq_false_iff,
      any_attach_fst (g := fun x : String × Term => recordBad bad x.2), any_false_iff, List.mem_map]
    refine ⟨resolve_clean bad sc h.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact resolve_clean bad x.2 (h.2 x hx)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hx; omega)

/-! ## The vtable -/

/-- Every layer projects `super` only, at members of the flattened row beneath it. -/
def superOnlyProjectedRow (seed : List (String × Term)) : List Layer → Bool
  | [] => true
  | L :: rest => L.fields.all (fun f => superOnlyProjected ((flatRow seed rest).map Prod.fst) 0 f.2) &&
      superOnlyProjectedRow seed rest

/-- No layer body and no seed term writes a record literal of a flagged shape itself. -/
def cleanRow (bad : List String → Bool) (seed : List (String × Term)) (ls : List Layer) : Bool :=
  seed.all (fun f => !recordBad bad f.2) && ls.all fun L => L.fields.all fun f => !recordBad bad f.2

/-- The name lists of the flattened suffix rows: the shapes a `super` row literal has. -/
def suffixNames (seed : List (String × Term)) : List Layer → List (List String)
  | [] => [(flatRow seed []).map Prod.fst]
  | L :: rest => ((flatRow seed (L :: rest)).map Prod.fst) :: suffixNames seed rest

theorem toSelf_clean (bad : List String → Bool) (R : List (String × Term)) (hR : ∀ e ∈ R, recordBad bad (resolve e.2) = false) :
    CleanSub bad (R.map Prod.fst) 0 (toSelf (.record R)) where
  row := ⟨R, rfl, rfl, hR⟩
  rest i hi := by
    match i with
    | 0 => exact absurd rfl hi
    | 1 => simp [toSelf, resolve, recordBad]
    | k + 2 => simp [toSelf, resolve, recordBad]

theorem flatRow_clean (bad : List String → Bool) (seed : List (String × Term)) :
    ∀ ls : List Layer, superOnlyProjectedRow seed ls = true → cleanRow bad seed ls = true →
      ∀ e ∈ flatRow seed ls, recordBad bad (resolve e.2) = false
  | [], _, hc, e, he => by
    simp only [cleanRow, Bool.and_eq_true, all_true_iff, Bool.not_eq_true'] at hc
    simp only [flatRow, mapFields, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    simp only [resolve_rename, recordBad_rename]
    exact resolve_clean bad x.2 (hc.1 x hx)
  | L :: rest, hs, hc, e, he => by
    simp only [superOnlyProjectedRow, Bool.and_eq_true, all_true_iff] at hs
    have hc' : cleanRow bad seed rest = true := by
      simp only [cleanRow, Bool.and_eq_true, all_true_iff, List.mem_cons] at hc ⊢
      exact ⟨hc.1, fun L' hL' => hc.2 L' (.inr hL')⟩
    have ih := flatRow_clean bad seed rest hs.2 hc'
    have hL : ∀ f ∈ L.fields, recordBad bad f.2 = false := by
      simp only [cleanRow, Bool.and_eq_true, all_true_iff, List.mem_cons, Bool.not_eq_true'] at hc
      exact hc.2 L (.inl rfl)
    have hfs : ∀ x ∈ mapFields (·.substitute (toSelf (.record (flatRow seed rest)))) L.fields,
        recordBad bad (resolve x.2) = false := by
      intro x hx
      simp only [mapFields, List.mem_map] at hx
      obtain ⟨f, hf, rfl⟩ := hx
      exact resolve_subst_clean bad _ f.2 0 _ (hs.1 f hf) (hL f hf) (toSelf_clean bad _ ih)
    simp only [flatRow] at he
    split at he
    · exact hfs e he
    · unfold extendFields at he
      rcases List.mem_append.1 he with h | h
      · exact hfs e h
      · exact ih e (List.mem_filter.1 h).1

/-- **No residual `super` row.** When every layer projects `super` only (`superOnlyProjectedRow`,
true of what Elaborate emits) and no layer body or seed term writes a record literal of a flagged
shape itself, the resolved vtable contains no record literal of that shape; with `bad` the suffix
rows' shapes (`suffixNames`), no `super` row is left anywhere in it. -/
theorem vtable_clean (bad : List String → Bool) (C : Composition)
    (hs : superOnlyProjectedRow C.seed C.layers = true) (hc : cleanRow bad C.seed C.layers = true) :
    ∀ e ∈ C.vtable, recordBad bad e.2 = false := by
  intro e he
  simp only [Composition.vtable, mapFields, List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  exact flatRow_clean bad C.seed C.layers hs hc x hx

end Obend.Leaf
end
