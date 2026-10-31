module
/- T7 of the quote orientation (`review/QUOTE-ORIENTATION-20261101.md` §4), lane C2 (2026-11-01):
the usage-composed contextual substitution for `splice`.

A template `t` checked in hypotheses `Ψ` and a filling `f` checked in the SAME hypotheses (open code,
not `Scoped 0`) at the type of hypothesis `x` give a spliced term `t[x := f]` checked in `Ψ` at the
template's type. Its uses are the composition `u[x ↦ 0] + u[x] · uf` (`spliceUses`): pointwise at
most that, and exactly that at every `linear` hypothesis. Two premises, both decidable:

* `spliceAllowed`: the filling uses its hypotheses as an argument passed to a binder of `x`'s
  quantity may (`argumentAllowed`'s quantity clauses): no `linear` hypothesis unless `x` is
  `linear`, only reusable captures if `x` is `unrestricted`;
* `spliceSafe`: the composed uses are within every hypothesis's quantity (`safeQuantity`). A
  hypothesis the template uses more than once multiplies its filling's uses; this premise is what
  refuses a once-resource laundered through a duplicated hole.

The result is again `Code Ψ A θ`, so splices compose hole by hole. The proof is the typed open
substitution of subject reduction (`subst_typed`) at the copy of `x` that weakening inserts beside
it; no new induction over the typing. -/
public import Obend.Core.Proofs.SubjectReduction.Substitution
public import Obend.Core.Code
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Check

namespace Obend.Core.Proofs.Splice
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation Obend.Core.Proofs.SubjectReduction
open Obend.Core.Proofs.Preservation (source_insert_binding shiftIndex)
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences uses_determined)
set_option autoImplicit false

/-- Hypothesis `x` replaced by `f`; every other hypothesis kept where it is. -/
@[expose] public def fillAt (x : Nat) (f : Term) : Nat → Term := fun i => if i = x then f else .bound i

/-- The spliced term. -/
@[expose] public def splice (x : Nat) (template filling : Term) : Term := template.substitute (fillAt x filling)

/-- The composed uses at hypothesis `j`: the template's own use of `j` (none of `x`, which is filled),
plus the filling's use of `j` once for every use of `x`. -/
@[expose] public def spliceUses (u : Uses) (x : Nat) (uf : Uses) (j : Nat) : Nat :=
  (if j = x then 0 else u.getD j 0) + u.getD x 0 * uf.getD j 0

/-- The filling may stand where a hypothesis of quantity `q` stood: `argumentAllowed`'s quantity
clauses. -/
@[expose] public def spliceAllowed (a : Assumptions) (q : Quantity) (Ψ : Context) (uf : Uses) : Bool :=
  (q == .linear || linearFree Ψ uf) && (q != .unrestricted || reusableCaptures a.shareableVariables Ψ uf)

/-- Every composed count is within its hypothesis's quantity. -/
@[expose] public def spliceSafe (Ψ : Context) (u : Uses) (x : Nat) (uf : Uses) : Bool :=
  (List.range Ψ.length).all fun j => match Ψ[j]? with
    | some c => safeQuantity c.quantity (spliceUses u x uf j)
    | none => true

theorem spliceSafe_at {Ψ : Context} {u : Uses} {x : Nat} {uf : Uses} (h : spliceSafe Ψ u x uf = true)
    {j : Nat} {c : Binding} (hj : Ψ[j]? = some c) : safeQuantity c.quantity (spliceUses u x uf j) = true := by
  have lt : j < Ψ.length := (List.getElem?_eq_some_iff.mp hj).1
  have := List.all_eq_true.mp h j (List.mem_range.mpr lt)
  simpa [hj] using this

/-! ### The inserted copy -/

theorem insert_erase {Ψ : Context} {x : Nat} {b : Binding} (hx : Ψ[x]? = some b) :
    (Ψ.insertIdx x b).eraseIdx (x + 1) = Ψ := by
  have lt : x < Ψ.length := (List.getElem?_eq_some_iff.mp hx).1
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_eraseIdx]
  by_cases hj : j < x + 1
  · rw [if_pos hj, List.getElem?_insertIdx]
    by_cases hjx : j < x
    · rw [if_pos hjx]
    · have e : j = x := by omega
      subst e
      rw [if_neg hjx, if_pos rfl, if_pos (by omega), hx]
  · rw [if_neg hj, List.getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]
    simp

theorem getD_insert_zero {u : Uses} {x : Nat} (hl : x ≤ u.length) (j : Nat) :
    (u.insertIdx x 0).getD j 0 = if j < x then u.getD j 0 else if j = x then 0 else u.getD (j - 1) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_insertIdx]
  by_cases h1 : j < x
  · simp [h1]
  · by_cases h2 : j = x
    · subst h2; simp [hl]
    · simp [h1, h2]

/-- The image of the weakened template's uses, substituted at the copy of `x`, is `spliceUses`. -/
theorem image_insert {u uf : Uses} {x : Nat} (hl : x ≤ u.length) (j : Nat) :
    Image (x + 1) uf (u.insertIdx x 0) j = spliceUses u x uf j := by
  unfold Image spliceUses skipAt
  simp only [getD_insert_zero hl]
  have n1 : ¬ x + 1 < x := by omega
  have n2 : x + 1 ≠ x := by omega
  by_cases h1 : j < x
  · simp [h1, show j < x + 1 by omega, show j ≠ x by omega, n1]
  · by_cases h2 : j = x
    · subst h2; simp [n1]
    · simp [h1, h2, n1, n2, show ¬ j < x + 1 by omega, show ¬ j + 1 < x by omega,
        show j + 1 ≠ x by omega]

theorem splice_rename {x : Nat} {t f : Term} :
    (t.rename (shiftIndex x)).substitute
        (fun k => if k < x + 1 then .bound k else if k = x + 1 then f else .bound (k - 1)) =
      splice x t f := by
  rw [Obend.Core.TermTraverse.rename_substitute]
  unfold splice
  congr 1
  funext i
  unfold shiftIndex fillAt
  by_cases h1 : i < x
  · simp [h1, show i < x + 1 by omega, show i ≠ x by omega]
  · by_cases h2 : i = x
    · subst h2; simp
    · simp [h1, h2, show ¬ i + 1 < x + 1 by omega, show i + 1 ≠ x + 1 by omega]

/-! ### T7 -/

/-- **The usage-composed contextual substitution** (relational form). -/
public theorem splice_typed {a : Assumptions} {Ψ : Context} {t f : Term} {T : Ty} {u uf : Uses} {x : Nat}
    {b : Binding} (typed : PartialTyping a Ψ t T u) (valid : validContext a.shareableVariables Ψ = true)
    (hx : Ψ[x]? = some b) (filled : PartialTyping a Ψ f b.type uf)
    (allowed : spliceAllowed a b.quantity Ψ uf = true) (safe : spliceSafe Ψ u x uf = true) :
    ∃ u', PartialTyping a Ψ (splice x t f) T u' ∧ safeUses Ψ u' = true ∧
      (∀ j, u'.getD j 0 ≤ spliceUses u x uf j) ∧
      (∀ j, LinearAt Ψ j → u'.getD j 0 = spliceUses u x uf j) := by
  have lt : x < Ψ.length := (List.getElem?_eq_some_iff.mp hx).1
  have ul : u.length = Ψ.length := source_uses_length typed
  have vb : validContext a.shareableVariables [b] = true := by
    unfold validContext at valid ⊢
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact List.all_eq_true.mp valid b (List.mem_of_getElem? hx)
  have w := source_insert_binding typed x b (by omega) vb
  have er : (Ψ.insertIdx x b).eraseIdx (x + 1) = Ψ := insert_erase hx
  have hb' : (Ψ.insertIdx x b)[x + 1]? = some b := by
    rw [List.getElem?_insertIdx_of_gt (by omega)]; simpa using hx
  simp only [spliceAllowed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at allowed
  obtain ⟨al, au⟩ := allowed
  have S : TSub a (Ψ.insertIdx x b) (x + 1)
      (fun k => if k < x + 1 then .bound k else if k = x + 1 then f else .bound (k - 1)) f uf := by
    refine ⟨fun k => rfl, b, hb', by rw [er]; exact filled, by rw [er]; exact al, fun q => ?_⟩
    rw [er]
    rcases au with n | r
    · exact absurd q n
    · exact r
  have B : Budget (Ψ.insertIdx x b) (x + 1) uf (u.insertIdx x 0) := by
    intro j c hc
    rw [er] at hc
    rw [image_insert (by omega) j]
    exact spliceSafe_at safe hc
  obtain ⟨u', h, le⟩ := subst_typed w (x + 1) _ f uf S B
  have lin := lin_eq w h S.sub
  have sf := safe_of_budget B (source_uses_length h) le
  rw [splice_rename, er] at h
  rw [er] at sf lin
  refine ⟨u', h, sf, fun j => ?_, fun j l => ?_⟩
  · rw [← image_insert (by omega) j]; exact le j
  · rw [← image_insert (by omega) j]; exact lin j l

/-- **T7 `contextual_msubst_uses`** over held code. A template `c : Code Ψ A θ` and a filling of
hypothesis `x` that is code in the same hypotheses (`Code Ψ Ψ[x].type θ`, open) splice to code at
`A` in `Ψ` whose uses are the composition `u[x ↦ 0] + u[x] · uf`: at most that everywhere, exactly
that at every `linear` hypothesis; provided the filling may stand where `x` stood
(`spliceAllowed`) and the composition is within every quantity (`spliceSafe`). -/
public theorem contextual_msubst_uses {Ψ : Context} {A : Ty} {θ : Assumptions} {x : Nat} {b : Binding}
    (c : Obend.Core.Code.Code Ψ A θ) (hx : Ψ[x]? = some b) (f : Obend.Core.Code.Code Ψ b.type θ)
    (allowed : spliceAllowed θ b.quantity Ψ (occurrences Ψ.length f.val.term) = true)
    (safe : spliceSafe Ψ (occurrences Ψ.length c.val.term) x (occurrences Ψ.length f.val.term) = true) :
    ∃ s : Obend.Core.Code.Code Ψ A θ, s.val.term = splice x c.val.term f.val.term ∧
      (∀ j, (occurrences Ψ.length s.val.term).getD j 0 ≤
        spliceUses (occurrences Ψ.length c.val.term) x (occurrences Ψ.length f.val.term) j) ∧
      (∀ j, LinearAt Ψ j → (occurrences Ψ.length s.val.term).getD j 0 =
        spliceUses (occurrences Ψ.length c.val.term) x (occurrences Ψ.length f.val.term) j) := by
  obtain ⟨cv, cθ, k, kA⟩ := c
  obtain ⟨fv, fθ, kf, kfB⟩ := f
  subst cθ
  have dc := k.derivation
  rw [kA] at dc
  have df := kf.derivation
  rw [kfB, fθ] at df
  have uc := uses_determined dc
  have uf := uses_determined df
  simp only [AnnotatedTerm.erase] at dc df uc uf
  rw [← uc, ← uf] at safe ⊢
  rw [← uf] at allowed
  obtain ⟨u', h, sf, le, lin⟩ := splice_typed dc k.contextValid hx df allowed safe
  refine ⟨⟨⟨splice x cv.term fv.term, cv.annotations, cv.assumptions⟩, rfl,
    ⟨⟨A, u', h, sf, k.contextValid, k.assumptionsValid⟩, rfl⟩⟩, rfl, ?_, ?_⟩
  · intro j; rw [← uses_determined h]; exact le j
  · intro j l; rw [← uses_determined h]; exact lin j l

end Obend.Core.Proofs.Splice
