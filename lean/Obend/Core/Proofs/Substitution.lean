module
/-
# Obend.Core.Proofs.Substitution — filling hypotheses keeps a checked term checked

The substitution lemma of the contextual calculus (`Obend.Slot.Calculus`), stated of Core4's own
checker. A HOLE is a free de Bruijn hypothesis of an open term; a FILLING is a closed annotated
term; `msubst σ t` puts the fillings `σ` names in place of the hypotheses they name, in the term by
`Term.substitute` and in the annotations by `annotationsAt`, which walks the checker's positions
(`infer`'s numbering of children) and answers with a filling's own annotation below the position
where it lands. The lemma (`check_msubst`): if `t` checks in `Ψ` and every filling checks in `Ψ` at
exactly the type `Ψ` declares for its hypothesis, then `msubst σ t` checks in `Ψ` at `t`'s type,
with no more uses of any hypothesis than `t` had.

Three corners, each with a tooth below (`*_tooth`): fillings must be CLOSED (an open filling that
shares a linear hypothesis with its surroundings is refused after substitution), fillings check
under the TEMPLATE'S assumptions (`msubst` keeps `t.assumptions`; the slot judges a filling under
its own), and the FUEL adds (a term that checks at fuel `n` with fillings at fuel `m` checks at
`n + m`; at a fixed fuel the lemma holds only within the budget, by monotonicity).

The lemmas on the way are of independent use: `infer` is monotone in its fuel (`infer_mono`,
`check_mono`), a checked term is scoped by its context (`typed_scoped`), and a closed term checks
the same in any valid context, at any position, with zero uses (`infer_transport`).
-/
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.AxiomPin
public import Obend.Tactic.Cases
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

/-! ## Filling hypotheses -/

/-- The filling of hypothesis `x` at binder depth `depth`, if `σ` fills it: a `bound index` with
`depth ≤ index` is the hypothesis `index - depth`. -/
@[expose] public def fillingAt (σ : Nat → Option AnnotatedTerm) (depth index : Nat) : Option AnnotatedTerm :=
  if depth ≤ index then σ (index - depth) else none

/-- Walk `t` along a checker position (`infer`'s conventions: children numbered as the checker
numbers them, record fields by their index, `extend` fields under `1`, `case` arms under `1`,
binders counted). If the path passes through a filled hypothesis, the answer is the filling's own
annotation at the rest of the path; otherwise it is `ann` at the whole path. Structural on the
path, so the kernel evaluates it. -/
@[expose] public def annotationsAt (σ : Nat → Option AnnotatedTerm) (ann : Annotations) :
    Nat → List Nat → Term → List Nat → Option LambdaAnnotation
  | depth, path, .bound index, rest =>
      match fillingAt σ depth index with
      | some f => f.annotations rest
      | none => ann (path ++ rest)
  | depth, path, .lam body, 0 :: rest => annotationsAt σ ann (depth + 1) (path ++ [0]) body rest
  | depth, path, .app function _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) function rest
  | depth, path, .app _ argument, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) argument rest
  | depth, path, .mix lower _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) lower rest
  | depth, path, .mix _ upper, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) upper rest
  | depth, path, .fix spec _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .fix _ inherited, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) inherited rest
  | depth, path, .specification metadata _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) metadata rest
  | depth, path, .specification _ extension, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) extension rest
  | depth, path, .prototype spec _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .prototype _ target, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) target rest
  | depth, path, .reflect target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .metadata spec, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) spec rest
  | depth, path, .project target, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .binary _ left _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) left rest
  | depth, path, .binary _ _ right, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) right rest
  | depth, path, .extend inherited _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) inherited rest
  | depth, path, .extend _ fields, 1 :: k :: rest =>
      match fields[k]? with
      | some field => annotationsAt σ ann depth (path ++ [1, k]) field.2 rest
      | none => ann (path ++ 1 :: k :: rest)
  | depth, path, .record fields, k :: rest =>
      match fields[k]? with
      | some field => annotationsAt σ ann depth (path ++ [k]) field.2 rest
      | none => ann (path ++ k :: rest)
  | depth, path, .get target _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) target rest
  | depth, path, .ifZero value _ _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) value rest
  | depth, path, .ifZero _ zero _, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) zero rest
  | depth, path, .ifZero _ _ successorBody, 2 :: rest => annotationsAt σ ann (depth + 1) (path ++ [2]) successorBody rest
  | depth, path, .inject _ payload, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) payload rest
  | depth, path, .case scrutinee _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) scrutinee rest
  | depth, path, .case _ arms, 1 :: k :: rest =>
      match arms[k]? with
      | some arm => annotationsAt σ ann (depth + 1) (path ++ [1, k]) arm.2 rest
      | none => ann (path ++ 1 :: k :: rest)
  | depth, path, .ifBool condition _ _, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) condition rest
  | depth, path, .ifBool _ whenTrue _, 1 :: rest => annotationsAt σ ann depth (path ++ [1]) whenTrue rest
  | depth, path, .ifBool _ _ whenFalse, 2 :: rest => annotationsAt σ ann depth (path ++ [2]) whenFalse rest
  | depth, path, .perform plan, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) plan rest
  | depth, path, .done value, 0 :: rest => annotationsAt σ ann depth (path ++ [0]) value rest
  | _, path, _, rest => ann (path ++ rest)
termination_by structural _ _ _ rest => rest

/-- The term substitution `msubst` applies at binder depth `depth`: a filling's term where `σ`
fills, the hypothesis itself otherwise. Fillings are closed, so lifting under a binder changes
nothing (`liftSubstitution_fillTerm`). -/
@[expose] public def fillTerm (σ : Nat → Option AnnotatedTerm) (depth : Nat) (index : Nat) : Term :=
  match fillingAt σ depth index with
  | some f => f.term
  | none => .bound index

/-- Fill the hypotheses `σ` names in an annotated term: the term by `Term.substitute`, the
annotations by `annotationsAt`. Assumptions are the template's. -/
@[expose] public def msubst (σ : Nat → Option AnnotatedTerm) (t : AnnotatedTerm) : AnnotatedTerm where
  term := t.term.substitute (fillTerm σ 0)
  annotations := annotationsAt σ t.annotations 0 [] t.term
  assumptions := t.assumptions

public theorem fillTerm_zero (σ : Nat → Option AnnotatedTerm) (index : Nat) :
    fillTerm σ 0 index = match σ index with | some f => f.term | none => .bound index := by
  simp [fillTerm, fillingAt]

theorem fillingAt_succ (σ : Nat → Option AnnotatedTerm) (depth index : Nat) :
    fillingAt σ (depth + 1) (index + 1) = fillingAt σ depth index := by
  simp only [fillingAt, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

theorem fillingAt_succ_zero (σ : Nat → Option AnnotatedTerm) (depth : Nat) :
    fillingAt σ (depth + 1) 0 = none := by
  simp [fillingAt]

/-- Under a binder the term substitution is the same substitution one deeper: the fillings are
closed, so renaming them is the identity. -/
theorem liftSubstitution_fillTerm (σ : Nat → Option AnnotatedTerm)
    (closed : ∀ x f, σ x = some f → Scoped 0 f.term) (depth : Nat) :
    liftSubstitution (fillTerm σ depth) = fillTerm σ (depth + 1) := by
  funext index
  cases index with
  | zero => simp [liftSubstitution, fillTerm, fillingAt_succ_zero]
  | succ index =>
    simp only [liftSubstitution, fillTerm, fillingAt_succ]
    cases h : fillingAt σ depth index with
    | none => simp [Term.rename]
    | some f =>
      have hf : Scoped 0 f.term := by
        unfold fillingAt at h
        split at h
        · exact closed _ _ h
        · cases h
      exact scoped_rename_identity hf Nat.succ (fun i hi => absurd hi (Nat.not_lt_zero i))

/-! ## Use vectors: pointwise order, and the split over an appended context -/

/-- Pointwise `≤` on use vectors of one length. -/
public inductive UsesLE : Uses → Uses → Prop
  | nil : UsesLE [] []
  | cons {a b : Nat} {u v : Uses} : a ≤ b → UsesLE u v → UsesLE (a :: u) (b :: v)

theorem UsesLE.length {u v : Uses} (h : UsesLE u v) : u.length = v.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem UsesLE.refl : ∀ u : Uses, UsesLE u u
  | [] => .nil
  | _ :: u => .cons (Nat.le_refl _) (UsesLE.refl u)

theorem UsesLE.zero : ∀ u : Uses, UsesLE (List.replicate u.length 0) u
  | [] => .nil
  | _ :: u => .cons (Nat.zero_le _) (UsesLE.zero u)

theorem UsesLE.tail {u v : Uses} (h : UsesLE u v) : UsesLE u.tail v.tail := by
  cases h with
  | nil => exact .nil
  | cons _ h => exact h

theorem UsesLE.add {a a' b b' : Uses} (ha : UsesLE a a') (hb : UsesLE b b') :
    UsesLE (addUses a b) (addUses a' b') := by
  induction ha generalizing b b' with
  | nil => cases hb <;> exact .nil
  | cons h _ ih =>
    cases hb with
    | nil => exact .nil
    | cons h' hb => exact .cons (Nat.add_le_add h h') (ih hb)

theorem zipAll_of_le {P : Binding × Nat → Bool}
    (hP : ∀ b m n, n ≤ m → P (b, m) = true → P (b, n) = true) {u v : Uses} (h : UsesLE u v) :
    ∀ Γ : Context, (Γ.zip v).all P = true → (Γ.zip u).all P = true := by
  induction h with
  | nil => intro Γ _; cases Γ <;> rfl
  | cons hab _ ih =>
    intro Γ hall
    cases Γ with
    | nil => rfl
    | cons b Γ =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨hP _ _ _ hab hall.1, ih Γ hall.2⟩

theorem safeQuantity_anti (q : Quantity) {m n : Nat} (h : n ≤ m) (hm : safeQuantity q m = true) :
    safeQuantity q n = true := by
  cases q <;> simp [safeQuantity] at hm ⊢ <;> omega

theorem safeUses_of_le {Γ : Context} {u v : Uses} (h : UsesLE u v) (hv : safeUses Γ v = true) :
    safeUses Γ u = true := by
  simp only [safeUses, Bool.and_eq_true, beq_iff_eq] at hv ⊢
  exact ⟨h.length.trans hv.1, zipAll_of_le (fun b m n hnm hm => safeQuantity_anti b.quantity hnm hm) h Γ hv.2⟩

theorem reusableCaptures_of_le {variables : List Nat} {Γ : Context} {u v : Uses} (h : UsesLE u v)
    (hv : reusableCaptures variables Γ v = true) : reusableCaptures variables Γ u = true := by
  simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq] at hv ⊢
  refine ⟨h.length.trans hv.1, zipAll_of_le ?_ h Γ hv.2⟩
  intro b m n hnm hm
  simp only [Bool.or_eq_true, beq_iff_eq] at hm ⊢
  rcases hm with hm | hm
  · exact .inl (by omega)
  · exact .inr hm

theorem reusableAllowed_of_le {asm : Assumptions} {reuse : Reuse} {Γ : Context} {u v : Uses}
    (h : UsesLE u v) (hv : reusableAllowed asm reuse Γ v = true) : reusableAllowed asm reuse Γ u = true := by
  simp only [reusableAllowed, Bool.or_eq_true] at hv ⊢
  rcases hv with hv | hv
  · exact .inl hv
  · exact .inr (reusableCaptures_of_le h hv)

theorem argumentAllowed_of_le {asm : Assumptions} {quantity : Quantity} {Γ : Context} {type : Ty}
    {u v : Uses} (h : UsesLE u v) (hv : argumentAllowed asm quantity Γ type v = true) :
    argumentAllowed asm quantity Γ type u = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rcases hv.2 with hq | ⟨hs, hc⟩
  · exact .inl hq
  · exact .inr ⟨hs, reusableCaptures_of_le h hc⟩

theorem length_zeroUses (Γ : Context) : (zeroUses Γ).length = Γ.length := by simp [zeroUses]

theorem length_variableUses (Γ : Context) (i : Nat) : (variableUses Γ i).length = Γ.length := by
  simp [variableUses]

theorem length_addUses {a b : Uses} (h : a.length = b.length) : (addUses a b).length = a.length := by
  simp [addUses, List.length_zipWith, h]

theorem zeroUses_append (Δ Ψ : Context) : zeroUses (Δ ++ Ψ) = zeroUses Δ ++ zeroUses Ψ := by
  simp [zeroUses, List.replicate_append_replicate]

theorem variableUses_append_left {Δ : Context} (Ψ : Context) {i : Nat} (h : i < Δ.length) :
    variableUses (Δ ++ Ψ) i = variableUses Δ i ++ zeroUses Ψ := by
  simp only [variableUses, zeroUses, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.eq_replicate_iff.mpr ⟨by simp, fun x hx => ?_⟩
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  simp only [Function.comp]
  rw [if_neg]
  omega

theorem addUses_append {a b z z' : Uses} (h : a.length = b.length) :
    addUses (a ++ z) (b ++ z') = addUses a b ++ addUses z z' := List.zipWith_append h

theorem addUses_zeroUses (Ψ : Context) : addUses (zeroUses Ψ) (zeroUses Ψ) = zeroUses Ψ := by
  simp [addUses, zeroUses]

theorem zipAll_zero {P : Binding × Nat → Bool} (hP : ∀ b, P (b, 0) = true) :
    ∀ Ψ : Context, (Ψ.zip (zeroUses Ψ)).all P = true
  | [] => rfl
  | b :: Ψ => by
    simp only [zeroUses, List.length_cons, List.replicate_succ, List.zip_cons_cons, List.all_cons, hP,
      Bool.true_and]
    exact zipAll_zero hP Ψ

theorem zipAll_append_zero {P : Binding × Nat → Bool} (hP : ∀ b, P (b, 0) = true) (Δ Ψ Ψ' : Context)
    {a : Uses} (ha : a.length = Δ.length) :
    ((Δ ++ Ψ').zip (a ++ zeroUses Ψ')).all P = ((Δ ++ Ψ).zip (a ++ zeroUses Ψ)).all P := by
  rw [List.zip_append ha.symm, List.zip_append ha.symm, List.all_append, List.all_append,
    zipAll_zero hP, zipAll_zero hP]

theorem safeUses_append_zero {Δ Ψ Ψ' : Context} {a : Uses} (ha : a.length = Δ.length)
    (h : safeUses (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) : safeUses (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  simp only [safeUses, Bool.and_eq_true, beq_iff_eq, List.length_append, length_zeroUses] at h ⊢
  refine ⟨by omega, ?_⟩
  rw [zipAll_append_zero (fun b => by cases b.quantity <;> rfl) Δ Ψ Ψ' ha]
  exact h.2

theorem reusableCaptures_append_zero {variables : List Nat} {Δ Ψ Ψ' : Context} {a : Uses}
    (ha : a.length = Δ.length) (h : reusableCaptures variables (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) :
    reusableCaptures variables (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  simp only [reusableCaptures, Bool.and_eq_true, beq_iff_eq, List.length_append, length_zeroUses] at h ⊢
  refine ⟨by omega, ?_⟩
  rw [zipAll_append_zero (fun b => by simp) Δ Ψ Ψ' ha]
  exact h.2

theorem validContext_append (variables : List Nat) (Δ Ψ : Context) :
    validContext variables (Δ ++ Ψ) = (validContext variables Δ && validContext variables Ψ) := by
  simp [validContext, List.all_append]

theorem reusableAllowed_append_zero {asm : Assumptions} {reuse : Reuse} {Δ Ψ Ψ' : Context} {a : Uses}
    (ha : a.length = Δ.length) (h : reusableAllowed asm reuse (Δ ++ Ψ) (a ++ zeroUses Ψ) = true) :
    reusableAllowed asm reuse (Δ ++ Ψ') (a ++ zeroUses Ψ') = true := by
  simp only [reusableAllowed, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr (reusableCaptures_append_zero ha h)

theorem argumentAllowed_append_zero {asm : Assumptions} {quantity : Quantity} {type : Ty}
    {Δ Ψ Ψ' : Context} {a : Uses} (ha : a.length = Δ.length)
    (h : argumentAllowed asm quantity (Δ ++ Ψ) type (a ++ zeroUses Ψ) = true) :
    argumentAllowed asm quantity (Δ ++ Ψ') type (a ++ zeroUses Ψ') = true := by
  simp only [argumentAllowed, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with hq | ⟨hs, hc⟩
  · exact .inl hq
  · exact .inr ⟨hs, reusableCaptures_append_zero ha hc⟩

/-! ## A checked term is scoped by its context -/

/-- Every hypothesis a typed term mentions is bound by its context. -/
public theorem typed_scoped {asm : Assumptions} {context : Context} {term : Term} {type : Ty} {uses : Uses}
    (typed : PartialTyping asm context term type uses) : Scoped context.length term := by
  refine PartialTyping.rec
    (motive_1 := fun context term _ _ _ => Scoped context.length term)
    (motive_2 := fun context fields _ _ _ => ∀ f ∈ fields, Scoped context.length f.2)
    (motive_3 := fun context arms _ _ _ _ => ∀ arm ∈ arms, Scoped (context.length + 1) arm.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intros; rename_i found; exact .bound (List.getElem?_eq_some_iff.mp found).1
  · intros; exact .natural _
  · intros; exact .boolean _
  · intros; exact .label _
  · intros; rename_i ih; exact .lam ih
  · intros; assumption
  · intros; rename_i ih₁ ih₂; exact .app ih₁ ih₂
  · intros; rename_i ih; exact .record ih
  · intros; rename_i ih; exact .get ih
  · intros; rename_i ih₁ ih₂; exact .extend ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .specification ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .prototype ih₁ ih₂
  · intros; rename_i ih; exact .reflect ih
  · intros; rename_i ih; exact .metadata ih
  · intros; rename_i ih; exact .project ih
  · intros; rename_i ih₁ ih₂; exact .mix ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .fix ih₁ ih₂
  · intros; rename_i ih₁ ih₂; exact .binary ih₁ ih₂
  · intros; rename_i ih₁ ih₂ ih₃; exact .condition ih₁ ih₂ ih₃
  · intros; rename_i ih; exact .inject ih
  · intros; rename_i ih₁ ih₂; exact .case ih₁ ih₂
  · intros; rename_i ih₁ ih₂ ih₃; exact .ifBool ih₁ ih₂ ih₃
  · intros; rename_i ih; exact .perform ih
  · intros; rename_i ih; exact .done ih
  · intros; rename_i ih₁ ih₂; exact .case ih₁ ih₂
  · intros; simp
  · intros; rename_i ih₁ ih₂
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ih₁
    · exact ih₂ f hf
  · intros; simp
  · intros; rename_i ih₁ ih₂
    intro arm harm
    rcases List.mem_cons.mp harm with rfl | harm
    · exact ih₁
    · exact ih₂ arm harm

/-! ## Transport: a scoped term checks the same in any valid extension of its context, at any
position, with more fuel -/

theorem shift_child {ann ann' : Annotations} {pos pos' : List Nat}
    (h : ∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) (k : Nat) :
    ∀ rest, ann' ((pos' ++ [k]) ++ rest) = ann ((pos ++ [k]) ++ rest) := by
  intro rest; simpa [List.append_assoc] using h (k :: rest)

theorem shift_here {ann ann' : Annotations} {pos pos' : List Nat}
    (h : ∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) : ann' pos' = ann pos := by
  simpa using h []

theorem split_add {a₁ a₂ : Uses} (Ψ : Context) (h : a₁.length = a₂.length) :
    addUses (a₁ ++ zeroUses Ψ) (a₂ ++ zeroUses Ψ) = addUses a₁ a₂ ++ zeroUses Ψ := by
  rw [addUses_append h, addUses_zeroUses]

theorem split_tail {a : Uses} (Ψ : Context) (h : a ≠ []) :
    (a ++ zeroUses Ψ).tail = a.tail ++ zeroUses Ψ :=
  List.tail_append_of_ne_nil h

theorem ne_nil_of_length_succ {a : Uses} {n : Nat} (h : a.length = n + 1) : a ≠ [] := by
  intro e; subst e; simp at h

/-- A term scoped under `Δ` and checked in `Δ ++ Ψ` uses nothing of `Ψ`, and checks in `Δ ++ Ψ'`
for every valid `Ψ'`, at any position whose annotations agree below it, with any more fuel, at the
same type and with the same uses of `Δ`. By induction on fuel, mirroring `infer`, `inferFields`,
`inferArms`. -/
theorem infer_transport (asm : Assumptions) (Ψ Ψ' : Context)
    (valid' : validContext asm.shareableVariables Ψ' = true) (extra : Nat) : ∀ fuel : Nat,
    (∀ (ann ann' : Annotations) (Δ : Context) (pos pos' : List Nat) (term : Term)
        (result : Inferred asm (Δ ++ Ψ) term),
      Scoped Δ.length term →
      infer asm ann (Δ ++ Ψ) pos fuel term = some result →
      (∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) →
      ∃ a : Uses, a.length = Δ.length ∧ result.uses = a ++ zeroUses Ψ ∧
        ∃ result' : Inferred asm (Δ ++ Ψ') term,
          infer asm ann' (Δ ++ Ψ') pos' (fuel + extra) term = some result' ∧
          result'.type = result.type ∧ result'.uses = a ++ zeroUses Ψ') ∧
    (∀ (ann ann' : Annotations) (Δ : Context) (pos pos' : List Nat) (index : Nat)
        (fields : List (String × Term)) (result : InferredFields asm (Δ ++ Ψ) fields),
      (∀ f ∈ fields, Scoped Δ.length f.2) →
      inferFields asm ann (Δ ++ Ψ) pos index fuel fields = some result →
      (∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) →
      ∃ a : Uses, a.length = Δ.length ∧ result.uses = a ++ zeroUses Ψ ∧
        ∃ result' : InferredFields asm (Δ ++ Ψ') fields,
          inferFields asm ann' (Δ ++ Ψ') pos' index (fuel + extra) fields = some result' ∧
          result'.type = result.type ∧ result'.uses = a ++ zeroUses Ψ') ∧
    (∀ (ann ann' : Annotations) (Δ : Context) (pos pos' : List Nat) (index : Nat) (row : Ty)
        (expected : Option Ty) (arms : List (String × Term)) (result : InferredArms asm (Δ ++ Ψ) arms),
      (∀ arm ∈ arms, Scoped (Δ.length + 1) arm.2) →
      inferArms asm ann (Δ ++ Ψ) pos index row expected fuel arms = some result →
      (∀ rest, ann' (pos' ++ rest) = ann (pos ++ rest)) →
      ∃ a : Uses, a.length = Δ.length ∧ result.uses = a ++ zeroUses Ψ ∧
        ∃ result' : InferredArms asm (Δ ++ Ψ') arms,
          inferArms asm ann' (Δ ++ Ψ') pos' index row expected (fuel + extra) arms = some result' ∧
          result'.row = result.row ∧ result'.result = result.result ∧ result'.uses = a ++ zeroUses Ψ')
  | 0 => ⟨fun _ _ _ _ _ _ _ _ h => by simp [infer] at h, fun _ _ _ _ _ _ _ _ _ h => by simp [inferFields] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [inferArms] at h⟩
  | fuel + 1 => by
    obtain ⟨ih, ihFields, ihArms⟩ := infer_transport asm Ψ Ψ' valid' extra fuel
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    refine ⟨?_, ?_, ?_⟩
    · intro ann ann' Δ pos pos' term result hs h hann
      cases term with
      | hole _ _ => obend_cases fuel with [infer]
      | bound index =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨binding, found, h⟩ := h
        rw [dif_pos found] at h
        cases h
        have hi : index < Δ.length := (scoped_bound_iff _ _).1 hs
        have foundΔ : Δ[index]? = some binding := by
          rw [← List.getElem?_append_left (l₂ := Ψ) hi]; exact found
        have found' : (Δ ++ Ψ')[index]? = some binding := by rw [List.getElem?_append_left hi]; exact foundΔ
        simp only [infer, Option.bind_eq_bind, found', Option.bind_some]
        exact ⟨variableUses Δ index, length_variableUses Δ index, variableUses_append_left Ψ hi, _, rfl, rfl,
          variableUses_append_left Ψ' hi⟩
      | nat value =>
        simp only [infer] at h; cases h
        exact ⟨zeroUses Δ, length_zeroUses Δ, zeroUses_append Δ Ψ, _, rfl, rfl, zeroUses_append Δ Ψ'⟩
      | boolean value =>
        simp only [infer] at h; cases h
        exact ⟨zeroUses Δ, length_zeroUses Δ, zeroUses_append Δ Ψ, _, rfl, rfl, zeroUses_append Δ Ψ'⟩
      | label value =>
        simp only [infer] at h; cases h
        exact ⟨zeroUses Δ, length_zeroUses Δ, zeroUses_append Δ Ψ, _, rfl, rfl, zeroUses_append Δ Ψ'⟩
      | lam body =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i safe
        split at h
        rotate_left; · cases h
        rename_i valid
        split at h
        rotate_left; · cases h
        rename_i captures
        cases h
        have hsb : Scoped (⟨annotation.domain, annotation.parameter⟩ :: Δ).length body := (scoped_lam_iff _ _).1 hs
        obtain ⟨a, ha, innerUses, inner₀, innerTyped₀, innerType₀, innerUses₀⟩ :=
          ih ann ann' (⟨annotation.domain, annotation.parameter⟩ :: Δ) _ _ body inner hsb innerTyped (shift_child hann 0)
        obtain ⟨inner', innerTyped', innerType, innerUses'⟩ :
            ∃ inner' : Inferred asm (⟨annotation.domain, annotation.parameter⟩ :: (Δ ++ Ψ')) body,
              infer asm ann' (⟨annotation.domain, annotation.parameter⟩ :: (Δ ++ Ψ')) (pos' ++ [0]) (fuel + extra) body =
                some inner' ∧ inner'.type = inner.type ∧ inner'.uses = a ++ zeroUses Ψ' :=
          ⟨inner₀, innerTyped₀, innerType₀, innerUses₀⟩
        have hne : a ≠ [] := ne_nil_of_length_succ ha
        have found' : ann' pos' = some annotation := by rw [shift_here hann]; exact found
        simp only [infer, Option.bind_eq_bind, found', Option.bind_some]
        rw [innerTyped', Option.bind_some]
        have a1 : agree asm inner'.type annotation.codomain = true := by rw [innerType]; exact agreed
        have a2 : safeUses (⟨annotation.domain, annotation.parameter⟩ :: (Δ ++ Ψ')) inner'.uses = true := by
          rw [innerUses']
          exact safeUses_append_zero (Δ := ⟨annotation.domain, annotation.parameter⟩ :: Δ) ha
            (by rw [← innerUses]; exact safe)
        have a3 : validContext asm.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: (Δ ++ Ψ')) = true := by
          have := valid
          rw [← List.cons_append, validContext_append, Bool.and_eq_true] at this ⊢
          exact ⟨this.1, valid'⟩
        have a4 : reusableAllowed asm annotation.reuse (Δ ++ Ψ') inner'.uses.tail = true := by
          rw [innerUses', split_tail Ψ' hne]
          exact reusableAllowed_append_zero (Ψ := Ψ) (by simp [ha])
            (by rw [← split_tail Ψ hne, ← innerUses]; exact captures)
        rw [dif_pos a1, dif_pos a2, dif_pos a3, dif_pos a4]
        refine ⟨a.tail, by simp [ha], ?_, _, rfl, rfl, ?_⟩
        · show inner.uses.tail = _; rw [innerUses, split_tail Ψ hne]
        · show inner'.uses.tail = _; rw [innerUses', split_tail Ψ' hne]
      | app function argument =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨fn, fnTyped, arg, argTyped, h⟩ := h
        obtain ⟨hsf, hsa⟩ := (scoped_app_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, fnUses, fn', fnTyped', fnType, fnUses'⟩ :=
          ih ann ann' Δ _ _ function fn hsf fnTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, argUses, arg', argTyped', argType, argUses'⟩ :=
          ih ann ann' Δ _ _ argument arg hsa argTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        simp only [infer, Option.bind_eq_bind, fnTyped', argTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i reuse quantity domain codomain shape
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i allowed
        cases h
        have shape' : callable fn'.type = .arrow reuse quantity domain codomain := by rw [fnType]; exact shape
        split
        · rename_i reuse' quantity' domain' codomain' shape''
          rw [shape'] at shape''
          cases shape''
          have a1 : agree asm arg'.type domain = true := by rw [argType]; exact agreed
          have a2 : argumentAllowed asm quantity (Δ ++ Ψ') domain arg'.uses = true := by
            rw [argUses']; exact argumentAllowed_append_zero ha₂ (by rw [← argUses]; exact allowed)
          rw [dif_pos a1, dif_pos a2]
          refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, rfl, ?_⟩
          · show addUses fn.uses arg.uses = _; rw [fnUses, argUses, split_add Ψ hl]
          · show addUses fn'.uses arg'.uses = _; rw [fnUses', argUses', split_add Ψ' hl]
        · rename_i other
          exact (other _ _ _ _ shape').elim
      | record fields =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨members, membersTyped, h⟩ := h
        cases h
        obtain ⟨a, ha, membersUses, members', membersTyped', membersType, membersUses'⟩ :=
          ihFields ann ann' Δ pos pos' 0 fields members ((scoped_record_iff _ _).1 hs) membersTyped hann
        simp only [infer, Option.bind_eq_bind, membersTyped', Option.bind_some]
        exact ⟨a, ha, membersUses, _, rfl, by exact membersType, membersUses'⟩
      | get target name =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, member, found, h⟩ := h
        rw [dif_pos found] at h
        cases h
        obtain ⟨a, ha, priorUses, prior', priorTyped', priorType, priorUses'⟩ :=
          ih ann ann' Δ _ _ target prior ((scoped_get_iff _ _ _).1 hs) priorTyped (shift_child hann 0)
        have found' : prior'.type.lookup asm.bounds (fuel + extra + 1) name = some member := by
          rw [priorType]; exact Ty.lookup_mono found (by omega)
        simp only [infer, Option.bind_eq_bind, priorTyped', Option.bind_some, found']
        exact ⟨a, ha, priorUses, _, rfl, rfl, priorUses'⟩
      | extend target fields =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, members, membersTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i isRow
        cases h
        obtain ⟨hst, hsf⟩ := (scoped_extend_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, priorUses, prior', priorTyped', priorType, priorUses'⟩ :=
          ih ann ann' Δ _ _ target prior hst priorTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, membersUses, members', membersTyped', membersType, membersUses'⟩ :=
          ihFields ann ann' Δ _ _ 0 fields members hsf membersTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have isRow' : prior'.type.isRow asm.bounds (fuel + extra + 64) = true := by
          rw [priorType]; exact Ty.isRow_mono isRow (by omega)
        simp only [infer, Option.bind_eq_bind, priorTyped', membersTyped', Option.bind_some, dif_pos isRow']
        refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, ?_, ?_⟩
        · show addUses prior.uses members.uses = _; rw [priorUses, membersUses, split_add Ψ hl]
        · show overlay members'.type prior'.type = overlay members.type prior.type; rw [membersType, priorType]
        · show addUses prior'.uses members'.uses = _; rw [priorUses', membersUses', split_add Ψ' hl]
      | specification metadata extension =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨descriptor, descriptorTyped, body, bodyTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureDescriptor
        split at h
        rotate_left; · cases h
        rename_i pureBody
        cases h
        obtain ⟨hs₁, hs₂⟩ := (scoped_specification_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, dUses, d', dTyped', dType, dUses'⟩ :=
          ih ann ann' Δ _ _ metadata descriptor hs₁ descriptorTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, bUses, b', bTyped', bType, bUses'⟩ :=
          ih ann ann' Δ _ _ extension body hs₂ bodyTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have p1 : d'.type.isComputation = false := by rw [dType]; exact pureDescriptor
        have p2 : b'.type.isComputation = false := by rw [bType]; exact pureBody
        simp only [infer, Option.bind_eq_bind, dTyped', bTyped', Option.bind_some, dif_pos p1, dif_pos p2]
        refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, ?_, ?_⟩
        · show addUses descriptor.uses body.uses = _; rw [dUses, bUses, split_add Ψ hl]
        · show Ty.specification d'.type b'.type = Ty.specification descriptor.type body.type; rw [dType, bType]
        · show addUses d'.uses b'.uses = _; rw [dUses', bUses', split_add Ψ' hl]
      | prototype spec target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨code, codeTyped, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureCode
        split at h
        rotate_left; · cases h
        rename_i pureValue
        cases h
        obtain ⟨hs₁, hs₂⟩ := (scoped_prototype_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, cUses, c', cTyped', cType, cUses'⟩ :=
          ih ann ann' Δ _ _ spec code hs₁ codeTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, vUses, v', vTyped', vType, vUses'⟩ :=
          ih ann ann' Δ _ _ target value hs₂ valueTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have p1 : c'.type.isComputation = false := by rw [cType]; exact pureCode
        have p2 : v'.type.isComputation = false := by rw [vType]; exact pureValue
        simp only [infer, Option.bind_eq_bind, cTyped', vTyped', Option.bind_some, dif_pos p1, dif_pos p2]
        refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, ?_, ?_⟩
        · show addUses code.uses value.uses = _; rw [cUses, vUses, split_add Ψ hl]
        · show Ty.prototype c'.type v'.type = Ty.prototype code.type value.type; rw [cType, vType]
        · show addUses c'.uses v'.uses = _; rw [cUses', vUses', split_add Ψ' hl]
      | reflect target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        cases h
        obtain ⟨a, ha, innerUses, inner', innerTyped', innerType, innerUses'⟩ :=
          ih ann ann' Δ _ _ target inner ((scoped_reflect_iff _ _).1 hs) innerTyped (shift_child hann 0)
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          exact ⟨a, ha, innerUses, _, rfl, rfl, innerUses'⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | metadata target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i metadataType extensionType shape
        cases h
        obtain ⟨a, ha, innerUses, inner', innerTyped', innerType, innerUses'⟩ :=
          ih ann ann' Δ _ _ target inner ((scoped_metadata_iff _ _).1 hs) innerTyped (shift_child hann 0)
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i m' e' shape'
          rw [innerType] at shape'
          cases shape'
          exact ⟨a, ha, innerUses, _, rfl, rfl, innerUses'⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | project target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        cases h
        obtain ⟨a, ha, innerUses, inner', innerTyped', innerType, innerUses'⟩ :=
          ih ann ann' Δ _ _ target inner ((scoped_project_iff _ _).1 hs) innerTyped (shift_child hann 0)
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          exact ⟨a, ha, innerUses, _, rfl, rfl, innerUses'⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | mix lower upper =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, second, secondTyped, h⟩ := h
        obtain ⟨hs₁, hs₂⟩ := (scoped_mix_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, firstUses, first', firstTyped', firstType, firstUses'⟩ :=
          ih ann ann' Δ _ _ lower first hs₁ firstTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, secondUses, second', secondTyped', secondType, secondUses'⟩ :=
          ih ann ann' Δ _ _ upper second hs₂ secondTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        simp only [infer, Option.bind_eq_bind, firstTyped', secondTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i self inherited middle self₂ middle₂ provided shapeFirst shapeSecond
        split at h
        rotate_left; · cases h
        rename_i sameSelf
        split at h
        rotate_left; · cases h
        rename_i sameMiddle
        split at h
        rotate_left; · cases h
        rename_i captures
        split at h
        rotate_left; · cases h
        rename_i shareSelf
        split at h
        rotate_left; · cases h
        rename_i shareInherited
        split at h
        rotate_left; · cases h
        rename_i shareMiddle
        cases h
        subst sameSelf sameMiddle
        have s1 : callable first'.type = callable first.type := by rw [firstType]
        have s2 : callable second'.type = callable second.type := by rw [secondType]
        rw [shapeFirst] at s1
        rw [shapeSecond] at s2
        split
        · rename_i a b c a' c' d t1 t2
          rw [s1] at t1
          rw [s2] at t2
          cases t1
          cases t2
          have c1 : reusableCaptures asm.shareableVariables (Δ ++ Ψ') (addUses first'.uses second'.uses) = true := by
            rw [firstUses', secondUses', split_add Ψ' hl]
            exact reusableCaptures_append_zero (Ψ := Ψ) (by rw [length_addUses hl, ha₁])
              (by rw [← split_add Ψ hl, ← firstUses, ← secondUses]; exact captures)
          rw [dif_pos rfl, dif_pos rfl, dif_pos c1, dif_pos shareSelf, dif_pos shareInherited, dif_pos shareMiddle]
          refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, rfl, ?_⟩
          · show addUses first.uses second.uses = _; rw [firstUses, secondUses, split_add Ψ hl]
          · show addUses first'.uses second'.uses = _; rw [firstUses', secondUses', split_add Ψ' hl]
        · rename_i other
          exact (other _ _ _ _ _ _ s1 s2).elim
      | fix spec inheritedTerm =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨code, codeTyped, base, baseTyped, h⟩ := h
        obtain ⟨hs₁, hs₂⟩ := (scoped_fix_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, codeUses, code', codeTyped', codeType, codeUses'⟩ :=
          ih ann ann' Δ _ _ spec code hs₁ codeTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, baseUses, base', baseTyped', baseType, baseUses'⟩ :=
          ih ann ann' Δ _ _ inheritedTerm base hs₂ baseTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        simp only [infer, Option.bind_eq_bind, codeTyped', baseTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i target inherited output shape
        split at h
        rotate_left; · cases h
        rename_i sameOutput
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i shareTarget
        split at h
        rotate_left; · cases h
        rename_i allowed
        split at h
        rotate_left; · cases h
        rename_i captures
        cases h
        subst sameOutput
        have s1 : callable code'.type = callable code.type := by rw [codeType]
        rw [shape] at s1
        split
        · rename_i a b c t1
          rw [s1] at t1
          cases t1
          rw [dif_pos rfl, dif_pos (by rw [baseType]; exact agreed), dif_pos shareTarget,
            dif_pos (by rw [baseUses']; exact argumentAllowed_append_zero ha₂ (by rw [← baseUses]; exact allowed)),
            dif_pos (by rw [codeUses']; exact reusableCaptures_append_zero ha₁ (by rw [← codeUses]; exact captures))]
          refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, rfl, ?_⟩
          · show addUses code.uses base.uses = _; rw [codeUses, baseUses, split_add Ψ hl]
          · show addUses code'.uses base'.uses = _; rw [codeUses', baseUses', split_add Ψ' hl]
        · rename_i other
          exact (other _ _ _ s1).elim
      | binary primitive left right =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨l, lTyped, rr, rTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i lShape
        split at h
        rotate_left; · cases h
        rename_i rShape
        cases h
        obtain ⟨hs₁, hs₂⟩ := (scoped_binary_iff _ _ _ _).1 hs
        obtain ⟨a₁, ha₁, lUses, l', lTyped', lType, lUses'⟩ :=
          ih ann ann' Δ _ _ left l hs₁ lTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, rUses, r', rTyped', rType, rUses'⟩ :=
          ih ann ann' Δ _ _ right rr hs₂ rTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have l1 : l'.type = (primitiveTypes primitive).1 := by rw [lType, lShape]
        have r1 : r'.type = (primitiveTypes primitive).1 := by rw [rType, rShape]
        simp only [infer, Option.bind_eq_bind, lTyped', rTyped', Option.bind_some, dif_pos l1, dif_pos r1]
        refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, rfl, ?_⟩
        · show addUses l.uses rr.uses = _; rw [lUses, rUses, split_add Ψ hl]
        · show addUses l'.uses r'.uses = _; rw [lUses', rUses', split_add Ψ' hl]
      | ifZero value zero successor =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨c, cTyped, z, zTyped, s, sTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i cShape
        split at h
        rotate_left; · cases h
        rename_i same
        split at h
        rotate_left; · cases h
        rename_i safe
        cases h
        obtain ⟨hs₁, hs₂, hs₃⟩ := (scoped_condition_iff _ _ _ _).1 hs
        obtain ⟨a₁, ha₁, cUses, c', cTyped', cType, cUses'⟩ :=
          ih ann ann' Δ _ _ value c hs₁ cTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, zUses, z', zTyped', zType, zUses'⟩ :=
          ih ann ann' Δ _ _ zero z hs₂ zTyped (shift_child hann 1)
        obtain ⟨a₃, ha₃, sUses, s₀, sTyped₀, sType₀, sUses₀⟩ :=
          ih ann ann' (⟨.natural, .unrestricted⟩ :: Δ) _ _ successor s hs₃ sTyped (shift_child hann 2)
        obtain ⟨s', sTyped', sType, sUses'⟩ :
            ∃ s' : Inferred asm (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ')) successor,
              infer asm ann' (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ')) (pos' ++ [2]) (fuel + extra) successor =
                some s' ∧ s'.type = s.type ∧ s'.uses = a₃ ++ zeroUses Ψ' :=
          ⟨s₀, sTyped₀, sType₀, sUses₀⟩
        have hne : a₃ ≠ [] := ne_nil_of_length_succ ha₃
        have hl : a₂.length = a₃.tail.length := by simp [ha₂, ha₃]
        have hl' : a₁.length = (addUses a₂ a₃.tail).length := by rw [length_addUses hl, ha₂, ha₁]
        have c1 : c'.type = .natural := by rw [cType, cShape]
        have s1 : s'.type = z'.type := by rw [sType, zType, same]
        have u1 : safeUses (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ')) s'.uses = true := by
          rw [sUses']
          exact safeUses_append_zero (Δ := ⟨.natural, .unrestricted⟩ :: Δ) ha₃ (by rw [← sUses]; exact safe)
        simp only [infer, Option.bind_eq_bind, cTyped', zTyped', sTyped', Option.bind_some, dif_pos c1, dif_pos s1,
          dif_pos u1]
        refine ⟨addUses a₁ (addUses a₂ a₃.tail), by rw [length_addUses hl', ha₁], ?_, _, rfl, by exact zType, ?_⟩
        · show addUses c.uses (addUses z.uses s.uses.tail) = _
          rw [cUses, zUses, sUses, split_tail Ψ hne, split_add Ψ hl, split_add Ψ hl']
        · show addUses c'.uses (addUses z'.uses s'.uses.tail) = _
          rw [cUses', zUses', sUses', split_tail Ψ' hne, split_add Ψ' hl, split_add Ψ' hl']
      | inject tag payload =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        obtain ⟨a, ha, valueUses, value', valueTyped', valueType, valueUses'⟩ :=
          ih ann ann' Δ _ _ payload value ((scoped_inject_iff _ _ _).1 hs) valueTyped (shift_child hann 0)
        have found' : ann' pos' = some annotation := by rw [shift_here hann]; exact found
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i kind
        rw [dif_pos kind]
        split at h
        · rename_i row codomainShape
          split at h
          rotate_left; · cases h
          rename_i member
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pure
          cases h
          have m1 : row.lookup asm.bounds (fuel + extra + 1) tag = some annotation.domain :=
            Ty.lookup_mono member (by omega)
          have a1 : agree asm value'.type annotation.domain = true := by rw [valueType]; exact agreed
          rw [dif_pos m1, dif_pos a1, dif_pos pure]
          exact ⟨a, ha, valueUses, _, rfl, rfl, valueUses'⟩
        · rename_i index codomainShape
          split at h
          rotate_left; · cases h
          rename_i row aliased
          split at h
          rotate_left; · cases h
          rename_i member
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pure
          split at h
          rotate_left; · cases h
          rename_i conversion
          cases h
          have m1 : row.lookup asm.bounds (fuel + extra + 1) tag = some annotation.domain :=
            Ty.lookup_mono member (by omega)
          have a1 : agree asm value'.type annotation.domain = true := by rw [valueType]; exact agreed
          rw [dif_pos m1, dif_pos a1, dif_pos pure, dif_pos conversion]
          exact ⟨a, ha, valueUses, _, rfl, rfl, valueUses'⟩
        · cases h
      | case scrutinee arms =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨value, valueTyped, h⟩ := h
        obtain ⟨hs₁, hs₂⟩ := (scoped_case_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, valueUses, value', valueTyped', valueType, valueUses'⟩ :=
          ih ann ann' Δ _ _ scrutinee value hs₁ valueTyped (shift_child hann 0)
        simp only [infer, Option.bind_eq_bind, valueTyped', Option.bind_some]
        split at h
        · rename_i plan response produced activity
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨row, rowFound, typed, armsTyped, h⟩ := h
          split at h
          rotate_left; · cases h
          rename_i planType responseType armResult resultShape
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pureResult
          cases h
          obtain ⟨a₂, ha₂, typedUses, typed', armsTyped', typedRow, typedResult, typedUses'⟩ :=
            ihArms ann ann' Δ _ _ 0 row none arms typed hs₂ armsTyped (shift_child hann 1)
          have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
          have activity' : value'.type = .computation plan response produced := by rw [valueType, activity]
          split
          · rename_i p r pr activity''
            rw [activity'] at activity''
            cases activity''
            simp only [rowFound, Option.bind_some, armsTyped']
            split
            · rename_i p' r' res' resultShape'
              rw [typedResult, resultShape] at resultShape'
              cases resultShape'
              have a1 : agree asm value'.type (.computation planType responseType (.variant typed'.row)) = true := by
                rw [typedRow, valueType]; exact agreed
              rw [dif_pos a1, dif_pos pureResult]
              refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, rfl, ?_⟩
              · show addUses value.uses typed.uses = _; rw [valueUses, typedUses, split_add Ψ hl]
              · show addUses value'.uses typed'.uses = _; rw [valueUses', typedUses', split_add Ψ' hl]
            · rename_i other
              exact (other _ _ _ (typedResult.trans resultShape)).elim
          · rename_i other
            exact (other _ _ _ activity').elim
        · rename_i notActivity
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨row, rowFound, typed, armsTyped, h⟩ := h
          split at h
          rotate_left; · cases h
          rename_i agreed
          cases h
          obtain ⟨a₂, ha₂, typedUses, typed', armsTyped', typedRow, typedResult, typedUses'⟩ :=
            ihArms ann ann' Δ _ _ 0 row none arms typed hs₂ armsTyped (shift_child hann 1)
          have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
          split
          · rename_i p r pr activity
            rw [valueType] at activity
            exact (notActivity _ _ _ activity).elim
          · have vr : variantRow asm value'.type = some row := by rw [valueType]; exact rowFound
            simp only [vr, Option.bind_some, armsTyped']
            have a1 : agree asm value'.type (.variant typed'.row) = true := by rw [typedRow, valueType]; exact agreed
            rw [dif_pos a1]
            refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, by exact typedResult, ?_⟩
            · show addUses value.uses typed.uses = _; rw [valueUses, typedUses, split_add Ψ hl]
            · show addUses value'.uses typed'.uses = _; rw [valueUses', typedUses', split_add Ψ' hl]
      | ifBool condition whenTrue whenFalse =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨c, cTyped, t, tTyped, f, fTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i cShape
        split at h
        rotate_left; · cases h
        rename_i same
        cases h
        obtain ⟨hs₁, hs₂, hs₃⟩ := (scoped_ifBool_iff _ _ _ _).1 hs
        obtain ⟨a₁, ha₁, cUses, c', cTyped', cType, cUses'⟩ :=
          ih ann ann' Δ _ _ condition c hs₁ cTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, tUses, t', tTyped', tType, tUses'⟩ :=
          ih ann ann' Δ _ _ whenTrue t hs₂ tTyped (shift_child hann 1)
        obtain ⟨a₃, ha₃, fUses, f', fTyped', fType, fUses'⟩ :=
          ih ann ann' Δ _ _ whenFalse f hs₃ fTyped (shift_child hann 2)
        have hl : a₂.length = a₃.length := ha₂.trans ha₃.symm
        have hl' : a₁.length = (addUses a₂ a₃).length := by rw [length_addUses hl, ha₂, ha₁]
        have c1 : c'.type = .boolean := by rw [cType, cShape]
        have s1 : f'.type = t'.type := by rw [fType, tType, same]
        simp only [infer, Option.bind_eq_bind, cTyped', tTyped', fTyped', Option.bind_some, dif_pos c1, dif_pos s1]
        refine ⟨addUses a₁ (addUses a₂ a₃), by rw [length_addUses hl', ha₁], ?_, _, rfl, by exact tType, ?_⟩
        · show addUses c.uses (addUses t.uses f.uses) = _
          rw [cUses, tUses, fUses, split_add Ψ hl, split_add Ψ hl']
        · show addUses c'.uses (addUses t'.uses f'.uses) = _
          rw [cUses', tUses', fUses', split_add Ψ' hl, split_add Ψ' hl']
      | perform plan =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i isPlan
        split at h
        rotate_left; · cases h
        rename_i isData
        cases h
        obtain ⟨a, ha, valueUses, value', valueTyped', valueType, valueUses'⟩ :=
          ih ann ann' Δ _ _ plan value ((scoped_perform_iff _ _).1 hs) valueTyped (shift_child hann 0)
        have found' : ann' pos' = some annotation := by rw [shift_here hann]; exact found
        have a1 : agree asm value'.type annotation.domain = true := by rw [valueType]; exact agreed
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some]
        rw [dif_pos a1, dif_pos isPlan, dif_pos isData]
        exact ⟨a, ha, valueUses, _, rfl, rfl, valueUses'⟩
      | done inner =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureValue
        cases h
        obtain ⟨a, ha, valueUses, value', valueTyped', valueType, valueUses'⟩ :=
          ih ann ann' Δ _ _ inner value ((scoped_done_iff _ _).1 hs) valueTyped (shift_child hann 0)
        have found' : ann' pos' = some annotation := by rw [shift_here hann]; exact found
        have p1 : value'.type.isComputation = false := by rw [valueType]; exact pureValue
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some, dif_pos p1]
        refine ⟨a, ha, valueUses, _, rfl, ?_, valueUses'⟩
        show Ty.computation annotation.domain annotation.codomain value'.type = _; rw [valueType]
    · intro ann ann' Δ pos pos' index fields result hs h hann
      cases fields with
      | nil =>
        simp only [inferFields] at h; cases h
        exact ⟨zeroUses Δ, length_zeroUses Δ, zeroUses_append Δ Ψ, _, rfl, rfl, zeroUses_append Δ Ψ'⟩
      | cons head rest =>
        obtain ⟨name, body⟩ := head
        simp only [inferFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureFirst
        cases h
        obtain ⟨a₁, ha₁, firstUses, first', firstTyped', firstType, firstUses'⟩ :=
          ih ann ann' Δ _ _ body first (hs _ List.mem_cons_self) firstTyped (shift_child hann index)
        obtain ⟨a₂, ha₂, laterUses, later', laterTyped', laterType, laterUses'⟩ :=
          ihFields ann ann' Δ pos pos' (index + 1) rest later (fun f hf => hs f (List.mem_cons_of_mem _ hf))
            laterTyped hann
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have p1 : first'.type.isComputation = false := by rw [firstType]; exact pureFirst
        simp only [inferFields, Option.bind_eq_bind, firstTyped', laterTyped', Option.bind_some, dif_pos p1]
        refine ⟨addUses a₁ a₂, by rw [length_addUses hl, ha₁], ?_, _, rfl, ?_, ?_⟩
        · show addUses first.uses later.uses = _; rw [firstUses, laterUses, split_add Ψ hl]
        · show Ty.field name first'.type later'.type = Ty.field name first.type later.type; rw [firstType, laterType]
        · show addUses first'.uses later'.uses = _; rw [firstUses', laterUses', split_add Ψ' hl]
    · intro ann ann' Δ pos pos' index row expected arms result hs h hann
      cases arms with
      | nil =>
        cases expected with
        | none => simp [inferArms] at h
        | some expectedResult =>
          simp only [inferArms] at h; cases h
          exact ⟨zeroUses Δ, length_zeroUses Δ, zeroUses_append Δ Ψ, _, rfl, rfl, rfl, zeroUses_append Δ Ψ'⟩
      | cons head rest =>
        obtain ⟨name, body⟩ := head
        simp only [inferArms, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨payload, found, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i sharePayload
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i safe
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i sameResult
        cases h
        obtain ⟨a₁, ha₁, firstUses, first₀, firstTyped₀, firstType₀, firstUses₀⟩ :=
          ih ann ann' (⟨payload, .unrestricted⟩ :: Δ) _ _ body first (hs _ List.mem_cons_self) firstTyped
            (shift_child hann index)
        obtain ⟨first', firstTyped', firstType, firstUses'⟩ :
            ∃ first' : Inferred asm (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ')) body,
              infer asm ann' (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ')) (pos' ++ [index]) (fuel + extra) body =
                some first' ∧ first'.type = first.type ∧ first'.uses = a₁ ++ zeroUses Ψ' :=
          ⟨first₀, firstTyped₀, firstType₀, firstUses₀⟩
        obtain ⟨a₂, ha₂, laterUses, later', laterTyped', laterRow, laterResult, laterUses'⟩ :=
          ihArms ann ann' Δ pos pos' (index + 1) row (some first.type) rest later
            (fun arm harm => hs arm (List.mem_cons_of_mem _ harm)) laterTyped hann
        have hne : a₁ ≠ [] := ne_nil_of_length_succ ha₁
        have hl : a₁.tail.length = a₂.length := by simp [ha₁, ha₂]
        have found' : row.lookup asm.bounds (fuel + extra + 1) name = some payload := Ty.lookup_mono found (by omega)
        have u1 : safeUses (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ')) first'.uses = true := by
          rw [firstUses']
          exact safeUses_append_zero (Δ := ⟨payload, .unrestricted⟩ :: Δ) ha₁ (by rw [← firstUses]; exact safe)
        rw [← firstType] at laterTyped'
        have hl' : later'.result = first'.type := by rw [laterResult, firstType]; exact sameResult
        simp only [inferArms, Option.bind_eq_bind, found', Option.bind_some, dif_pos sharePayload, firstTyped',
          dif_pos u1, laterTyped', dif_pos hl']
        refine ⟨addUses a₁.tail a₂, by rw [length_addUses hl]; simp [ha₁], ?_, _, rfl, ?_, by exact firstType, ?_⟩
        · show addUses first.uses.tail later.uses = _; rw [firstUses, laterUses, split_tail Ψ hne, split_add Ψ hl]
        · show Ty.field name payload later'.row = Ty.field name payload later.row; rw [laterRow]
        · show addUses first'.uses.tail later'.uses = _
          rw [firstUses', laterUses', split_tail Ψ' hne, split_add Ψ' hl]

/-- More fuel never loses a result of `infer`, and the result is the same. -/
public theorem infer_mono {asm : Assumptions} {ann : Annotations} {Γ : Context} {pos : List Nat}
    {fuel fuel' : Nat} {term : Term} {result : Inferred asm Γ term}
    (h : infer asm ann Γ pos fuel term = some result) (le : fuel ≤ fuel') :
    infer asm ann Γ pos fuel' term = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  have e : Γ ++ [] = Γ := List.append_nil Γ
  revert result h
  rw [← e]
  intro result h
  have hs : Scoped Γ.length term := by simpa using typed_scoped result.derivation
  obtain ⟨a, _, hu, result', h', ht, hu'⟩ :=
    (infer_transport asm [] [] rfl extra fuel).1 ann ann Γ pos pos term result hs h (fun _ => rfl)
  cases result with
  | mk ty us d =>
    cases result' with
    | mk ty' us' d' =>
      simp only at ht hu hu'
      subst ht
      have : us' = us := hu'.trans hu.symm
      subst this
      exact h'

/-- More fuel never loses a result of `check`, and the result is the same. -/
public theorem check_mono {source : AnnotatedTerm} {Γ : Context} {fuel fuel' : Nat} {c : Checked source Γ}
    (h : check source Γ fuel = some c) (le : fuel ≤ fuel') : check source Γ fuel' = some c := by
  unfold check at h ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨result, typed, h⟩ := h
  exact ⟨result, infer_mono typed le, h⟩

/-! ## The substitution lemma -/

/-- What the lemma asks of the fillings: each is closed, and checks (under the template's assumptions
`asm`, with its own annotations) in the hole's context `Ψ` at fuel `m`, at exactly the type `Ψ`
declares for the hypothesis it fills. -/
public structure Fillings (asm : Assumptions) (Ψ : Context) (m : Nat) (σ : Nat → Option AnnotatedTerm) : Prop where
  closed : ∀ x f, σ x = some f → Scoped 0 f.term
  typed : ∀ x f, σ x = some f → ∃ (b : Binding) (r : Inferred asm Ψ f.term),
    Ψ[x]? = some b ∧ infer asm f.annotations Ψ [] m f.term = some r ∧ r.type = b.type

/-- The annotations `ann'` of the filled term agree, below `pos`, with what `annotationsAt` reads off
`term` at `(depth, pos)`. -/
@[expose] public def FilledAnn (σ : Nat → Option AnnotatedTerm) (ann ann' : Annotations) (depth : Nat)
    (pos : List Nat) (term : Term) : Prop :=
  ∀ rest, ann' (pos ++ rest) = annotationsAt σ ann depth pos term rest

/-- `FilledAnn` for each item of a field or arm list, numbered from `index` under `pos`. -/
@[expose] public def FilledAnnList (σ : Nat → Option AnnotatedTerm) (ann ann' : Annotations) (depth : Nat)
    (pos : List Nat) (index : Nat) (items : List (String × Term)) : Prop :=
  ∀ j rest, (hj : j < items.length) →
    ann' (pos ++ (index + j) :: rest) = annotationsAt σ ann depth (pos ++ [index + j]) (items[j]).2 rest

theorem FilledAnn.child {σ : Nat → Option AnnotatedTerm} {ann ann' : Annotations} {depth : Nat} {pos : List Nat}
    {term : Term} (h : FilledAnn σ ann ann' depth pos term) (k depth' : Nat) (child : Term)
    (step : ∀ rest, annotationsAt σ ann depth pos term (k :: rest) = annotationsAt σ ann depth' (pos ++ [k]) child rest) :
    FilledAnn σ ann ann' depth' (pos ++ [k]) child := by
  intro rest
  have := h (k :: rest)
  rw [step rest] at this
  simpa [List.append_assoc] using this

theorem FilledAnn.fields {σ : Nat → Option AnnotatedTerm} {ann ann' : Annotations} {depth : Nat} {pos : List Nat}
    {fields : List (String × Term)} (h : FilledAnn σ ann ann' depth pos (.record fields)) :
    FilledAnnList σ ann ann' depth pos 0 fields := by
  intro j rest hj
  have := h ((0 + j) :: rest)
  simp only [annotationsAt, Nat.zero_add, List.getElem?_eq_getElem hj] at this
  simpa using this

theorem FilledAnn.extendFields {σ : Nat → Option AnnotatedTerm} {ann ann' : Annotations} {depth : Nat}
    {pos : List Nat} {t : Term} {fields : List (String × Term)} (h : FilledAnn σ ann ann' depth pos (.extend t fields)) :
    FilledAnnList σ ann ann' depth (pos ++ [1]) 0 fields := by
  intro j rest hj
  have := h (1 :: (0 + j) :: rest)
  simp only [annotationsAt, Nat.zero_add, List.getElem?_eq_getElem hj] at this
  simpa [List.append_assoc] using this

theorem FilledAnn.arms {σ : Nat → Option AnnotatedTerm} {ann ann' : Annotations} {depth : Nat}
    {pos : List Nat} {t : Term} {arms : List (String × Term)} (h : FilledAnn σ ann ann' depth pos (.case t arms)) :
    FilledAnnList σ ann ann' (depth + 1) (pos ++ [1]) 0 arms := by
  intro j rest hj
  have := h (1 :: (0 + j) :: rest)
  simp only [annotationsAt, Nat.zero_add, List.getElem?_eq_getElem hj] at this
  simpa [List.append_assoc] using this

theorem FilledAnnList.head {σ : Nat → Option AnnotatedTerm} {ann ann' : Annotations} {depth : Nat} {pos : List Nat}
    {index : Nat} {name : String} {body : Term} {rest : List (String × Term)}
    (h : FilledAnnList σ ann ann' depth pos index ((name, body) :: rest)) :
    FilledAnn σ ann ann' depth (pos ++ [index]) body := by
  intro r
  have := h 0 r (by simp)
  simpa [List.append_assoc] using this

theorem FilledAnnList.tail {σ : Nat → Option AnnotatedTerm} {ann ann' : Annotations} {depth : Nat} {pos : List Nat}
    {index : Nat} {hd : String × Term} {rest : List (String × Term)}
    (h : FilledAnnList σ ann ann' depth pos index (hd :: rest)) :
    FilledAnnList σ ann ann' depth pos (index + 1) rest := by
  intro j r hj
  have := h (j + 1) r (by simp; omega)
  rw [show index + (j + 1) = index + 1 + j by omega] at this
  simpa using this

/-- The substitution lemma at the level of `infer`: with `Fillings` for `σ`, a term inferred in
`Δ ++ Ψ` (the `Δ` are the binders above the position, the `Ψ` the hole's context) is, after
`Term.substitute (fillTerm σ Δ.length)` and with annotations read by `annotationsAt`, inferred at the
same type with pointwise no more uses, at fuel `fuel + m`. By induction on fuel, mirroring `infer`,
`inferFields`, `inferArms`; a filled hypothesis is `infer_transport` of the filling. -/
theorem infer_msubst (asm : Assumptions) (Ψ : Context) (m : Nat) (σ : Nat → Option AnnotatedTerm)
    (F : Fillings asm Ψ m σ) : ∀ fuel : Nat,
    (∀ (ann ann' : Annotations) (Δ : Context) (pos : List Nat) (term : Term) (result : Inferred asm (Δ ++ Ψ) term),
      infer asm ann (Δ ++ Ψ) pos fuel term = some result →
      validContext asm.shareableVariables (Δ ++ Ψ) = true →
      FilledAnn σ ann ann' Δ.length pos term →
      ∀ term', term.substitute (fillTerm σ Δ.length) = term' →
      ∃ result' : Inferred asm (Δ ++ Ψ) term',
        infer asm ann' (Δ ++ Ψ) pos (fuel + m) term' = some result' ∧
        result'.type = result.type ∧ UsesLE result'.uses result.uses) ∧
    (∀ (ann ann' : Annotations) (Δ : Context) (pos : List Nat) (index : Nat) (fields : List (String × Term))
        (result : InferredFields asm (Δ ++ Ψ) fields),
      inferFields asm ann (Δ ++ Ψ) pos index fuel fields = some result →
      validContext asm.shareableVariables (Δ ++ Ψ) = true →
      FilledAnnList σ ann ann' Δ.length pos index fields →
      ∀ fields', (fields.map fun field => (field.1, field.2.substitute (fillTerm σ Δ.length))) = fields' →
      ∃ result' : InferredFields asm (Δ ++ Ψ) fields',
        inferFields asm ann' (Δ ++ Ψ) pos index (fuel + m) fields' = some result' ∧
        result'.type = result.type ∧ UsesLE result'.uses result.uses) ∧
    (∀ (ann ann' : Annotations) (Δ : Context) (pos : List Nat) (index : Nat) (row : Ty) (expected : Option Ty)
        (arms : List (String × Term)) (result : InferredArms asm (Δ ++ Ψ) arms),
      inferArms asm ann (Δ ++ Ψ) pos index row expected fuel arms = some result →
      validContext asm.shareableVariables (Δ ++ Ψ) = true →
      FilledAnnList σ ann ann' (Δ.length + 1) pos index arms →
      ∀ arms', (arms.map fun arm => (arm.1, arm.2.substitute (fillTerm σ (Δ.length + 1)))) = arms' →
      ∃ result' : InferredArms asm (Δ ++ Ψ) arms',
        inferArms asm ann' (Δ ++ Ψ) pos index row expected (fuel + m) arms' = some result' ∧
        result'.row = result.row ∧ result'.result = result.result ∧ UsesLE result'.uses result.uses)
  | 0 => ⟨fun _ _ _ _ _ _ h => by simp [infer] at h, fun _ _ _ _ _ _ _ h => by simp [inferFields] at h,
      fun _ _ _ _ _ _ _ _ _ h => by simp [inferArms] at h⟩
  | fuel + 1 => by
    obtain ⟨ih, ihFields, ihArms⟩ := infer_msubst asm Ψ m σ F fuel
    rw [show fuel + 1 + m = (fuel + m) + 1 by omega]
    refine ⟨?_, ?_, ?_⟩
    · intro ann ann' Δ pos term result h valid hann term' hterm'
      cases term with
      | hole _ _ => obend_cases fuel with [infer]
      | bound index =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨binding, found, h⟩ := h
        rw [dif_pos found] at h
        cases h
        cases hfill : fillingAt σ Δ.length index with
        | none =>
          simp only [Term.substitute, fillTerm, hfill] at hterm'
          subst hterm'
          simp only [infer, Option.bind_eq_bind, found, Option.bind_some]
          exact ⟨_, rfl, rfl, by exact UsesLE.refl _⟩
        | some f =>
          simp only [Term.substitute, fillTerm, hfill] at hterm'
          subst hterm'
          have hle : Δ.length ≤ index := by
            unfold fillingAt at hfill
            split at hfill
            · assumption
            · cases hfill
          have hσ : σ (index - Δ.length) = some f := by
            unfold fillingAt at hfill; rw [if_pos hle] at hfill; exact hfill
          obtain ⟨b, r, hb, hr, hty⟩ := F.typed _ _ hσ
          have hbind : binding = b := by
            have := List.getElem?_append_right (l₁ := Δ) (l₂ := Ψ) hle
            rw [found, hb] at this
            cases this
            rfl
          subst hbind
          have hann' : ∀ rest, ann' (pos ++ rest) = f.annotations ([] ++ rest) := by
            intro rest
            rw [hann rest]
            simp only [annotationsAt, hfill, List.nil_append]
          obtain ⟨a, ha, -, r', hr', hty', hu'⟩ :=
            (infer_transport asm Ψ (Δ ++ Ψ) valid (fuel + 1) m).1 f.annotations ann' [] [] pos f.term r
              (F.closed _ _ hσ) hr hann'
          have hu'' : r'.uses = zeroUses (Δ ++ Ψ) := by rw [hu', List.eq_nil_of_length_eq_zero ha]; rfl
          rw [show m + (fuel + 1) = fuel + m + 1 by omega] at hr'
          refine ⟨r', hr', hty'.trans hty, ?_⟩
          rw [hu'']
          have := UsesLE.zero (variableUses (Δ ++ Ψ) index)
          rwa [length_variableUses] at this
      | nat value =>
        simp only [infer] at h; cases h
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer]
        exact ⟨_, rfl, rfl, by exact UsesLE.refl _⟩
      | boolean value =>
        simp only [infer] at h; cases h
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer]
        exact ⟨_, rfl, rfl, by exact UsesLE.refl _⟩
      | label value =>
        simp only [infer] at h; cases h
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer]
        exact ⟨_, rfl, rfl, by exact UsesLE.refl _⟩
      | lam body =>
        simp only [Term.substitute, liftSubstitution_fillTerm σ F.closed] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i safe
        split at h
        rotate_left; · cases h
        rename_i valid'
        split at h
        rotate_left; · cases h
        rename_i captures
        cases h
        have here : ann' pos = some annotation := by
          have := hann []
          simp only [annotationsAt, List.append_nil] at this
          rw [this]; exact found
        obtain ⟨inner₀, innerTyped₀, innerType₀, innerUses₀⟩ :=
          ih ann ann' (⟨annotation.domain, annotation.parameter⟩ :: Δ) (pos ++ [0]) body inner innerTyped valid'
            (hann.child 0 _ body (fun _ => by simp only [annotationsAt, List.length_cons])) _ rfl
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :
            ∃ inner' : Inferred asm (⟨annotation.domain, annotation.parameter⟩ :: (Δ ++ Ψ))
                (body.substitute (fillTerm σ (Δ.length + 1))),
              infer asm ann' (⟨annotation.domain, annotation.parameter⟩ :: (Δ ++ Ψ)) (pos ++ [0]) (fuel + m)
                  (body.substitute (fillTerm σ (Δ.length + 1))) = some inner' ∧
                inner'.type = inner.type ∧ UsesLE inner'.uses inner.uses :=
          ⟨inner₀, innerTyped₀, innerType₀, innerUses₀⟩
        simp only [infer, Option.bind_eq_bind, here,
          innerTyped', Option.bind_some]
        rw [dif_pos (by rw [innerType]; exact agreed), dif_pos (safeUses_of_le innerUses safe), dif_pos valid',
          dif_pos (reusableAllowed_of_le innerUses.tail captures)]
        exact ⟨_, rfl, rfl, by exact innerUses.tail⟩
      | app function argument =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨fn, fnTyped, arg, argTyped, h⟩ := h
        obtain ⟨fn', fnTyped', fnType, fnUses⟩ :=
          ih ann ann' Δ _ function fn fnTyped valid (hann.child 0 _ function (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨arg', argTyped', argType, argUses⟩ :=
          ih ann ann' Δ _ argument arg argTyped valid (hann.child 1 _ argument (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, fnTyped', argTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i reuse quantity domain codomain shape
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i allowed
        cases h
        have shape' : callable fn'.type = .arrow reuse quantity domain codomain := by rw [fnType]; exact shape
        split
        · rename_i reuse' quantity' domain' codomain' shape''
          rw [shape'] at shape''
          cases shape''
          rw [dif_pos (by rw [argType]; exact agreed), dif_pos (argumentAllowed_of_le argUses allowed)]
          exact ⟨_, rfl, rfl, by exact UsesLE.add fnUses argUses⟩
        · rename_i other
          exact (other _ _ _ _ shape').elim
      | record fields =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨members, membersTyped, h⟩ := h
        cases h
        obtain ⟨members', membersTyped', membersType, membersUses⟩ :=
          ihFields ann ann' Δ pos 0 fields members membersTyped valid hann.fields _ rfl
        simp only [infer, Option.bind_eq_bind, membersTyped', Option.bind_some]
        exact ⟨_, rfl, by exact membersType, by exact membersUses⟩
      | get target name =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, member, found, h⟩ := h
        rw [dif_pos found] at h
        cases h
        obtain ⟨prior', priorTyped', priorType, priorUses⟩ :=
          ih ann ann' Δ _ target prior priorTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        have found' : prior'.type.lookup asm.bounds (fuel + m + 1) name = some member := by
          rw [priorType]; exact Ty.lookup_mono found (by omega)
        simp only [infer, Option.bind_eq_bind, priorTyped', Option.bind_some, found']
        exact ⟨_, rfl, rfl, by exact priorUses⟩
      | extend target fields =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, members, membersTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i isRow
        cases h
        obtain ⟨prior', priorTyped', priorType, priorUses⟩ :=
          ih ann ann' Δ _ target prior priorTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨members', membersTyped', membersType, membersUses⟩ :=
          ihFields ann ann' Δ (pos ++ [1]) 0 fields members membersTyped valid hann.extendFields _ rfl
        have isRow' : prior'.type.isRow asm.bounds (fuel + m + 64) = true := by
          rw [priorType]; exact Ty.isRow_mono isRow (by omega)
        simp only [infer, Option.bind_eq_bind, priorTyped', membersTyped', Option.bind_some,
          dif_pos isRow']
        refine ⟨_, rfl, ?_, by exact UsesLE.add priorUses membersUses⟩
        show overlay members'.type prior'.type = overlay members.type prior.type
        rw [membersType, priorType]
      | specification metadata extension =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨descriptor, descriptorTyped, body, bodyTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureDescriptor
        split at h
        rotate_left; · cases h
        rename_i pureBody
        cases h
        obtain ⟨d', dTyped', dType, dUses⟩ :=
          ih ann ann' Δ _ metadata descriptor descriptorTyped valid
            (hann.child 0 _ metadata (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨b', bTyped', bType, bUses⟩ :=
          ih ann ann' Δ _ extension body bodyTyped valid (hann.child 1 _ extension (fun _ => by simp only [annotationsAt])) _ rfl
        have p1 : d'.type.isComputation = false := by rw [dType]; exact pureDescriptor
        have p2 : b'.type.isComputation = false := by rw [bType]; exact pureBody
        simp only [infer, Option.bind_eq_bind, dTyped', bTyped', Option.bind_some, dif_pos p1, dif_pos p2]
        refine ⟨_, rfl, ?_, by exact UsesLE.add dUses bUses⟩
        show Ty.specification d'.type b'.type = Ty.specification descriptor.type body.type
        rw [dType, bType]
      | prototype spec target =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨code, codeTyped, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureCode
        split at h
        rotate_left; · cases h
        rename_i pureValue
        cases h
        obtain ⟨c', cTyped', cType, cUses⟩ :=
          ih ann ann' Δ _ spec code codeTyped valid (hann.child 0 _ spec (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨v', vTyped', vType, vUses⟩ :=
          ih ann ann' Δ _ target value valueTyped valid (hann.child 1 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        have p1 : c'.type.isComputation = false := by rw [cType]; exact pureCode
        have p2 : v'.type.isComputation = false := by rw [vType]; exact pureValue
        simp only [infer, Option.bind_eq_bind, cTyped', vTyped', Option.bind_some, dif_pos p1, dif_pos p2]
        refine ⟨_, rfl, ?_, by exact UsesLE.add cUses vUses⟩
        show Ty.prototype c'.type v'.type = Ty.prototype code.type value.type
        rw [cType, vType]
      | reflect target =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :=
          ih ann ann' Δ _ target inner innerTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          exact ⟨_, rfl, rfl, by exact innerUses⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | metadata target =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i metadataType extensionType shape
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :=
          ih ann ann' Δ _ target inner innerTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i m' e' shape'
          rw [innerType] at shape'
          cases shape'
          exact ⟨_, rfl, rfl, by exact innerUses⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | project target =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :=
          ih ann ann' Δ _ target inner innerTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          exact ⟨_, rfl, rfl, by exact innerUses⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | mix lower upper =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, second, secondTyped, h⟩ := h
        obtain ⟨first', firstTyped', firstType, firstUses⟩ :=
          ih ann ann' Δ _ lower first firstTyped valid (hann.child 0 _ lower (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨second', secondTyped', secondType, secondUses⟩ :=
          ih ann ann' Δ _ upper second secondTyped valid (hann.child 1 _ upper (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, firstTyped', secondTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i self inherited middle self₂ middle₂ provided shapeFirst shapeSecond
        split at h
        rotate_left; · cases h
        rename_i sameSelf
        split at h
        rotate_left; · cases h
        rename_i sameMiddle
        split at h
        rotate_left; · cases h
        rename_i captures
        split at h
        rotate_left; · cases h
        rename_i shareSelf
        split at h
        rotate_left; · cases h
        rename_i shareInherited
        split at h
        rotate_left; · cases h
        rename_i shareMiddle
        cases h
        subst sameSelf sameMiddle
        have s1 : callable first'.type = callable first.type := by rw [firstType]
        have s2 : callable second'.type = callable second.type := by rw [secondType]
        rw [shapeFirst] at s1
        rw [shapeSecond] at s2
        split
        · rename_i a b c a' c' d t1 t2
          rw [s1] at t1
          rw [s2] at t2
          cases t1
          cases t2
          rw [dif_pos rfl, dif_pos rfl, dif_pos (reusableCaptures_of_le (UsesLE.add firstUses secondUses) captures),
            dif_pos shareSelf, dif_pos shareInherited, dif_pos shareMiddle]
          exact ⟨_, rfl, rfl, by exact UsesLE.add firstUses secondUses⟩
        · rename_i other
          exact (other _ _ _ _ _ _ s1 s2).elim
      | fix spec inheritedTerm =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨code, codeTyped, base, baseTyped, h⟩ := h
        obtain ⟨code', codeTyped', codeType, codeUses⟩ :=
          ih ann ann' Δ _ spec code codeTyped valid (hann.child 0 _ spec (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨base', baseTyped', baseType, baseUses⟩ :=
          ih ann ann' Δ _ inheritedTerm base baseTyped valid
            (hann.child 1 _ inheritedTerm (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, codeTyped', baseTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i target inherited output shape
        split at h
        rotate_left; · cases h
        rename_i sameOutput
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i shareTarget
        split at h
        rotate_left; · cases h
        rename_i allowed
        split at h
        rotate_left; · cases h
        rename_i captures
        cases h
        subst sameOutput
        have s1 : callable code'.type = callable code.type := by rw [codeType]
        rw [shape] at s1
        split
        · rename_i a b c t1
          rw [s1] at t1
          cases t1
          rw [dif_pos rfl, dif_pos (by rw [baseType]; exact agreed), dif_pos shareTarget,
            dif_pos (argumentAllowed_of_le baseUses allowed), dif_pos (reusableCaptures_of_le codeUses captures)]
          exact ⟨_, rfl, rfl, by exact UsesLE.add codeUses baseUses⟩
        · rename_i other
          exact (other _ _ _ s1).elim
      | binary primitive left right =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨l, lTyped, rr, rTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i lShape
        split at h
        rotate_left; · cases h
        rename_i rShape
        cases h
        obtain ⟨l', lTyped', lType, lUses⟩ :=
          ih ann ann' Δ _ left l lTyped valid (hann.child 0 _ left (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨r', rTyped', rType, rUses⟩ :=
          ih ann ann' Δ _ right rr rTyped valid (hann.child 1 _ right (fun _ => by simp only [annotationsAt])) _ rfl
        have l1 : l'.type = (primitiveTypes primitive).1 := by rw [lType, lShape]
        have r1 : r'.type = (primitiveTypes primitive).1 := by rw [rType, rShape]
        simp only [infer, Option.bind_eq_bind, lTyped', rTyped', Option.bind_some, dif_pos l1, dif_pos r1]
        exact ⟨_, rfl, rfl, by exact UsesLE.add lUses rUses⟩
      | ifZero value zero successor =>
        simp only [Term.substitute, liftSubstitution_fillTerm σ F.closed] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨c, cTyped, z, zTyped, s, sTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i cShape
        split at h
        rotate_left; · cases h
        rename_i same
        split at h
        rotate_left; · cases h
        rename_i safe
        cases h
        have validN : validContext asm.shareableVariables (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ)) = true := by
          rw [show (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ) : Context) = [⟨.natural, .unrestricted⟩] ++ (Δ ++ Ψ) from rfl,
            validContext_append, valid]
          rfl
        obtain ⟨c', cTyped', cType, cUses⟩ :=
          ih ann ann' Δ _ value c cTyped valid (hann.child 0 _ value (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨z', zTyped', zType, zUses⟩ :=
          ih ann ann' Δ _ zero z zTyped valid (hann.child 1 _ zero (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨s₀, sTyped₀, sType₀, sUses₀⟩ :=
          ih ann ann' (⟨.natural, .unrestricted⟩ :: Δ) (pos ++ [2]) successor s sTyped validN
            (hann.child 2 _ successor (fun _ => by simp only [annotationsAt, List.length_cons])) _ rfl
        obtain ⟨s', sTyped', sType, sUses⟩ :
            ∃ s' : Inferred asm (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ)) (successor.substitute (fillTerm σ (Δ.length + 1))),
              infer asm ann' (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ)) (pos ++ [2]) (fuel + m)
                  (successor.substitute (fillTerm σ (Δ.length + 1))) = some s' ∧
                s'.type = s.type ∧ UsesLE s'.uses s.uses :=
          ⟨s₀, sTyped₀, sType₀, sUses₀⟩
        have c1 : c'.type = .natural := by rw [cType, cShape]
        have s1 : s'.type = z'.type := by rw [sType, zType, same]
        simp only [infer, Option.bind_eq_bind, cTyped', zTyped',
          sTyped', Option.bind_some, dif_pos c1, dif_pos s1, dif_pos (safeUses_of_le sUses safe)]
        exact ⟨_, rfl, by exact zType, by exact UsesLE.add cUses (UsesLE.add zUses sUses.tail)⟩
      | inject tag payload =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ :=
          ih ann ann' Δ _ payload value valueTyped valid (hann.child 0 _ payload (fun _ => by simp only [annotationsAt])) _ rfl
        have here : ann' pos = some annotation := by
          have := hann []
          simp only [annotationsAt, List.append_nil] at this
          rw [this]; exact found
        simp only [infer, Option.bind_eq_bind, here, valueTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i kind
        rw [dif_pos kind]
        split at h
        · rename_i row codomainShape
          split at h
          rotate_left; · cases h
          rename_i member
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pure
          cases h
          have m1 : row.lookup asm.bounds (fuel + m + 1) tag = some annotation.domain := Ty.lookup_mono member (by omega)
          have a1 : agree asm value'.type annotation.domain = true := by rw [valueType]; exact agreed
          rw [dif_pos m1, dif_pos a1, dif_pos pure]
          exact ⟨_, rfl, rfl, by exact valueUses⟩
        · rename_i index codomainShape
          split at h
          rotate_left; · cases h
          rename_i row aliased
          split at h
          rotate_left; · cases h
          rename_i member
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pure
          split at h
          rotate_left; · cases h
          rename_i conversion
          cases h
          have m1 : row.lookup asm.bounds (fuel + m + 1) tag = some annotation.domain := Ty.lookup_mono member (by omega)
          have a1 : agree asm value'.type annotation.domain = true := by rw [valueType]; exact agreed
          rw [dif_pos m1, dif_pos a1, dif_pos pure, dif_pos conversion]
          exact ⟨_, rfl, rfl, by exact valueUses⟩
        · cases h
      | case scrutinee arms =>
        simp only [Term.substitute, liftSubstitution_fillTerm σ F.closed] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨value, valueTyped, h⟩ := h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ :=
          ih ann ann' Δ _ scrutinee value valueTyped valid
            (hann.child 0 _ scrutinee (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, valueTyped',
          Option.bind_some]
        split at h
        · rename_i plan response produced activity
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨row, rowFound, typed, armsTyped, h⟩ := h
          split at h
          rotate_left; · cases h
          rename_i planType responseType armResult resultShape
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pureResult
          cases h
          obtain ⟨typed', armsTyped', typedRow, typedResult, typedUses⟩ :=
            ihArms ann ann' Δ (pos ++ [1]) 0 row none arms typed armsTyped valid hann.arms _ rfl
          have activity' : value'.type = .computation plan response produced := by rw [valueType, activity]
          split
          · rename_i p r pr activity''
            rw [activity'] at activity''
            cases activity''
            simp only [rowFound, Option.bind_some, armsTyped']
            split
            · rename_i p' r' res' resultShape'
              rw [typedResult, resultShape] at resultShape'
              cases resultShape'
              have a1 : agree asm value'.type (.computation planType responseType (.variant typed'.row)) = true := by
                rw [typedRow, valueType]; exact agreed
              rw [dif_pos a1, dif_pos pureResult]
              exact ⟨_, rfl, rfl, by exact UsesLE.add valueUses typedUses⟩
            · rename_i other
              exact (other _ _ _ (typedResult.trans resultShape)).elim
          · rename_i other
            exact (other _ _ _ activity').elim
        · rename_i notActivity
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨row, rowFound, typed, armsTyped, h⟩ := h
          split at h
          rotate_left; · cases h
          rename_i agreed
          cases h
          obtain ⟨typed', armsTyped', typedRow, typedResult, typedUses⟩ :=
            ihArms ann ann' Δ (pos ++ [1]) 0 row none arms typed armsTyped valid hann.arms _ rfl
          split
          · rename_i p r pr activity
            rw [valueType] at activity
            exact (notActivity _ _ _ activity).elim
          · have vr : variantRow asm value'.type = some row := by rw [valueType]; exact rowFound
            simp only [vr, Option.bind_some, armsTyped']
            have a1 : agree asm value'.type (.variant typed'.row) = true := by rw [typedRow, valueType]; exact agreed
            rw [dif_pos a1]
            exact ⟨_, rfl, by exact typedResult, by exact UsesLE.add valueUses typedUses⟩
      | ifBool condition whenTrue whenFalse =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨c, cTyped, t, tTyped, f, fTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i cShape
        split at h
        rotate_left; · cases h
        rename_i same
        cases h
        obtain ⟨c', cTyped', cType, cUses⟩ :=
          ih ann ann' Δ _ condition c cTyped valid (hann.child 0 _ condition (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨t', tTyped', tType, tUses⟩ :=
          ih ann ann' Δ _ whenTrue t tTyped valid (hann.child 1 _ whenTrue (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨f', fTyped', fType, fUses⟩ :=
          ih ann ann' Δ _ whenFalse f fTyped valid (hann.child 2 _ whenFalse (fun _ => by simp only [annotationsAt])) _ rfl
        have c1 : c'.type = .boolean := by rw [cType, cShape]
        have s1 : f'.type = t'.type := by rw [fType, tType, same]
        simp only [infer, Option.bind_eq_bind, cTyped', tTyped', fTyped', Option.bind_some, dif_pos c1,
          dif_pos s1]
        exact ⟨_, rfl, by exact tType, by exact UsesLE.add cUses (UsesLE.add tUses fUses)⟩
      | perform plan =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i isPlan
        split at h
        rotate_left; · cases h
        rename_i isData
        cases h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ :=
          ih ann ann' Δ _ plan value valueTyped valid (hann.child 0 _ plan (fun _ => by simp only [annotationsAt])) _ rfl
        have here : ann' pos = some annotation := by
          have := hann []
          simp only [annotationsAt, List.append_nil] at this
          rw [this]; exact found
        have a1 : agree asm value'.type annotation.domain = true := by rw [valueType]; exact agreed
        simp only [infer, Option.bind_eq_bind, here, valueTyped', Option.bind_some]
        rw [dif_pos a1, dif_pos isPlan, dif_pos isData]
        exact ⟨_, rfl, rfl, by exact valueUses⟩
      | done inner =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureValue
        cases h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ :=
          ih ann ann' Δ _ inner value valueTyped valid (hann.child 0 _ inner (fun _ => by simp only [annotationsAt])) _ rfl
        have here : ann' pos = some annotation := by
          have := hann []
          simp only [annotationsAt, List.append_nil] at this
          rw [this]; exact found
        have p1 : value'.type.isComputation = false := by rw [valueType]; exact pureValue
        simp only [infer, Option.bind_eq_bind, here, valueTyped', Option.bind_some, dif_pos p1]
        refine ⟨_, rfl, ?_, by exact valueUses⟩
        show Ty.computation annotation.domain annotation.codomain value'.type = _
        rw [valueType]
    · intro ann ann' Δ pos index fields result h valid hann fields' hfields'
      cases fields with
      | nil =>
        simp only [inferFields] at h; cases h
        simp only [List.map_nil] at hfields'
        subst hfields'
        simp only [inferFields]
        exact ⟨_, rfl, rfl, by exact UsesLE.refl _⟩
      | cons head rest =>
        obtain ⟨name, body⟩ := head
        simp only [List.map_cons] at hfields'
        subst hfields'
        simp only [inferFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureFirst
        cases h
        obtain ⟨first', firstTyped', firstType, firstUses⟩ := ih ann ann' Δ _ body first firstTyped valid hann.head _ rfl
        obtain ⟨later', laterTyped', laterType, laterUses⟩ :=
          ihFields ann ann' Δ pos (index + 1) rest later laterTyped valid hann.tail _ rfl
        have p1 : first'.type.isComputation = false := by rw [firstType]; exact pureFirst
        simp only [inferFields, Option.bind_eq_bind, firstTyped', laterTyped', Option.bind_some, dif_pos p1]
        refine ⟨_, rfl, ?_, by exact UsesLE.add firstUses laterUses⟩
        show Ty.field name first'.type later'.type = Ty.field name first.type later.type
        rw [firstType, laterType]
    · intro ann ann' Δ pos index row expected arms result h valid hann arms' harms'
      cases arms with
      | nil =>
        cases expected with
        | none => simp [inferArms] at h
        | some expectedResult =>
          simp only [inferArms] at h; cases h
          simp only [List.map_nil] at harms'
          subst harms'
          simp only [inferArms]
          exact ⟨_, rfl, rfl, rfl, by exact UsesLE.refl _⟩
      | cons head rest =>
        obtain ⟨name, body⟩ := head
        simp only [List.map_cons] at harms'
        subst harms'
        simp only [inferArms, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨payload, found, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i sharePayload
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i safe
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i sameResult
        cases h
        have validP : validContext asm.shareableVariables (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ)) = true := by
          rw [show (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ) : Context) = [⟨payload, .unrestricted⟩] ++ (Δ ++ Ψ) from rfl,
            validContext_append, valid]
          simp [validContext, sharePayload]
        obtain ⟨first₀, firstTyped₀, firstType₀, firstUses₀⟩ :=
          ih ann ann' (⟨payload, .unrestricted⟩ :: Δ) (pos ++ [index]) body first firstTyped validP hann.head _ rfl
        obtain ⟨first', firstTyped', firstType, firstUses⟩ :
            ∃ first' : Inferred asm (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ)) (body.substitute (fillTerm σ (Δ.length + 1))),
              infer asm ann' (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ)) (pos ++ [index]) (fuel + m)
                  (body.substitute (fillTerm σ (Δ.length + 1))) = some first' ∧
                first'.type = first.type ∧ UsesLE first'.uses first.uses :=
          ⟨first₀, firstTyped₀, firstType₀, firstUses₀⟩
        obtain ⟨later', laterTyped', laterRow, laterResult, laterUses⟩ :=
          ihArms ann ann' Δ pos (index + 1) row (some first.type) rest later laterTyped valid hann.tail _ rfl
        have found' : row.lookup asm.bounds (fuel + m + 1) name = some payload := Ty.lookup_mono found (by omega)
        rw [← firstType] at laterTyped'
        have hl : later'.result = first'.type := by rw [laterResult, firstType]; exact sameResult
        simp only [inferArms, Option.bind_eq_bind, found', Option.bind_some, dif_pos sharePayload,
          firstTyped', dif_pos (safeUses_of_le firstUses safe), laterTyped', dif_pos hl]
        refine ⟨_, rfl, ?_, by exact firstType, by exact UsesLE.add firstUses.tail laterUses⟩
        show Ty.field name payload later'.row = Ty.field name payload later.row
        rw [laterRow]

/-- **The substitution lemma.** A term `t` that checks in `Ψ` (at fuel `n`), with every filling `σ`
names closed and checking in `Ψ` under `t`'s assumptions (at fuel `m`) at exactly the type `Ψ`
declares for its hypothesis, gives `msubst σ t` checking in `Ψ` at fuel `n + m`, at `t`'s type, with
pointwise no more uses of any hypothesis than `t` had. -/
public theorem check_msubst {t : AnnotatedTerm} {Ψ : Context} {n m : Nat} {c : Checked t Ψ}
    (σ : Nat → Option AnnotatedTerm) (ht : check t Ψ n = some c)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧
      ∃ (b : Binding) (d : Checked { f with assumptions := t.assumptions } Ψ),
        Ψ[x]? = some b ∧ check { f with assumptions := t.assumptions } Ψ m = some d ∧ d.type = b.type) :
    ∃ c' : Checked (msubst σ t) Ψ, check (msubst σ t) Ψ (n + m) = some c' ∧ c'.type = c.type ∧ UsesLE c'.uses c.uses := by
  unfold check at ht
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
  obtain ⟨result, typed, ht⟩ := ht
  split at ht
  rotate_left; · cases ht
  rename_i safe
  split at ht
  rotate_left; · cases ht
  rename_i valid
  split at ht
  rotate_left; · cases ht
  rename_i asmValid
  cases ht
  have F : Fillings t.assumptions Ψ m σ := by
    refine ⟨fun x f hx => (hσ x f hx).1, fun x f hx => ?_⟩
    obtain ⟨-, b, d, hb, hd, hty⟩ := hσ x f hx
    unfold check at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
    obtain ⟨r, hr, hd⟩ := hd
    have hdt : d.type = r.type := by
      repeat' split at hd
      all_goals first | (cases hd; rfl) | cases hd
    exact ⟨b, r, hb, hr, hdt.symm.trans hty⟩
  obtain ⟨result', typed', hty, hu⟩ :=
    (infer_msubst t.assumptions Ψ m σ F n).1 t.annotations (annotationsAt σ t.annotations 0 [] t.term) [] [] t.term
      result typed valid (fun _ => rfl) _ rfl
  unfold check
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  refine ⟨⟨result'.type, result'.uses, result'.derivation, safeUses_of_le hu safe, valid, asmValid⟩,
    ⟨result', typed', ?_⟩, hty, hu⟩
  rw [dif_pos (safeUses_of_le hu safe),
    dif_pos (show validContext (msubst σ t).assumptions.shareableVariables Ψ = true from valid),
    dif_pos (show (msubst σ t).assumptions.valid = true from asmValid)]

/-! ## Teeth: the three corners, each a refusal `decide` computes -/

/-- `σ` filling hypothesis `0` with `f`, nothing else. -/
@[expose] public def fillZero (f : AnnotatedTerm) : Nat → Option AnnotatedTerm := fun i => if i = 0 then some f else none

@[expose] public def fuelTemplate : AnnotatedTerm :=
  ⟨.lam (.bound 1), fun p => if p = [] then
    some ⟨.natural, .arrow .reusable .unrestricted .natural .natural, .unrestricted, .reusable⟩ else none, {}⟩
@[expose] public def fuelFilling : AnnotatedTerm :=
  ⟨.lam (.bound 0), fun p => if p = [] then some ⟨.natural, .natural, .unrestricted, .reusable⟩ else none, {}⟩
@[expose] public def fuelContext : Context := [⟨.arrow .reusable .unrestricted .natural .natural, .unrestricted⟩]

theorem fuel_template_checks : (check fuelTemplate fuelContext 2).isSome = true := by decide
theorem fuel_filling_checks : (check fuelFilling fuelContext 2).isSome = true := by decide
theorem msubst_fuel : msubst (fillZero fuelFilling) fuelTemplate =
    ⟨.lam (.lam (.bound 0)), annotationsAt (fillZero fuelFilling) fuelTemplate.annotations 0 [] fuelTemplate.term, {}⟩ := by
  have e : (msubst (fillZero fuelFilling) fuelTemplate).term = .lam (.lam (.bound 0)) := by
    simp [msubst, Term.substitute, liftSubstitution, fillTerm, fillingAt, fillZero, fuelTemplate, fuelFilling, Term.rename,
      liftRename]
  rw [← e]; rfl
/-- TOOTH (the fuel adds). Template and filling each check at fuel 2; the filled term is refused at
fuel 2 and accepted at 3. `check_msubst` promises fuel `2 + 2`; a fixed fuel keeps the lemma only
within its budget (`Obend.Slot.Core4.calculus_check_msubst`). -/
theorem fuel_tooth :
    (check (msubst (fillZero fuelFilling) fuelTemplate) fuelContext 2).isNone = true ∧
    (check (msubst (fillZero fuelFilling) fuelTemplate) fuelContext 3).isSome = true := by
  rw [msubst_fuel]; exact ⟨by decide, by decide⟩

@[expose] public def linearTemplate : AnnotatedTerm := ⟨.binary .add (.bound 0) (.bound 1), fun _ => none, {}⟩
@[expose] public def linearFilling : AnnotatedTerm := ⟨.bound 1, fun _ => none, {}⟩
@[expose] public def linearContext : Context := [⟨.natural, .unrestricted⟩, ⟨.natural, .linear⟩]

theorem linear_template_checks : (check linearTemplate linearContext 4).isSome = true := by decide
theorem linear_filling_checks : (check linearFilling linearContext 4).isSome = true := by decide
theorem linear_filling_open : ¬ Scoped 0 linearFilling.term := by
  intro h; have := (scoped_bound_iff _ _).1 h; omega
theorem msubst_linear : msubst (fillZero linearFilling) linearTemplate =
    ⟨.binary .add (.bound 1) (.bound 1), annotationsAt (fillZero linearFilling) linearTemplate.annotations 0 []
      linearTemplate.term, {}⟩ := by
  have e : (msubst (fillZero linearFilling) linearTemplate).term = .binary .add (.bound 1) (.bound 1) := by
    simp [msubst, Term.substitute, fillTerm, fillingAt, fillZero, linearTemplate, linearFilling]
  rw [← e]; rfl
/-- TOOTH (fillings are closed). An OPEN filling (`bound 1`, the linear hypothesis) checks at the type
of hypothesis `0`, and the template checks; the filled term uses the linear hypothesis twice and is
refused. `Scoped 0` on the fillings is load-bearing. -/
theorem open_filling_tooth : (check (msubst (fillZero linearFilling) linearTemplate) linearContext 4).isNone = true := by
  rw [msubst_linear]; decide

@[expose] public def sumRow : Ty := .field "l" .natural .emptyRow
@[expose] public def sumAssumptions : Assumptions := ⟨[(0, .variant sumRow)], [], []⟩
@[expose] public def aliasFilling : AnnotatedTerm :=
  ⟨.inject "l" (.nat 1), fun p => if p = [] then some ⟨.natural, .variable 0, .unrestricted, .reusable⟩ else none,
    sumAssumptions⟩
@[expose] public def aliasTemplate : AnnotatedTerm := ⟨.bound 0, fun _ => none, {}⟩
@[expose] public def aliasContext : Context := [⟨.variable 0, .linear⟩]

theorem alias_filling_checks : (check aliasFilling aliasContext 4).isSome = true := by decide
theorem alias_template_checks : (check aliasTemplate aliasContext 4).isSome = true := by decide
theorem alias_filling_closed : Scoped 0 aliasFilling.term := .inject (.natural _)
theorem msubst_alias : msubst (fillZero aliasFilling) aliasTemplate =
    ⟨.inject "l" (.nat 1), annotationsAt (fillZero aliasFilling) aliasTemplate.annotations 0 [] aliasTemplate.term, {}⟩ := by
  have e : (msubst (fillZero aliasFilling) aliasTemplate).term = .inject "l" (.nat 1) := by
    simp [msubst, Term.substitute, fillTerm, fillingAt, fillZero, aliasTemplate, aliasFilling]
  rw [← e]; rfl
/-- TOOTH (fillings check under the template's assumptions). The filling checks under ITS assumptions
(a bound for type variable `0`, so its injection converts to the declared sum) at the hypothesis's
type; `msubst` keeps the template's assumptions, which have no bound, and the filled term is refused.
This is why `check_msubst` judges a filling as `{ f with assumptions := t.assumptions }`. -/
theorem assumptions_tooth : (check (msubst (fillZero aliasFilling) aliasTemplate) aliasContext 4).isNone = true := by
  rw [msubst_alias]; decide

#assert_axioms liftSubstitution_fillTerm typed_scoped infer_transport infer_mono check_mono infer_msubst check_msubst
  fuel_template_checks fuel_filling_checks fuel_tooth linear_template_checks linear_filling_checks linear_filling_open
  open_filling_tooth alias_filling_checks alias_template_checks alias_filling_closed assumptions_tooth

end Obend.Core.Proofs.Substitution
