module
/- `infer_msubst`, `check_msubst`: the substitution lemma. -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Substitution.Transport
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

/-! ## The substitution lemma -/

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
        result'.type = result.type ∧ UsesMasked σ Δ.length result'.uses result.uses) ∧
    (∀ (ann ann' : Annotations) (Δ : Context) (pos : List Nat) (index : Nat) (fields : List (String × Term))
        (result : InferredFields asm (Δ ++ Ψ) fields),
      inferFields asm ann (Δ ++ Ψ) pos index fuel fields = some result →
      validContext asm.shareableVariables (Δ ++ Ψ) = true →
      FilledAnnList σ ann ann' Δ.length pos index fields →
      ∀ fields', (fields.map fun field => (field.1, field.2.substitute (fillTerm σ Δ.length))) = fields' →
      ∃ result' : InferredFields asm (Δ ++ Ψ) fields',
        inferFields asm ann' (Δ ++ Ψ) pos index (fuel + m) fields' = some result' ∧
        result'.type = result.type ∧ UsesMasked σ Δ.length result'.uses result.uses) ∧
    (∀ (ann ann' : Annotations) (Δ : Context) (pos : List Nat) (index : Nat) (row : Ty) (expected : Option Ty)
        (arms : List (String × Term)) (result : InferredArms asm (Δ ++ Ψ) arms),
      inferArms asm ann (Δ ++ Ψ) pos index row expected fuel arms = some result →
      validContext asm.shareableVariables (Δ ++ Ψ) = true →
      FilledAnnList σ ann ann' (Δ.length + 1) pos index arms →
      ∀ arms', (arms.map fun arm => (arm.1, arm.2.substitute (fillTerm σ (Δ.length + 1)))) = arms' →
      ∃ result' : InferredArms asm (Δ ++ Ψ) arms',
        inferArms asm ann' (Δ ++ Ψ) pos index row expected (fuel + m) arms' = some result' ∧
        result'.row = result.row ∧ result'.result = result.result ∧ UsesMasked σ Δ.length result'.uses result.uses)
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
          exact ⟨_, rfl, rfl, by exact UsesMasked.variable (keepAt_of_fillingAt_none hfill)⟩
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
          exact UsesMasked.filled (keepAt_of_fillingAt_some hfill)
      | nat value =>
        simp only [infer] at h; cases h
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer]
        exact ⟨_, rfl, rfl, by exact UsesMasked.zero _ _ _⟩
      | boolean value =>
        simp only [infer] at h; cases h
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer]
        exact ⟨_, rfl, rfl, by exact UsesMasked.zero _ _ _⟩
      | label value =>
        simp only [infer] at h; cases h
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer]
        exact ⟨_, rfl, rfl, by exact UsesMasked.zero _ _ _⟩
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
        split at h
        rotate_left; · cases h
        rename_i fits
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
                inner'.type = inner.type ∧ UsesMasked σ (Δ.length + 1) inner'.uses inner.uses :=
          ⟨inner₀, innerTyped₀, innerType₀, innerUses₀⟩
        simp only [infer, Option.bind_eq_bind, here,
          innerTyped', Option.bind_some]
        rw [dif_pos (by rw [innerType]; exact agreed), dif_pos (safeUses_of_le innerUses.le safe), dif_pos valid',
          dif_pos (reusableAllowed_of_le innerUses.tail.le captures), dif_pos (by rw [innerUses.headD]; exact fits)]
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
          rw [dif_pos (by rw [argType]; exact agreed), dif_pos (argumentAllowed_of_le argUses.le allowed)]
          exact ⟨_, rfl, rfl, by exact UsesMasked.add fnUses argUses⟩
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨prior', priorTyped', priorType, priorUses⟩ :=
          ih ann ann' Δ _ target prior priorTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        have found' : prior'.type.lookup asm.bounds (fuel + m + 1) name = some member := by
          rw [priorType]; exact Ty.lookup_mono found (by omega)
        simp only [infer, Option.bind_eq_bind, priorTyped', Option.bind_some, found',
          dif_pos (linearFree_of_le priorUses.le free)]
        exact ⟨_, rfl, rfl, by exact priorUses⟩
      | extend target fields =>
        simp only [Term.substitute] at hterm'
        subst hterm'
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, members, membersTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i isRow
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨prior', priorTyped', priorType, priorUses⟩ :=
          ih ann ann' Δ _ target prior priorTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨members', membersTyped', membersType, membersUses⟩ :=
          ihFields ann ann' Δ (pos ++ [1]) 0 fields members membersTyped valid hann.extendFields _ rfl
        have isRow' : prior'.type.isRow asm.bounds (fuel + m + 64) = true := by
          rw [priorType]; exact Ty.isRow_mono isRow (by omega)
        simp only [infer, Option.bind_eq_bind, priorTyped', membersTyped', Option.bind_some,
          dif_pos isRow', dif_pos (linearFree_of_le priorUses.le free)]
        refine ⟨_, rfl, ?_, by exact UsesMasked.add priorUses membersUses⟩
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨d', dTyped', dType, dUses⟩ :=
          ih ann ann' Δ _ metadata descriptor descriptorTyped valid
            (hann.child 0 _ metadata (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨b', bTyped', bType, bUses⟩ :=
          ih ann ann' Δ _ extension body bodyTyped valid (hann.child 1 _ extension (fun _ => by simp only [annotationsAt])) _ rfl
        have p1 : d'.type.isComputation = false := by rw [dType]; exact pureDescriptor
        have p2 : b'.type.isComputation = false := by rw [bType]; exact pureBody
        simp only [infer, Option.bind_eq_bind, dTyped', bTyped', Option.bind_some, dif_pos p1, dif_pos p2,
          dif_pos (linearFree_of_le dUses.le free)]
        refine ⟨_, rfl, ?_, by exact UsesMasked.add dUses bUses⟩
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
        refine ⟨_, rfl, ?_, by exact UsesMasked.add cUses vUses⟩
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :=
          ih ann ann' Δ _ target inner innerTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          rw [dif_pos (linearFree_of_le innerUses.le free)]
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :=
          ih ann ann' Δ _ target inner innerTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i m' e' shape'
          rw [innerType] at shape'
          cases shape'
          rw [dif_pos (linearFree_of_le innerUses.le free)]
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ :=
          ih ann ann' Δ _ target inner innerTyped valid (hann.child 0 _ target (fun _ => by simp only [annotationsAt])) _ rfl
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          rw [dif_pos (linearFree_of_le innerUses.le free)]
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
          rw [dif_pos rfl, dif_pos rfl, dif_pos (reusableCaptures_of_le (UsesMasked.add firstUses secondUses).le captures),
            dif_pos shareSelf, dif_pos shareInherited, dif_pos shareMiddle]
          exact ⟨_, rfl, rfl, by exact UsesMasked.add firstUses secondUses⟩
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
            dif_pos (argumentAllowed_of_le baseUses.le allowed), dif_pos (reusableCaptures_of_le codeUses.le captures)]
          exact ⟨_, rfl, rfl, by exact UsesMasked.add codeUses baseUses⟩
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
        exact ⟨_, rfl, rfl, by exact UsesMasked.add lUses rUses⟩
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
        split at h
        rotate_left; · cases h
        rename_i agreeing
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
                s'.type = s.type ∧ UsesMasked σ (Δ.length + 1) s'.uses s.uses :=
          ⟨s₀, sTyped₀, sType₀, sUses₀⟩
        have c1 : c'.type = .natural := by rw [cType, cShape]
        have s1 : agree asm s'.type z'.type = true := by rw [sType, zType]; exact same
        simp only [infer, Option.bind_eq_bind, cTyped', zTyped',
          sTyped', Option.bind_some, dif_pos c1, dif_pos s1, dif_pos (safeUses_of_le sUses.le safe),
          dif_pos (zUses.agree sUses.tail agreeing)]
        exact ⟨_, rfl, by exact zType, by exact UsesMasked.add cUses (UsesMasked.join zUses sUses.tail)⟩
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
          split at h
          rotate_left; · cases h
          rename_i distinct
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
              simp only [labelsDistinct_map, distinct, ↓reduceDIte]
              exact ⟨_, rfl, rfl, by exact UsesMasked.add valueUses typedUses⟩
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
          split at h
          rotate_left; · cases h
          rename_i distinct
          split at h
          rotate_left; · cases h
          rename_i free
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
            simp only [labelsDistinct_map, distinct, ↓reduceDIte, dif_pos (linearFree_of_le valueUses.le free)]
            exact ⟨_, rfl, by exact typedResult, by exact UsesMasked.add valueUses typedUses⟩
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
        split at h
        rotate_left; · cases h
        rename_i agreeing
        cases h
        obtain ⟨c', cTyped', cType, cUses⟩ :=
          ih ann ann' Δ _ condition c cTyped valid (hann.child 0 _ condition (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨t', tTyped', tType, tUses⟩ :=
          ih ann ann' Δ _ whenTrue t tTyped valid (hann.child 1 _ whenTrue (fun _ => by simp only [annotationsAt])) _ rfl
        obtain ⟨f', fTyped', fType, fUses⟩ :=
          ih ann ann' Δ _ whenFalse f fTyped valid (hann.child 2 _ whenFalse (fun _ => by simp only [annotationsAt])) _ rfl
        have c1 : c'.type = .boolean := by rw [cType, cShape]
        have s1 : agree asm f'.type t'.type = true := by rw [fType, tType]; exact same
        simp only [infer, Option.bind_eq_bind, cTyped', tTyped', fTyped', Option.bind_some, dif_pos c1,
          dif_pos s1, dif_pos (tUses.agree fUses agreeing)]
        exact ⟨_, rfl, by exact tType, by exact UsesMasked.add cUses (UsesMasked.join tUses fUses)⟩
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ :=
          ih ann ann' Δ _ inner value valueTyped valid (hann.child 0 _ inner (fun _ => by simp only [annotationsAt])) _ rfl
        have here : ann' pos = some annotation := by
          have := hann []
          simp only [annotationsAt, List.append_nil] at this
          rw [this]; exact found
        have p1 : value'.type.isComputation = false := by rw [valueType]; exact pureValue
        simp only [infer, Option.bind_eq_bind, here, valueTyped', Option.bind_some, dif_pos p1,
          dif_pos (linearFree_of_le valueUses.le free)]
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
        exact ⟨_, rfl, rfl, by exact UsesMasked.zero _ _ _⟩
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
        refine ⟨_, rfl, ?_, by exact UsesMasked.add firstUses laterUses⟩
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
          exact ⟨_, rfl, rfl, rfl, by exact UsesMasked.zero _ _ _⟩
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
        split at h
        rotate_left; · cases h
        rename_i agreed
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i sameResult
        split at h
        rotate_left; · cases h
        rename_i agreeing
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
                first'.type = first.type ∧ UsesMasked σ (Δ.length + 1) first'.uses first.uses :=
          ⟨first₀, firstTyped₀, firstType₀, firstUses₀⟩
        obtain ⟨later', laterTyped', laterRow, laterResult, laterUses⟩ :=
          ihArms ann ann' Δ pos (index + 1) row (some (expected.getD first.type)) rest later laterTyped valid hann.tail _ rfl
        have found' : row.lookup asm.bounds (fuel + m + 1) name = some payload := Ty.lookup_mono found (by omega)
        rw [← firstType] at laterTyped'
        have hl : later'.result = expected.getD first'.type := by rw [laterResult, firstType]; exact sameResult
        have a1 : agree asm first'.type (expected.getD first'.type) = true := by rw [firstType]; exact agreed
        have j1 := firstUses.tail.agreeArms
          (rest' := rest.map fun arm => (arm.1, arm.2.substitute (fillTerm σ (Δ.length + 1)))) (by simp) laterUses agreeing
        simp only [inferArms, Option.bind_eq_bind, found', Option.bind_some, dif_pos sharePayload,
          firstTyped', dif_pos (safeUses_of_le firstUses.le safe), dif_pos a1, laterTyped', dif_pos hl,
          dif_pos j1]
        refine ⟨_, rfl, ?_, by show expected.getD first'.type = expected.getD first.type; rw [firstType], by exact UsesMasked.join firstUses.tail laterUses⟩
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
  refine ⟨⟨result'.type, result'.uses, result'.derivation, safeUses_of_le hu.le safe, valid, asmValid⟩,
    ⟨result', typed', ?_⟩, hty, hu.le⟩
  rw [dif_pos (safeUses_of_le hu.le safe),
    dif_pos (show validContext (msubst σ t).assumptions.shareableVariables Ψ = true from valid),
    dif_pos (show (msubst σ t).assumptions.valid = true from asmValid)]


end Obend.Core.Proofs.Substitution
