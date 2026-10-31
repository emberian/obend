module
/- `infer_transport`: a closed term checks the same in any valid context, at any position, with zero uses. -/
public import Obend.Tactic.Tooth
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Tactic.Cases
public import Obend.Core.Proofs.Substitution.Uses
namespace Obend.Core.Proofs.Substitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
set_option autoImplicit false

/-- A term scoped under `Δ` and checked in `Δ ++ Ψ` uses nothing of `Ψ`, and checks in `Δ ++ Ψ'`
for every valid `Ψ'`, at any position whose annotations agree below it, with any more fuel, at the
same type and with the same uses of `Δ`. By induction on fuel, mirroring `infer`, `inferFields`,
`inferArms`. -/
public theorem infer_transport (asm : Assumptions) (Ψ Ψ' : Context)
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
        split at h
        rotate_left; · cases h
        rename_i fits
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
        have a5 : annotation.parameter.fits (inner'.uses.headD 0) = true := by
          rw [innerUses', headD_append _ hne]; rw [innerUses, headD_append _ hne] at fits; exact fits
        rw [dif_pos a1, dif_pos a2, dif_pos a3, dif_pos a4, dif_pos a5]
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨a, ha, priorUses, prior', priorTyped', priorType, priorUses'⟩ :=
          ih ann ann' Δ _ _ target prior ((scoped_get_iff _ _ _).1 hs) priorTyped (shift_child hann 0)
        have found' : prior'.type.lookup asm.bounds (fuel + extra + 1) name = some member := by
          rw [priorType]; exact Ty.lookup_mono found (by omega)
        have free' : linearFree (Δ ++ Ψ') prior'.uses = true := by
          rw [priorUses']; exact linearFree_append_zero ha (by rw [← priorUses]; exact free)
        simp only [infer, Option.bind_eq_bind, priorTyped', Option.bind_some, found', dif_pos free']
        exact ⟨a, ha, priorUses, _, rfl, rfl, priorUses'⟩
      | extend target fields =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, members, membersTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i isRow
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨hst, hsf⟩ := (scoped_extend_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, priorUses, prior', priorTyped', priorType, priorUses'⟩ :=
          ih ann ann' Δ _ _ target prior hst priorTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, membersUses, members', membersTyped', membersType, membersUses'⟩ :=
          ihFields ann ann' Δ _ _ 0 fields members hsf membersTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have isRow' : prior'.type.isRow asm.bounds (fuel + extra + 64) = true := by
          rw [priorType]; exact Ty.isRow_mono isRow (by omega)
        have free' : linearFree (Δ ++ Ψ') prior'.uses = true := by
          rw [priorUses']; exact linearFree_append_zero ha₁ (by rw [← priorUses]; exact free)
        simp only [infer, Option.bind_eq_bind, priorTyped', membersTyped', Option.bind_some, dif_pos isRow', dif_pos free']
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨hs₁, hs₂⟩ := (scoped_specification_iff _ _ _).1 hs
        obtain ⟨a₁, ha₁, dUses, d', dTyped', dType, dUses'⟩ :=
          ih ann ann' Δ _ _ metadata descriptor hs₁ descriptorTyped (shift_child hann 0)
        obtain ⟨a₂, ha₂, bUses, b', bTyped', bType, bUses'⟩ :=
          ih ann ann' Δ _ _ extension body hs₂ bodyTyped (shift_child hann 1)
        have hl : a₁.length = a₂.length := ha₁.trans ha₂.symm
        have p1 : d'.type.isComputation = false := by rw [dType]; exact pureDescriptor
        have p2 : b'.type.isComputation = false := by rw [bType]; exact pureBody
        have free' : linearFree (Δ ++ Ψ') d'.uses = true := by
          rw [dUses']; exact linearFree_append_zero ha₁ (by rw [← dUses]; exact free)
        simp only [infer, Option.bind_eq_bind, dTyped', bTyped', Option.bind_some, dif_pos p1, dif_pos p2, dif_pos free']
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨a, ha, innerUses, inner', innerTyped', innerType, innerUses'⟩ :=
          ih ann ann' Δ _ _ target inner ((scoped_reflect_iff _ _).1 hs) innerTyped (shift_child hann 0)
        have free' : linearFree (Δ ++ Ψ') inner'.uses = true := by
          rw [innerUses']; exact linearFree_append_zero ha (by rw [← innerUses]; exact free)
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          rw [dif_pos free']
          exact ⟨a, ha, innerUses, _, rfl, rfl, innerUses'⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | metadata target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i metadataType extensionType shape
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨a, ha, innerUses, inner', innerTyped', innerType, innerUses'⟩ :=
          ih ann ann' Δ _ _ target inner ((scoped_metadata_iff _ _).1 hs) innerTyped (shift_child hann 0)
        have free' : linearFree (Δ ++ Ψ') inner'.uses = true := by
          rw [innerUses']; exact linearFree_append_zero ha (by rw [← innerUses]; exact free)
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i m' e' shape'
          rw [innerType] at shape'
          cases shape'
          rw [dif_pos free']
          exact ⟨a, ha, innerUses, _, rfl, rfl, innerUses'⟩
        · rename_i other
          exact (other _ _ innerType).elim
      | project target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨a, ha, innerUses, inner', innerTyped', innerType, innerUses'⟩ :=
          ih ann ann' Δ _ _ target inner ((scoped_project_iff _ _).1 hs) innerTyped (shift_child hann 0)
        have free' : linearFree (Δ ++ Ψ') inner'.uses = true := by
          rw [innerUses']; exact linearFree_append_zero ha (by rw [← innerUses]; exact free)
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          cases shape'
          rw [dif_pos free']
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
        split at h
        rotate_left; · cases h
        rename_i agreeing
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
        have s1 : agree asm s'.type z'.type = true := by rw [sType, zType]; exact same
        have u1 : safeUses (⟨.natural, .unrestricted⟩ :: (Δ ++ Ψ')) s'.uses = true := by
          rw [sUses']
          exact safeUses_append_zero (Δ := ⟨.natural, .unrestricted⟩ :: Δ) ha₃ (by rw [← sUses]; exact safe)
        have hl₃ : a₃.tail.length = Δ.length := by simp [ha₃]
        have j1 : branchesAgree (Δ ++ Ψ') z'.uses s'.uses.tail = true := by
          rw [zUses', sUses', split_tail Ψ' hne, branchesAgree_append_zero ha₂ hl₃]
          rw [zUses, sUses, split_tail Ψ hne, branchesAgree_append_zero ha₂ hl₃] at agreeing; exact agreeing
        have hl'' : a₁.length = (joinUses a₂ a₃.tail).length := by rw [length_joinUses hl, ha₂, ha₁]
        simp only [infer, Option.bind_eq_bind, cTyped', zTyped', sTyped', Option.bind_some, dif_pos c1, dif_pos s1,
          dif_pos u1, dif_pos j1]
        refine ⟨addUses a₁ (joinUses a₂ a₃.tail), by rw [length_addUses hl'', ha₁], ?_, _, rfl, by exact zType, ?_⟩
        · show addUses c.uses (joinUses z.uses s.uses.tail) = _
          rw [cUses, zUses, sUses, split_tail Ψ hne, split_join Ψ hl, split_add Ψ hl'']
        · show addUses c'.uses (joinUses z'.uses s'.uses.tail) = _
          rw [cUses', zUses', sUses', split_tail Ψ' hne, split_join Ψ' hl, split_add Ψ' hl'']
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
          split at h
          rotate_left; · cases h
          rename_i distinct
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
              simp only [labelsDistinct_map, distinct, ↓reduceDIte]
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
          split at h
          rotate_left; · cases h
          rename_i distinct
          split at h
          rotate_left; · cases h
          rename_i free
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
            have free' : linearFree (Δ ++ Ψ') value'.uses = true := by
              rw [valueUses']; exact linearFree_append_zero ha₁ (by rw [← valueUses]; exact free)
            simp only [labelsDistinct_map, distinct, ↓reduceDIte, dif_pos free']
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
        split at h
        rotate_left; · cases h
        rename_i agreeing
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
        have s1 : agree asm f'.type t'.type = true := by rw [fType, tType]; exact same
        have j1 : branchesAgree (Δ ++ Ψ') t'.uses f'.uses = true := by
          rw [tUses', fUses', branchesAgree_append_zero ha₂ ha₃]
          rw [tUses, fUses, branchesAgree_append_zero ha₂ ha₃] at agreeing; exact agreeing
        have hl'' : a₁.length = (joinUses a₂ a₃).length := by rw [length_joinUses hl, ha₂, ha₁]
        simp only [infer, Option.bind_eq_bind, cTyped', tTyped', fTyped', Option.bind_some, dif_pos c1, dif_pos s1,
          dif_pos j1]
        refine ⟨addUses a₁ (joinUses a₂ a₃), by rw [length_addUses hl'', ha₁], ?_, _, rfl, by exact tType, ?_⟩
        · show addUses c.uses (joinUses t.uses f.uses) = _
          rw [cUses, tUses, fUses, split_join Ψ hl, split_add Ψ hl'']
        · show addUses c'.uses (joinUses t'.uses f'.uses) = _
          rw [cUses', tUses', fUses', split_join Ψ' hl, split_add Ψ' hl'']
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
        split at h
        rotate_left; · cases h
        rename_i free
        cases h
        obtain ⟨a, ha, valueUses, value', valueTyped', valueType, valueUses'⟩ :=
          ih ann ann' Δ _ _ inner value ((scoped_done_iff _ _).1 hs) valueTyped (shift_child hann 0)
        have found' : ann' pos' = some annotation := by rw [shift_here hann]; exact found
        have p1 : value'.type.isComputation = false := by rw [valueType]; exact pureValue
        have free' : linearFree (Δ ++ Ψ') value'.uses = true := by
          rw [valueUses']; exact linearFree_append_zero ha (by rw [← valueUses]; exact free)
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some, dif_pos p1, dif_pos free']
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
        obtain ⟨a₁, ha₁, firstUses, first₀, firstTyped₀, firstType₀, firstUses₀⟩ :=
          ih ann ann' (⟨payload, .unrestricted⟩ :: Δ) _ _ body first (hs _ List.mem_cons_self) firstTyped
            (shift_child hann index)
        obtain ⟨first', firstTyped', firstType, firstUses'⟩ :
            ∃ first' : Inferred asm (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ')) body,
              infer asm ann' (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ')) (pos' ++ [index]) (fuel + extra) body =
                some first' ∧ first'.type = first.type ∧ first'.uses = a₁ ++ zeroUses Ψ' :=
          ⟨first₀, firstTyped₀, firstType₀, firstUses₀⟩
        obtain ⟨a₂, ha₂, laterUses, later', laterTyped', laterRow, laterResult, laterUses'⟩ :=
          ihArms ann ann' Δ pos pos' (index + 1) row (some (expected.getD first.type)) rest later
            (fun arm harm => hs arm (List.mem_cons_of_mem _ harm)) laterTyped hann
        have hne : a₁ ≠ [] := ne_nil_of_length_succ ha₁
        have hl : a₁.tail.length = a₂.length := by simp [ha₁, ha₂]
        have found' : row.lookup asm.bounds (fuel + extra + 1) name = some payload := Ty.lookup_mono found (by omega)
        have u1 : safeUses (⟨payload, .unrestricted⟩ :: (Δ ++ Ψ')) first'.uses = true := by
          rw [firstUses']
          exact safeUses_append_zero (Δ := ⟨payload, .unrestricted⟩ :: Δ) ha₁ (by rw [← firstUses]; exact safe)
        rw [← firstType] at laterTyped'
        have hl' : later'.result = expected.getD first'.type := by rw [laterResult, firstType]; exact sameResult
        have a1 : agree asm first'.type (expected.getD first'.type) = true := by rw [firstType]; exact agreed
        have hl₁ : a₁.tail.length = Δ.length := by simp [ha₁]
        have j1 : (rest.isEmpty || branchesAgree (Δ ++ Ψ') first'.uses.tail later'.uses) = true := by
          rw [firstUses', laterUses', split_tail Ψ' hne, branchesAgree_append_zero hl₁ ha₂]
          rw [firstUses, laterUses, split_tail Ψ hne, branchesAgree_append_zero hl₁ ha₂] at agreeing; exact agreeing
        simp only [inferArms, Option.bind_eq_bind, found', Option.bind_some, dif_pos sharePayload, firstTyped',
          dif_pos u1, dif_pos a1, laterTyped', dif_pos hl', dif_pos j1]
        refine ⟨joinUses a₁.tail a₂, by rw [length_joinUses hl]; simp [ha₁], ?_, _, rfl, ?_, by show expected.getD first'.type = expected.getD first.type; rw [firstType], ?_⟩
        · show joinUses first.uses.tail later.uses = _; rw [firstUses, laterUses, split_tail Ψ hne, split_join Ψ hl]
        · show Ty.field name payload later'.row = Ty.field name payload later.row; rw [laterRow]
        · show joinUses first'.uses.tail later'.uses = _
          rw [firstUses', laterUses', split_tail Ψ' hne, split_join Ψ' hl]

end Obend.Core.Proofs.Substitution
