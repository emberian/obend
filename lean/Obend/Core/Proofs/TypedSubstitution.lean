module
/- Semantic substitution for Checked evidence, independently of checker fuel and annotations. -/
public import Obend.Core.Proofs.Substitution.Msubst
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.Substitution.Transport
import all Obend.Core.Proofs.Substitution.Mono
import all Obend.Core.Proofs.Substitution.Msubst

namespace Obend.Core.Proofs.TypedSubstitution
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant
open Obend.Core.Proofs.Substitution
set_option autoImplicit false

/-- Transport a derivation whose free indices lie in a retained prefix. The discarded
context has zero uses. This is induction on evidence, including conversion rules. -/
public theorem partialTyping_transport {asm : Assumptions} {Γ : Context} {term : Term}
    {type : Ty} {uses : Uses} (typed : PartialTyping asm Γ term type uses)
    (Ψ Ψ' : Context) (valid' : validContext asm.shareableVariables Ψ' = true) :
    ∀ Δ : Context, Γ = Δ ++ Ψ → Scoped Δ.length term →
      ∃ a : Uses, a.length = Δ.length ∧ uses = a ++ zeroUses Ψ ∧
        PartialTyping asm (Δ ++ Ψ') term type (a ++ zeroUses Ψ') := by
  refine PartialTyping.rec
    (motive_1 := fun Γ term type uses _ => ∀ Δ : Context, Γ = Δ ++ Ψ → Scoped Δ.length term →
      ∃ a : Uses, a.length = Δ.length ∧ uses = a ++ zeroUses Ψ ∧
        PartialTyping asm (Δ ++ Ψ') term type (a ++ zeroUses Ψ'))
    (motive_2 := fun Γ fields row uses _ => ∀ Δ : Context, Γ = Δ ++ Ψ →
      (∀ f ∈ fields, Scoped Δ.length f.2) →
      ∃ a : Uses, a.length = Δ.length ∧ uses = a ++ zeroUses Ψ ∧
        FieldsTyping asm (Δ ++ Ψ') fields row (a ++ zeroUses Ψ'))
    (motive_3 := fun Γ arms row result uses _ => ∀ Δ : Context, Γ = Δ ++ Ψ →
      (∀ arm ∈ arms, Scoped (Δ.length + 1) arm.2) →
      ∃ a : Uses, a.length = Δ.length ∧ uses = a ++ zeroUses Ψ ∧
        ArmsTyping asm (Δ ++ Ψ') arms row result (a ++ zeroUses Ψ'))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · rintro Γ i b found Δ rfl hs
    have hi : i < Δ.length := (scoped_bound_iff _ _).mp hs
    have hf : (Δ ++ Ψ')[i]? = some b := by
      rw [List.getElem?_append_left hi]
      rw [← List.getElem?_append_left (l₂ := Ψ) hi]
      exact found
    refine ⟨variableUses Δ i, length_variableUses _ _, variableUses_append_left Ψ hi, ?_⟩
    rw [← variableUses_append_left Ψ' hi]
    exact .bound hf
  · rintro Γ value Δ rfl hs
    refine ⟨zeroUses Δ, length_zeroUses _, zeroUses_append Δ Ψ, ?_⟩
    rw [← zeroUses_append]
    exact .natural _ value
  · rintro Γ value Δ rfl hs
    refine ⟨zeroUses Δ, length_zeroUses _, zeroUses_append Δ Ψ, ?_⟩
    rw [← zeroUses_append]
    exact .boolean _ value
  · rintro Γ value Δ rfl hs
    refine ⟨zeroUses Δ, length_zeroUses _, zeroUses_append Δ Ψ, ?_⟩
    rw [← zeroUses_append]
    exact .label _ value
  · rintro Γ body ann u d safe valid captures fits ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih (⟨ann.domain, ann.parameter⟩ :: Δ) rfl ((scoped_lam_iff _ _).mp hs)
    have hn : a ≠ [] := ne_nil_of_length_succ ha
    have ht : a.tail.length = Δ.length := by simpa using (congrArg (fun n => n - 1) ha).trans (Nat.add_sub_cancel _ _)
    refine ⟨a.tail, ht, by rw [hu, split_tail Ψ hn], ?_⟩
    rw [← split_tail Ψ' hn]
    apply PartialTyping.lambda d'
    · exact safeUses_append_zero ha (hu ▸ safe)
    · change validContext asm.shareableVariables ((⟨ann.domain, ann.parameter⟩ :: Δ) ++ Ψ') = true
      change validContext asm.shareableVariables ((⟨ann.domain, ann.parameter⟩ :: Δ) ++ Ψ) = true at valid
      rw [validContext_append, Bool.and_eq_true] at valid ⊢
      exact ⟨valid.1, valid'⟩
    · rw [split_tail Ψ' hn]
      apply reusableAllowed_append_zero (Ψ := Ψ) ht
      simpa only [hu, split_tail Ψ hn] using captures
    · rw [headD_append _ hn]; rw [hu, headD_append _ hn] at fits; exact fits
  · rintro Γ term actual expected u d same ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl (hs)
    exact ⟨a, ha, hu, .conversion d' same⟩
  · rintro Γ fn arg ft argTy dom cod fu au reuse qty df da shape same allowed ih₁ ih₂ Δ rfl hs
    simp only [scoped_app_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .application d₁ d₂ shape same (argumentAllowed_append_zero hb (hv ▸ allowed))
  · rintro Γ fields row u d ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_record_iff _ _).mp hs)
    exact ⟨a, ha, hu, .record d'⟩
  · rintro Γ target tt member u name fuel d found ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_get_iff _ _ _).mp hs)
    exact ⟨a, ha, hu, .get d' found⟩
  · rintro Γ target fields tt row tu fu fuel dt df rowOk ih₁ ih₂ Δ rfl hs
    simp only [scoped_extend_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .extend d₁ d₂ rowOk
  · rintro Γ metadataTerm ext mt et mu eu dm de mp ep ih₁ ih₂ Δ rfl hs
    simp only [scoped_specification_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .specification d₁ d₂ mp ep
  · rintro Γ spec target st tt su tu ds dt sp tp ih₁ ih₂ Δ rfl hs
    simp only [scoped_prototype_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .prototype d₁ d₂ sp tp
  · rintro Γ target t₁ t₂ u d ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_reflect_iff _ _).mp hs)
    exact ⟨a, ha, hu, .reflect d'⟩
  · rintro Γ target t₁ t₂ u d ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_metadata_iff _ _).mp hs)
    exact ⟨a, ha, hu, .metadata d'⟩
  · rintro Γ target t₁ t₂ u d ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_project_iff _ _).mp hs)
    exact ⟨a, ha, hu, .project d'⟩
  · rintro Γ lower upper lt ut self inherited middle provided lu uu dl du sl su cap sh ih mh ih₁ ih₂ Δ rfl hs
    simp only [scoped_mix_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .mix d₁ d₂ sl su (by rw [split_add Ψ' hab]; exact reusableCaptures_append_zero ((length_addUses hab).trans ha) (by simpa only [hu, hv, split_add Ψ hab] using cap)) sh ih mh
  · rintro Γ spec base st inherited target su iu ds shape di sh allowed cap ih₁ ih₂ Δ rfl hs
    simp only [scoped_fix_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .fix d₁ shape d₂ sh (argumentAllowed_append_zero hb (hv ▸ allowed)) (reusableCaptures_append_zero ha (hu ▸ cap))
  · rintro Γ prim left right input output lu ru shape dl dr ih₁ ih₂ Δ rfl hs
    simp only [scoped_binary_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .binary shape d₁ d₂
  · rintro Γ value zero succ result vu zu su dv dz ds safe ih₁ ih₂ ih₃ Δ rfl hs
    simp only [scoped_condition_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl hs.1
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl hs.2.1
    obtain ⟨c, hc, hw, d₃⟩ := ih₃ (⟨.natural, .unrestricted⟩ :: Δ) rfl hs.2.2
    have hn : c ≠ [] := ne_nil_of_length_succ hc
    have ht : c.tail.length = Δ.length := by simpa using (congrArg (fun n => n - 1) hc).trans (Nat.add_sub_cancel _ _)
    have hbc := hb.trans ht.symm
    have habc := ha.trans ((length_addUses hbc).trans hb).symm
    refine ⟨addUses a (addUses b c.tail), (length_addUses habc).trans ha, ?_, ?_⟩
    · rw [hu, hv, hw, split_tail Ψ hn, split_add Ψ hbc, split_add Ψ habc]
    · rw [← split_add Ψ' habc, ← split_add Ψ' hbc, ← split_tail Ψ' hn]
      exact .ifZero d₁ d₂ d₃ (safeUses_append_zero hc (hw ▸ safe))
  · rintro Γ tag payload pt row u fuel d found pure ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_inject_iff _ _ _).mp hs)
    exact ⟨a, ha, hu, .inject d' found pure⟩
  · rintro Γ scrut arms row result su au ds da distinct ih₁ ih₂ Δ rfl hs
    simp only [scoped_case_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .case d₁ d₂ distinct
  · rintro Γ cond yes no result cu tu fu dc dt df ih₁ ih₂ ih₃ Δ rfl hs
    simp only [scoped_ifBool_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl hs.1
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl hs.2.1
    obtain ⟨c, hc, hw, d₃⟩ := ih₃ Δ rfl hs.2.2
    have hbc := hb.trans hc.symm
    have habc := ha.trans ((length_addUses hbc).trans hb).symm
    refine ⟨addUses a (addUses b c), (length_addUses habc).trans ha, ?_, ?_⟩
    · rw [hu, hv, hw, split_add Ψ hbc, split_add Ψ habc]
    · rw [← split_add Ψ' habc, ← split_add Ψ' hbc]
      exact .ifBool d₁ d₂ d₃
  · rintro Γ plan pt response u d isPlan isData ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_perform_iff _ _).mp hs)
    exact ⟨a, ha, hu, .perform d' isPlan isData⟩
  · rintro Γ value pt response result u d pure ih Δ rfl hs
    obtain ⟨a, ha, hu, d'⟩ := ih Δ rfl ((scoped_done_iff _ _).mp hs)
    exact ⟨a, ha, hu, .done d' pure⟩
  · rintro Γ scrut arms plan response row result su au ds da pure distinct ih₁ ih₂ Δ rfl hs
    simp only [scoped_case_iff] at hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs.1)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (hs.2)
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .effectCase d₁ d₂ pure distinct
  · rintro Γ Δ rfl hs
    refine ⟨zeroUses Δ, length_zeroUses _, zeroUses_append Δ Ψ, ?_⟩
    rw [← zeroUses_append]
    exact .nil _
  · rintro Γ name body rest type row bu ru db dr pure ih₁ ih₂ Δ rfl hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ Δ rfl (hs _ (List.mem_cons_self))
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (fun f hf => hs f (List.mem_cons_of_mem _ hf))
    have hab := ha.trans hb.symm
    refine ⟨addUses a b, (length_addUses hab).trans ha, ?_, ?_⟩
    · rw [hu, hv, split_add Ψ hab]
    · rw [← split_add Ψ' hab]
      exact .cons d₁ d₂ pure
  · rintro Γ result Δ rfl hs
    refine ⟨zeroUses Δ, length_zeroUses _, zeroUses_append Δ Ψ, ?_⟩
    rw [← zeroUses_append]
    exact .nil _ _
  · rintro Γ name body rest payload row result bu ru db safe share dr ih₁ ih₂ Δ rfl hs
    obtain ⟨a, ha, hu, d₁⟩ := ih₁ (⟨payload, .unrestricted⟩ :: Δ) rfl (hs _ List.mem_cons_self)
    obtain ⟨b, hb, hv, d₂⟩ := ih₂ Δ rfl (fun f hf => hs f (List.mem_cons_of_mem _ hf))
    have hn : a ≠ [] := ne_nil_of_length_succ ha
    have ht : a.tail.length = Δ.length := by simpa using (congrArg (fun n => n - 1) ha).trans (Nat.add_sub_cancel _ _)
    have hab := ht.trans hb.symm
    refine ⟨addUses a.tail b, (length_addUses hab).trans ht, ?_, ?_⟩
    · rw [hu, hv, split_tail Ψ hn, split_add Ψ hab]
    · rw [← split_add Ψ' hab, ← split_tail Ψ' hn]
      exact .cons d₁ (safeUses_append_zero ha (hu ▸ safe)) share d₂

/-- A closed derivation has zero uses and transports to every valid context. -/
public theorem partialTyping_closed_transport {asm : Assumptions} {Γ : Context} {term : Term}
    {type : Ty} {uses : Uses} (typed : PartialTyping asm Γ term type uses)
    (closed : Scoped 0 term) (Γ' : Context)
    (valid' : validContext asm.shareableVariables Γ' = true) :
    uses = zeroUses Γ ∧ PartialTyping asm Γ' term type (zeroUses Γ') := by
  obtain ⟨a, ha, hu, d⟩ := partialTyping_transport typed Γ Γ' valid' [] rfl closed
  have : a = [] := by simpa using ha
  subst a
  exact ⟨hu, d⟩

private theorem validContext_cons_unrestricted {asm : Assumptions} {Γ : Context} {type : Ty}
    (valid : validContext asm.shareableVariables Γ = true)
    (share : type.shareableUnder asm.shareableVariables = true) :
    validContext asm.shareableVariables (⟨type, .unrestricted⟩ :: Γ) = true := by
  simp [validContext, validContext] at valid ⊢
  exact ⟨share, valid⟩

/-- Simultaneous substitution on typing evidence. The mutual recursor also handles
fields and arms; conversions and their types are retained without consulting `infer`. -/
public theorem partialTyping_msubst {asm : Assumptions} {Γ : Context} {term : Term}
    {type : Ty} {uses : Uses} (typed : PartialTyping asm Γ term type uses)
    (Ψ : Context) (σ : Nat → Option AnnotatedTerm)
    (closed : ∀ x f, σ x = some f → Scoped 0 f.term)
    (fillings : ∀ x f, σ x = some f → ∃ (b : Binding) (u : Uses),
      Ψ[x]? = some b ∧ PartialTyping asm Ψ f.term b.type u) :
    ∀ Δ : Context, Γ = Δ ++ Ψ → validContext asm.shareableVariables Γ = true →
      ∃ u : Uses, PartialTyping asm Γ (term.substitute (fillTerm σ Δ.length)) type u ∧ UsesLEOn Δ.length u uses := by
  refine PartialTyping.rec
    (motive_1 := fun Γ term type uses _ => ∀ Δ : Context, Γ = Δ ++ Ψ →
      validContext asm.shareableVariables Γ = true →
      ∃ u : Uses, PartialTyping asm Γ (term.substitute (fillTerm σ Δ.length)) type u ∧ UsesLEOn Δ.length u uses)
    (motive_2 := fun Γ fields row uses _ => ∀ Δ : Context, Γ = Δ ++ Ψ →
      validContext asm.shareableVariables Γ = true →
      ∃ u : Uses, FieldsTyping asm Γ
        (fields.map fun f => (f.1, f.2.substitute (fillTerm σ Δ.length))) row u ∧ UsesLEOn Δ.length u uses)
    (motive_3 := fun Γ arms row result uses _ => ∀ Δ : Context, Γ = Δ ++ Ψ →
      validContext asm.shareableVariables Γ = true →
      ∃ u : Uses, ArmsTyping asm Γ
        (arms.map fun arm => (arm.1, arm.2.substitute (fillTerm σ (Δ.length + 1)))) row result u ∧ UsesLEOn Δ.length u uses)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · rintro Γ i b found Δ rfl validΓ
    simp only [Term.substitute]
    by_cases isLocal : i < Δ.length
    · have empty : fillingAt σ Δ.length i = none := by simp [fillingAt, show ¬ Δ.length ≤ i by omega]
      rw [fillTerm, empty]
      exact ⟨_, .bound found, UsesLEOn.refl _ _⟩
    · have ge : Δ.length ≤ i := by omega
      cases hf : σ (i - Δ.length) with
      | none =>
        have empty : fillingAt σ Δ.length i = none := by simp [fillingAt, ge, hf]
        rw [fillTerm, empty]
        exact ⟨_, .bound found, UsesLEOn.refl _ _⟩
      | some f =>
        obtain ⟨b', u, hb, df⟩ := fillings _ _ hf
        have eqb : b' = b := by
          rw [List.getElem?_append_right ge] at found
          exact Option.some.inj (hb.symm.trans found)
        subst b'
        obtain ⟨_, df'⟩ := partialTyping_closed_transport df (closed _ _ hf) (Δ ++ Ψ) validΓ
        have filled : fillingAt σ Δ.length i = some f := by simp [fillingAt, ge, hf]
        rw [fillTerm, filled]
        refine ⟨zeroUses (Δ ++ Ψ), df', ?_, ?_⟩
        · simpa only [zeroUses, length_variableUses] using UsesLE.zero (variableUses (Δ ++ Ψ) i)
        · have := variableUses_take_zero (Δ ++ Ψ) ge
          rw [length_variableUses] at this
          simpa only [zeroUses] using this.symm
  · rintro Γ value Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .natural _ value, UsesLEOn.refl _ _⟩
  · rintro Γ value Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .boolean _ value, UsesLEOn.refl _ _⟩
  · rintro Γ value Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .label _ value, UsesLEOn.refl _ _⟩
  · rintro Γ body ann u d safe valid captures fits ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih (⟨ann.domain, ann.parameter⟩ :: Δ) rfl valid
    simp only [Term.substitute, liftSubstitution_fillTerm σ closed]
    exact ⟨u'.tail, .lambda d' (safeUses_of_le hu.le safe) valid
      (reusableAllowed_of_le hu.tail.le captures) (by rw [hu.headD]; exact fits), hu.tail⟩
  · rintro Γ term actual expected u d same ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    exact ⟨u', .conversion d' same, hu⟩
  · rintro Γ fn arg ft argTy dom cod fu au reuse qty df da shape same allowed ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .application d₁ d₂ shape same (argumentAllowed_of_le hv.le allowed), UsesLEOn.add hu hv⟩
  · rintro Γ fields row u d ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .record d', hu⟩
  · rintro Γ target tt member u name fuel d found ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .get d' found, hu⟩
  · rintro Γ target fields tt row tu fu fuel dt df rowOk ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .extend d₁ d₂ rowOk, UsesLEOn.add hu hv⟩
  · rintro Γ metadataTerm ext mt et mu eu dm de mp ep ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .specification d₁ d₂ mp ep, UsesLEOn.add hu hv⟩
  · rintro Γ spec target st tt su tu ds dt sp tp ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .prototype d₁ d₂ sp tp, UsesLEOn.add hu hv⟩
  · rintro Γ target t₁ t₂ u d ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .reflect d', hu⟩
  · rintro Γ target t₁ t₂ u d ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .metadata d', hu⟩
  · rintro Γ target t₁ t₂ u d ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .project d', hu⟩
  · rintro Γ lower upper lt ut self inherited middle provided lu uu dl du sl su cap sh ih mh ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .mix d₁ d₂ sl su (reusableCaptures_of_le (UsesLEOn.add hu hv).le cap) sh ih mh, UsesLEOn.add hu hv⟩
  · rintro Γ spec base st inherited target su iu ds shape di sh allowed cap ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .fix d₁ shape d₂ sh (argumentAllowed_of_le hv.le allowed) (reusableCaptures_of_le hu.le cap), UsesLEOn.add hu hv⟩
  · rintro Γ prim left right input output lu ru shape dl dr ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .binary shape d₁ d₂, UsesLEOn.add hu hv⟩
  · rintro Γ value zero succ result vu zu su dv dz ds safe ih₁ ih₂ ih₃ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    have validS := validContext_cons_unrestricted validΓ (type := .natural) (by rfl)
    obtain ⟨w', d₃, hw⟩ := ih₃ (⟨.natural, .unrestricted⟩ :: Δ) rfl validS
    simp only [Term.substitute, liftSubstitution_fillTerm σ closed]
    exact ⟨_, .ifZero d₁ d₂ d₃ (safeUses_of_le hw.le safe), UsesLEOn.add hu (UsesLEOn.add hv hw.tail)⟩
  · rintro Γ tag payload pt row u fuel d found pure ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .inject d' found pure, hu⟩
  · rintro Γ scrut arms row result su au ds da distinct ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute, liftSubstitution_fillTerm σ closed]
    exact ⟨_, .case d₁ d₂ (by simpa using distinct), UsesLEOn.add hu hv⟩
  · rintro Γ cond yes no result cu tu fu dc dt df ih₁ ih₂ ih₃ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    obtain ⟨w', d₃, hw⟩ := ih₃ Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .ifBool d₁ d₂ d₃, UsesLEOn.add hu (UsesLEOn.add hv hw)⟩
  · rintro Γ plan pt response u d isPlan isData ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .perform d' isPlan isData, hu⟩
  · rintro Γ value pt response result u d pure ih Δ rfl validΓ
    obtain ⟨u', d', hu⟩ := ih Δ rfl validΓ
    simp only [Term.substitute]
    exact ⟨_, .done d' pure, hu⟩
  · rintro Γ scrut arms plan response row result su au ds da pure distinct ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [Term.substitute, liftSubstitution_fillTerm σ closed]
    exact ⟨_, .effectCase d₁ d₂ pure (by simpa using distinct), UsesLEOn.add hu hv⟩
  · rintro Γ Δ rfl validΓ
    exact ⟨_, .nil _, UsesLEOn.refl _ _⟩
  · rintro Γ name body rest type row bu ru db dr pure ih₁ ih₂ Δ rfl validΓ
    obtain ⟨u', d₁, hu⟩ := ih₁ Δ rfl validΓ
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    exact ⟨_, .cons d₁ d₂ pure, UsesLEOn.add hu hv⟩
  · rintro Γ result Δ rfl validΓ
    exact ⟨_, .nil _ _, UsesLEOn.refl _ _⟩
  · rintro Γ name body rest payload row result bu ru db safe share dr ih₁ ih₂ Δ rfl validΓ
    have validB := validContext_cons_unrestricted validΓ share
    obtain ⟨u', d₁, hu⟩ := ih₁ (⟨payload, .unrestricted⟩ :: Δ) rfl validB
    obtain ⟨v', d₂, hv⟩ := ih₂ Δ rfl validΓ
    simp only [List.map_cons]
    exact ⟨_, .cons d₁ (safeUses_of_le hu.le safe) share d₂, UsesLEOn.add hu.tail hv⟩

/-- Semantic substitution for arbitrary Checked evidence: no checker-completeness or
fuel premise. Closed fillings share the template's assumptions and declared hole types. -/
public theorem checked_msubst {t : AnnotatedTerm} {Ψ : Context} (c : Checked t Ψ)
    (σ : Nat → Option AnnotatedTerm)
    (hσ : ∀ x f, σ x = some f → Scoped 0 f.term ∧ f.assumptions = t.assumptions ∧
      ∃ b : Binding, Ψ[x]? = some b ∧ ∃ d : Checked f Ψ, d.type = b.type) :
    ∃ c' : Checked (msubst σ t) Ψ, c'.type = c.type ∧ UsesLE c'.uses c.uses := by
  have fillings : ∀ x f, σ x = some f → ∃ (b : Binding) (u : Uses),
      Ψ[x]? = some b ∧ PartialTyping t.assumptions Ψ f.term b.type u := by
    intro x f found
    obtain ⟨_, same, b, hb, d, hd⟩ := hσ x f found
    refine ⟨b, d.uses, hb, ?_⟩
    simpa only [AnnotatedTerm.erase, same, hd] using d.derivation
  obtain ⟨u, derivation, le⟩ := partialTyping_msubst c.derivation Ψ σ
    (fun x f found => (hσ x f found).1) fillings [] rfl c.contextValid
  exact ⟨⟨c.type, u, derivation, safeUses_of_le le.le c.safe, c.contextValid, c.assumptionsValid⟩, rfl, le.le⟩

end Obend.Core.Proofs.TypedSubstitution
