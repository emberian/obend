module
/- Linear resource conservation (lane Sound, 2026-11-01).

A source `Step` from a well-typed term never changes how often it uses a `linear` hypothesis:
`step_conserves_linear`. The context is the custody the term holds; a `linear` hypothesis is one
the term must consume exactly once. The count is `occurrences` (every derivation computes it,
`uses_determined`), so the theorem needs the derivation of the term before the step only. -/
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Proofs.Preservation.Cases.Functions
import all Obend.Core.Check

namespace Obend.Core.Proofs.Conservation
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences fieldOccurrences armOccurrences uses_determined)
set_option autoImplicit false

/-- Position `j` of the context holds a `linear` hypothesis. -/
@[expose] public def LinearAt (context : Context) (j : Nat) : Prop :=
  ∃ binding, context[j]? = some binding ∧ binding.quantity = .linear

/-! ### Lists of counts -/

theorem getD_zipWith {f : Nat → Nat → Nat} (zero : f 0 0 = 0) :
    ∀ (x y : List Nat), x.length = y.length → ∀ j, (List.zipWith f x y).getD j 0 = f (x.getD j 0) (y.getD j 0)
  | [], [], _, _ => by simp [zero]
  | a :: x, b :: y, h, 0 => by simp
  | a :: x, b :: y, h, j + 1 => by
    simpa using getD_zipWith zero x y (by simpa using h) j
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h

theorem getD_addUses {x y : Uses} (h : x.length = y.length) (j : Nat) :
    (addUses x y).getD j 0 = x.getD j 0 + y.getD j 0 := getD_zipWith rfl x y h j

theorem getD_joinUses {x y : Uses} (h : x.length = y.length) (j : Nat) :
    (joinUses x y).getD j 0 = max (x.getD j 0) (y.getD j 0) := getD_zipWith (by simp) x y h j

theorem getD_replicate_zero (n j : Nat) : (List.replicate n 0).getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem getD_zeroUses (context : Context) (j : Nat) : (zeroUses context).getD j 0 = 0 :=
  getD_replicate_zero _ j

theorem getD_tail (x : Uses) (j : Nat) : x.tail.getD j 0 = x.getD (j + 1) 0 := by
  cases x <;> simp

theorem linearAt_cons {binding : Binding} {context : Context} {j : Nat} :
    LinearAt (binding :: context) (j + 1) ↔ LinearAt context j := by
  simp [LinearAt]

/-- A `linearFree` usage vector uses no `linear` hypothesis. -/
theorem linearFree_getD : ∀ {context : Context} {uses : Uses}, linearFree context uses = true →
    ∀ {j}, LinearAt context j → uses.getD j 0 = 0
  | [], _, _, j, ⟨_, h, _⟩ => by simp at h
  | _ :: _, [], _, _, _ => by simp
  | b :: context, count :: uses, free, 0, ⟨b', h, lin⟩ => by
    simp at h; subst h
    simp [linearFree, lin] at free
    simpa using free.1
  | b :: context, count :: uses, free, j + 1, lin => by
    simp [linearFree] at free
    simpa using linearFree_getD (context := context) (uses := uses) (by simpa [linearFree] using free.2)
      (linearAt_cons.mp lin)

/-- Branches that agree count every `linear` hypothesis equally. -/
theorem branchesAgree_getD : ∀ {context : Context} {x y : Uses}, branchesAgree context x y = true →
    x.length = context.length → y.length = context.length →
    ∀ {j}, LinearAt context j → x.getD j 0 = y.getD j 0
  | [], _, _, _, _, _, j, ⟨_, h, _⟩ => by simp at h
  | _ :: _, [], _, _, hx, _, _, _ => by simp at hx
  | _ :: _, _ :: _, [], _, _, hy, _, _ => by simp at hy
  | b :: context, a :: x, c :: y, agree, hx, hy, 0, ⟨b', h, lin⟩ => by
    simp at h; subst h
    simp [branchesAgree, Quantity.agrees, lin] at agree
    simpa using agree.1
  | b :: context, a :: x, c :: y, agree, hx, hy, j + 1, lin => by
    simp [branchesAgree] at agree
    simpa using branchesAgree_getD agree.2 (by simpa using hx) (by simpa using hy) (linearAt_cons.mp lin)

/-! ### Occurrence counts of raw terms -/

mutual
theorem occurrences_length (n : Nat) : (t : Term) → (occurrences n t).length = n
  | .bound _ => by simp [occurrences]
  | .nat _ | .boolean _ | .label _ | .hole _ _ => by simp [occurrences]
  | .lam body => by simp [occurrences, occurrences_length (n + 1) body]
  | .app a b | .binary _ a b | .specification a b | .prototype a b | .mix a b | .fix a b => by
    simp [occurrences, addUses, occurrences_length n a, occurrences_length n b]
  | .get t _ | .reflect t | .metadata t | .project t | .inject _ t | .perform t | .done t => by
    simp [occurrences, occurrences_length n t]
  | .record fields => by simp [occurrences, fieldOccurrences_length n fields]
  | .extend target fields => by
    simp [occurrences, addUses, occurrences_length n target, fieldOccurrences_length n fields]
  | .ifZero v z s => by
    simp [occurrences, addUses, joinUses, occurrences_length n v, occurrences_length n z,
      occurrences_length (n + 1) s]
  | .case s arms => by
    simp [occurrences, addUses, occurrences_length n s, armOccurrences_length n arms]
  | .ifBool c t f => by
    simp [occurrences, addUses, joinUses, occurrences_length n c, occurrences_length n t,
      occurrences_length n f]
theorem fieldOccurrences_length (n : Nat) : (fields : List (String × Term)) → (fieldOccurrences n fields).length = n
  | [] => by simp [fieldOccurrences]
  | (_, body) :: rest => by
    simp [fieldOccurrences, addUses, occurrences_length n body, fieldOccurrences_length n rest]
theorem armOccurrences_length (n : Nat) : (arms : List (String × Term)) → (armOccurrences n arms).length = n
  | [] => by simp [armOccurrences]
  | (_, body) :: rest => by
    simp [armOccurrences, joinUses, occurrences_length (n + 1) body, armOccurrences_length n rest]
end

theorem getD_indicator (n k i : Nat) :
    ((List.range n).map (fun p => if p = k then 1 else 0)).getD i 0 = if i < n ∧ i = k then 1 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases h : i < n <;> simp [h]

theorem getD_variableUses (context : Context) (k i : Nat) :
    (variableUses context k).getD i 0 = if i < context.length ∧ i = k then 1 else 0 :=
  getD_indicator _ _ _

theorem getD_occurrences_bound (n k i : Nat) :
    (occurrences n (.bound k)).getD i 0 = if i < n ∧ i = k then 1 else 0 := by
  simp only [occurrences]; exact getD_indicator _ _ _

theorem getD_occurrences_literal (n i : Nat) (t : Term) (literal : ∀ n, occurrences n t = List.replicate n 0) :
    (occurrences n t).getD i 0 = 0 := by rw [literal]; exact getD_replicate_zero n i

/-! ### Counting through a substitution

`t.substitute σ`, where `σ` puts `A` at index `d`, keeps the indices below and closes the gap above,
counts hypothesis `j` of the shrunk context as `t` counted its image `skipAt d j`, plus `A`'s count
once for every use of `d`. Exact at every `linear` position: at a join, both branches count a `linear`
hypothesis equally, and either the substituted binder is `linear` (so they count it equally too) or
`A` uses no `linear` hypothesis. -/

/-- The position in the larger context of position `j` of the context with `d` erased. -/
@[expose] public def skipAt (d j : Nat) : Nat := if j < d then j else j + 1

/-- `σ` substitutes `A` at `d`. -/
@[expose] public def SubstAt (σ : Nat → Term) (d : Nat) (A : Term) : Prop :=
  ∀ k, σ k = if k < d then .bound k else if k = d then A else .bound (k - 1)

theorem substAt_instantiate (A : Term) :
    SubstAt (fun index => match index with | 0 => A | n + 1 => .bound n) 0 A := by
  intro k; cases k <;> simp

theorem substAt_lift {σ : Nat → Term} {d : Nat} {A : Term} (h : SubstAt σ d A) :
    SubstAt (liftSubstitution σ) (d + 1) (A.rename Nat.succ) := by
  intro k
  cases k with
  | zero => simp [liftSubstitution]
  | succ k =>
    simp only [liftSubstitution, h k]
    by_cases lt : k < d
    · simp [lt, Term.rename, show k + 1 < d + 1 by omega]
    · by_cases eq : k = d
      · subst eq; simp
      · simp [lt, eq, Term.rename, show ¬ k + 1 < d + 1 by omega, show k + 1 ≠ d + 1 by omega]; omega

theorem eraseIdx_getElem? (context : Context) (d j : Nat) :
    (context.eraseIdx d)[j]? = context[skipAt d j]? := by
  rw [List.getElem?_eraseIdx]; unfold skipAt; split <;> rfl

theorem linearAt_skip {context : Context} {d j : Nat} (h : LinearAt (context.eraseIdx d) j) :
    LinearAt context (skipAt d j) := by
  obtain ⟨b, hb, q⟩ := h; exact ⟨b, by rw [← eraseIdx_getElem?]; exact hb, q⟩

/-- What the substituted term counts at `j`, read off the original usage vector. -/
@[expose] public def Image (d : Nat) (ua : Uses) (uses : Uses) (j : Nat) : Nat :=
  uses.getD (skipAt d j) 0 + uses.getD d 0 * ua.getD j 0

/-- The substitution's data: `A` checks in the shrunk context, and either the binder at `d` is
`linear` or `A` uses no `linear` hypothesis. -/
structure Sub (a : Assumptions) (context : Context) (d : Nat) (σ : Nat → Term) (A : Term) (ua : Uses) : Prop where
  binding : ∃ b, context[d]? = some b ∧ (b.quantity = .linear ∨ linearFree (context.eraseIdx d) ua = true)
  subst : SubstAt σ d A
  arg : ∃ TA, PartialTyping a (context.eraseIdx d) A TA ua

theorem Sub.lift {a : Assumptions} {context : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : Sub a context d σ A ua) (x : Binding) (valid : validContext a.shareableVariables [x] = true) :
    Sub a (x :: context) (d + 1) (liftSubstitution σ) (A.rename Nat.succ) (0 :: ua) := by
  obtain ⟨b, hb, hq⟩ := S.binding
  obtain ⟨TA, hA⟩ := S.arg
  refine ⟨⟨b, by simpa using hb, ?_⟩, substAt_lift S.subst, ⟨TA, ?_⟩⟩
  · rcases hq with q | free
    · exact .inl q
    · right; simpa [linearFree] using free
  · simpa using Obend.Core.Proofs.Preservation.source_weaken hA x valid

theorem image_add {d : Nat} {ua x y : Uses} (h : x.length = y.length) (j : Nat) :
    Image d ua (addUses x y) j = Image d ua x j + Image d ua y j := by
  simp only [Image, getD_addUses h, Nat.add_mul]; omega

theorem image_zero {d : Nat} {ua : Uses} (context : Context) (j : Nat) :
    Image d ua (zeroUses context) j = 0 := by
  simp only [Image, getD_zeroUses, Nat.zero_mul, Nat.add_zero]

theorem image_tail {d : Nat} {ua x : Uses} (j : Nat) :
    Image (d + 1) (0 :: ua) x (j + 1) = Image d ua x.tail j := by
  simp only [Image, getD_tail, skipAt, List.getD_cons_succ]
  congr 2; split <;> split <;> omega

theorem image_join {a : Assumptions} {context : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua x y : Uses}
    (S : Sub a context d σ A ua) (hx : x.length = context.length) (hy : y.length = context.length)
    (agree : branchesAgree context x y = true) {j : Nat} (lin : LinearAt (context.eraseIdx d) j) :
    Image d ua (joinUses x y) j = max (Image d ua x j) (Image d ua y j) := by
  have hs := branchesAgree_getD agree hx hy (linearAt_skip lin)
  obtain ⟨b, hb, hq⟩ := S.binding
  have hd : x.getD d 0 = y.getD d 0 ∨ ua.getD j 0 = 0 := by
    rcases hq with q | free
    · exact .inl (branchesAgree_getD agree hx hy ⟨b, hb, q⟩)
    · exact .inr (linearFree_getD free lin)
  simp only [Image, getD_joinUses (hx.trans hy.symm), hs]
  rcases hd with e | e
  · rw [e]; simp
  · rw [e]; simp

theorem occ_add (n : Nat) (s t : Term) (j : Nat) :
    (addUses (occurrences n s) (occurrences n t)).getD j 0 = (occurrences n s).getD j 0 + (occurrences n t).getD j 0 :=
  getD_addUses ((occurrences_length n s).trans (occurrences_length n t).symm) j

theorem lt_of_linearAt {context : Context} {j : Nat} (h : LinearAt context j) : j < context.length := by
  obtain ⟨b, hb, _⟩ := h; exact (List.getElem?_eq_some_iff.mp hb).1

theorem image_joinZero {d : Nat} {ua x : Uses} (context : Context) (hx : x.length = context.length) (j : Nat) :
    Image d ua (joinUses x (zeroUses context)) j = Image d ua x j := by
  have h : x.length = (zeroUses context).length := by simp [zeroUses, hx]
  simp only [Image]
  rw [getD_joinUses h, getD_joinUses h, getD_zeroUses, getD_zeroUses, Nat.max_zero, Nat.max_zero]

theorem occ_join (n : Nat) (x y : Uses) (hx : x.length = n) (hy : y.length = n) (j : Nat) :
    (joinUses x y).getD j 0 = max (x.getD j 0) (y.getD j 0) := getD_joinUses (hx.trans hy.symm) j

theorem ind_eq {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then 1 else 0 : Nat) = if Q then 1 else 0 := by
  by_cases p : P
  · rw [if_pos p, if_pos (h.mp p)]
  · rw [if_neg p, if_neg (fun q => p (h.mpr q))]

theorem image_bound {a : Assumptions} {context : Context} {d : Nat} {σ : Nat → Term} {A : Term} {ua : Uses}
    (S : Sub a context d σ A ua) {k : Nat} (hk : k < context.length) {j : Nat}
    (lin : LinearAt (context.eraseIdx d) j) :
    (occurrences (context.eraseIdx d).length (σ k)).getD j 0 = Image d ua (variableUses context k) j := by
  obtain ⟨b, hb, _⟩ := S.binding
  obtain ⟨TA, hA⟩ := S.arg
  have hd : d < context.length := (List.getElem?_eq_some_iff.mp hb).1
  have hj := lt_of_linearAt lin
  have len : (context.eraseIdx d).length = context.length - 1 := by simp [List.length_eraseIdx, hd]
  have hsk : skipAt d j < context.length := by unfold skipAt; split <;> omega
  simp only [Image, getD_variableUses, S.subst k]
  by_cases lt : k < d
  · have z : ¬ (d < context.length ∧ d = k) := by omega
    rw [if_pos lt, getD_occurrences_bound, if_neg z, Nat.zero_mul, Nat.add_zero]
    exact ind_eq (by unfold skipAt; constructor <;> intro h <;> split at * <;> omega)
  · by_cases eq : k = d
    · subst eq
      have z : ¬ (skipAt k j < context.length ∧ skipAt k j = k) := by unfold skipAt; split <;> omega
      rw [if_neg lt, if_pos rfl, if_neg z, if_pos ⟨hd, rfl⟩, Nat.zero_add, Nat.one_mul, ← uses_determined hA]
    · have z : ¬ (d < context.length ∧ d = k) := by omega
      rw [if_neg lt, if_neg eq, getD_occurrences_bound, if_neg z, Nat.zero_mul, Nat.add_zero]
      exact ind_eq (by unfold skipAt; constructor <;> intro h <;> split at * <;> omega)

/-- **Counting through a substitution.** -/
theorem subst_counts {a : Assumptions} {context : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a context t T u) :
    ∀ d σ A ua, Sub a context d σ A ua → ∀ j, LinearAt (context.eraseIdx d) j →
      (occurrences (context.eraseIdx d).length (t.substitute σ)).getD j 0 = Image d ua u j := by
  apply PartialTyping.rec
    (motive_1 := fun context t _ u _ => ∀ d σ A ua, Sub a context d σ A ua → ∀ j, LinearAt (context.eraseIdx d) j →
      (occurrences (context.eraseIdx d).length (t.substitute σ)).getD j 0 = Image d ua u j)
    (motive_2 := fun context fields _ u _ => ∀ d σ A ua, Sub a context d σ A ua → ∀ j, LinearAt (context.eraseIdx d) j →
      (fieldOccurrences (context.eraseIdx d).length (fields.map fun field => (field.1, field.2.substitute σ))).getD j 0 =
        Image d ua u j)
    (motive_3 := fun context _ arms _ _ u _ => ∀ d σ A ua, Sub a context d σ A ua → ∀ j, LinearAt (context.eraseIdx d) j →
      (armOccurrences (context.eraseIdx d).length
        (arms.map fun field => (field.1, field.2.substitute (liftSubstitution σ)))).getD j 0 = Image d ua u j)
    (t := typed)
  case bound =>
    intro context index binding found d σ A ua S j lin
    simp only [Term.substitute]
    exact image_bound S (List.getElem?_eq_some_iff.mp found).1 lin
  case natural =>
    intro context value d σ A ua S j lin
    simp only [Term.substitute, image_zero]; exact getD_replicate_zero _ _
  case boolean =>
    intro context value d σ A ua S j lin
    simp only [Term.substitute, image_zero]; exact getD_replicate_zero _ _
  case label =>
    intro context value d σ A ua S j lin
    simp only [Term.substitute, image_zero]; exact getD_replicate_zero _ _
  case lambda =>
    intro context body annotation uses bodyTyped safe valid captures fits ih d σ A ua S j lin
    have vx : validContext a.shareableVariables [⟨annotation.domain, annotation.parameter⟩] = true := by
      simp only [validContext, List.all_cons, List.all_nil, Bool.and_true] at valid ⊢; exact (Bool.and_eq_true_iff.mp valid).1
    have h := ih (d + 1) _ _ _ (S.lift _ vx) (j + 1) (by simpa using linearAt_cons.mpr lin)
    simp only [List.eraseIdx_cons_succ, List.length_cons] at h
    simp only [Term.substitute, occurrences, getD_tail, h, image_tail]
  case conversion =>
    intro context term actual expected uses prior agreement ih d σ A ua S j lin
    exact ih d σ A ua S j lin
  case application =>
    intro context fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped callableEq same allowed ihFn ihArg d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [occ_add, image_add ((source_uses_length fnTyped).trans (source_uses_length argTyped).symm),
      ihFn d σ A ua S j lin, ihArg d σ A ua S j lin]
  case record =>
    intro context fields row uses fieldsTyped ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    exact ih d σ A ua S j lin
  case get =>
    intro context target targetType member uses name fuel targetTyped lookup free ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case extend =>
    intro context target fields targetType row tu fu rowFuel targetTyped fieldsTyped isRow free ihTarget ihFields d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm),
      image_add ((source_uses_length targetTyped).trans (source_uses_length (PartialTyping.record fieldsTyped)).symm),
      ihTarget d σ A ua S j lin, ihFields d σ A ua S j lin]
  case specification =>
    intro context metadata extension metadataType extensionType mu eu metadataTyped extensionTyped mPure ePure free ihM ihE d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [occ_add, image_add ((source_uses_length metadataTyped).trans (source_uses_length extensionTyped).symm),
      ihM d σ A ua S j lin, ihE d σ A ua S j lin]
  case prototype =>
    intro context spec target specType targetType su tu specTyped targetTyped sPure tPure ihS ihT d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [occ_add, image_add ((source_uses_length specTyped).trans (source_uses_length targetTyped).symm),
      ihS d σ A ua S j lin, ihT d σ A ua S j lin]
  case reflect =>
    intro context target specType targetType uses prior free ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case metadata =>
    intro context target metadataType extensionType uses prior free ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case project =>
    intro context target specType targetType uses prior free ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case mix =>
    intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped lowerCallable upperCallable captures selfShare inheritedShare middleShare ihL ihU d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [occ_add, image_add ((source_uses_length lowerTyped).trans (source_uses_length upperTyped).symm),
      ihL d σ A ua S j lin, ihU d σ A ua S j lin]
  case fix =>
    intro context spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare inheritedAllowed captures ihS ihI d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [occ_add, image_add ((source_uses_length specTyped).trans (source_uses_length inheritedTyped).symm),
      ihS d σ A ua S j lin, ihI d σ A ua S j lin]
  case binary =>
    intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihL ihR d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [occ_add, image_add ((source_uses_length leftTyped).trans (source_uses_length rightTyped).symm),
      ihL d σ A ua S j lin, ihR d σ A ua S j lin]
  case ifZero =>
    intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe agreeing ihV ihZ ihS d σ A ua S j lin
    have vx : validContext a.shareableVariables [⟨.natural, .unrestricted⟩] = true := by
      simp [validContext, Ty.shareableUnder, Ty.shareable]
    have hs := ihS (d + 1) _ _ _ (S.lift _ vx) (j + 1) (by simpa using linearAt_cons.mpr lin)
    simp only [List.eraseIdx_cons_succ, List.length_cons] at hs
    have zl := source_uses_length zeroTyped
    have sl : su.tail.length = context.length := by simp [source_uses_length successorTyped]
    simp only [Term.substitute, occurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (by simp [joinUses, occurrences_length])),
      occ_join _ _ _ (occurrences_length _ _) (by simp [occurrences_length]), getD_tail, hs, image_tail,
      ihV d σ A ua S j lin, ihZ d σ A ua S j lin,
      image_add ((source_uses_length valueTyped).trans (by simp [joinUses, zl, sl])),
      image_join S zl sl agreeing lin]
  case inject =>
    intro context tag payload payloadType row uses fuel payloadTyped lookup pure ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case case =>
    intro context scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihS ihA d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (armOccurrences_length _ _).symm),
      image_add ((source_uses_length scrutineeTyped).trans (Obend.Core.Proofs.Preservation.arms_uses_length armsTyped).symm),
      ihS d σ A ua S j lin, ihA d σ A ua S j lin]
  case ifBool =>
    intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped agreeing ihC ihT ihF d σ A ua S j lin
    have tl := source_uses_length trueTyped
    have fl := source_uses_length falseTyped
    simp only [Term.substitute, occurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (by simp [joinUses, occurrences_length])),
      occ_join _ _ _ (occurrences_length _ _) (occurrences_length _ _),
      ihC d σ A ua S j lin, ihT d σ A ua S j lin, ihF d σ A ua S j lin,
      image_add ((source_uses_length conditionTyped).trans (by simp [joinUses, tl, fl])),
      image_join S tl fl agreeing lin]
  case perform =>
    intro context plan planType response uses planTyped isPlan isData ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case done =>
    intro context value planType response result uses valueTyped pure ih d σ A ua S j lin
    simp only [Term.substitute, occurrences]; exact ih d σ A ua S j lin
  case effectCase =>
    intro context scrutinee arms planType response row result su au q scrutineeTyped armsTyped pure distinct allowed ihS ihA d σ A ua S j lin
    simp only [Term.substitute, occurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (armOccurrences_length _ _).symm),
      image_add ((source_uses_length scrutineeTyped).trans (Obend.Core.Proofs.Preservation.arms_uses_length armsTyped).symm),
      ihS d σ A ua S j lin, ihA d σ A ua S j lin]
  case nil =>
    intro context d σ A ua S j lin
    simp only [List.map_nil, fieldOccurrences, image_zero]; exact getD_replicate_zero _ _
  case cons =>
    intro context name body rest type row bu ru bodyTyped restTyped pure ihBody ihRest d σ A ua S j lin
    simp only [List.map_cons, fieldOccurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm),
      image_add ((source_uses_length bodyTyped).trans (source_uses_length (PartialTyping.record restTyped)).symm),
      ihBody d σ A ua S j lin, ihRest d σ A ua S j lin]
  case nil =>
    intro context q result d σ A ua S j lin
    simp only [List.map_nil, armOccurrences, image_zero]; exact getD_replicate_zero _ _
  case cons =>
    intro context q name body rest payload row result bu ru bodyTyped safe shareable fits restTyped agreeing ihBody ihRest d σ A ua S j lin
    have vx : validContext a.shareableVariables [⟨payload, q⟩] = true := shareable
    have hb := ihBody (d + 1) _ _ _ (S.lift _ vx) (j + 1) (by simpa using linearAt_cons.mpr lin)
    simp only [List.eraseIdx_cons_succ, List.length_cons] at hb
    have bl : bu.tail.length = context.length := by simp [source_uses_length bodyTyped]
    have rl := Obend.Core.Proofs.Preservation.arms_uses_length restTyped
    simp only [List.map_cons, armOccurrences]
    rw [occ_join _ _ _ (by simp [occurrences_length]) (armOccurrences_length _ _), getD_tail, hb, image_tail,
      ihRest d σ A ua S j lin]
    cases rest with
    | nil =>
      cases restTyped
      rw [image_joinZero context bl, image_zero]; simp
    | cons first others =>
      simp only [List.isEmpty_cons, Bool.false_or] at agreeing
      rw [image_join S bl rl agreeing lin]

/-! ### Inversions, through conversion -/

/-- Close the rule cases of an inversion whose term does not match (`.lam body = t` is absurd). -/
local macro "inv_other" : tactic => `(tactic| (intros; first | trivial | (rename_i e; cases e)))

theorem lam_inv {a : Assumptions} {context : Context} {body : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a context (.lam body) T u) : ∃ (ann : LambdaAnnotation) (ub : Uses),
      PartialTyping a (⟨ann.domain, ann.parameter⟩ :: context) body ann.codomain ub ∧
      ann.parameter.fits (ub.headD 0) = true ∧
      validContext a.shareableVariables (⟨ann.domain, ann.parameter⟩ :: context) = true ∧
      sameType a (.arrow ann.reuse ann.parameter ann.domain ann.codomain) T = true ∧ u = ub.tail := by
  generalize ht : Term.lam body = t0 at h
  revert ht; revert body
  apply PartialTyping.rec
    (motive_1 := fun context t T u _ => ∀ body, Term.lam body = t → ∃ (ann : LambdaAnnotation) (ub : Uses),
      PartialTyping a (⟨ann.domain, ann.parameter⟩ :: context) body ann.codomain ub ∧
      ann.parameter.fits (ub.headD 0) = true ∧
      validContext a.shareableVariables (⟨ann.domain, ann.parameter⟩ :: context) = true ∧
      sameType a (.arrow ann.reuse ann.parameter ann.domain ann.codomain) T = true ∧ u = ub.tail)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case lambda =>
    intro context body' ann ub hb _ valid _ fits _ body e
    cases e; exact ⟨ann, ub, hb, fits, valid, sameType_refl _ _, rfl⟩
  case conversion =>
    intro context t actual expected u _ same ih body e
    obtain ⟨ann, ub, hb, fits, valid, s, eq⟩ := ih body e
    exact ⟨ann, ub, hb, fits, valid, sameType_trans s same, eq⟩
  all_goals inv_other

theorem specification_inv {a : Assumptions} {context : Context} {m e : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a context (.specification m e) T u) : ∃ mu eu,
      (∃ M, PartialTyping a context m M mu) ∧ (∃ E, PartialTyping a context e E eu) ∧
      linearFree context mu = true ∧ u = addUses mu eu := by
  generalize ht : Term.specification m e = t0 at h
  revert ht; revert m e
  apply PartialTyping.rec
    (motive_1 := fun context t _ u _ => ∀ m e, Term.specification m e = t → ∃ mu eu,
      (∃ M, PartialTyping a context m M mu) ∧ (∃ E, PartialTyping a context e E eu) ∧
      linearFree context mu = true ∧ u = addUses mu eu)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case specification =>
    intro context m' e' M E mu eu hm he _ _ free _ _ m e eq
    cases eq; exact ⟨mu, eu, ⟨M, hm⟩, ⟨E, he⟩, free, rfl⟩
  case conversion =>
    intro context t actual expected u _ _ ih m e eq; exact ih m e eq
  all_goals inv_other

theorem prototype_inv {a : Assumptions} {context : Context} {s t : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a context (.prototype s t) T u) : ∃ su tu,
      (∃ S, PartialTyping a context s S su) ∧ (∃ T', PartialTyping a context t T' tu) ∧ u = addUses su tu := by
  generalize ht : Term.prototype s t = t0 at h
  revert ht; revert s t
  apply PartialTyping.rec
    (motive_1 := fun context term _ u _ => ∀ s t, Term.prototype s t = term → ∃ su tu,
      (∃ S, PartialTyping a context s S su) ∧ (∃ T', PartialTyping a context t T' tu) ∧ u = addUses su tu)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case prototype =>
    intro context s' t' S T' su tu hs ht _ _ _ _ s t eq
    cases eq; exact ⟨su, tu, ⟨S, hs⟩, ⟨T', ht⟩, rfl⟩
  case conversion =>
    intro context term actual expected u _ _ ih s t eq; exact ih s t eq
  all_goals inv_other

theorem record_inv {a : Assumptions} {context : Context} {fields : List (String × Term)} {T : Ty} {u : Uses}
    (h : PartialTyping a context (.record fields) T u) : ∃ row, FieldsTyping a context fields row u := by
  generalize ht : Term.record fields = t0 at h
  revert ht; revert fields
  apply PartialTyping.rec
    (motive_1 := fun context term _ u _ => ∀ fields, Term.record fields = term → ∃ row, FieldsTyping a context fields row u)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case record =>
    intro context fields' row u hf _ fields eq
    cases eq; exact ⟨row, hf⟩
  case conversion =>
    intro context term actual expected u _ _ ih fields eq; exact ih fields eq
  all_goals inv_other

theorem inject_inv {a : Assumptions} {context : Context} {l : String} {p : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a context (.inject l p) T u) :
      (∃ P, PartialTyping a context p P u) ∧ ∃ row, sameType a (.variant row) T = true := by
  generalize ht : Term.inject l p = t0 at h
  revert ht; revert l p
  apply PartialTyping.rec
    (motive_1 := fun context term T u _ => ∀ l p, Term.inject l p = term →
      (∃ P, PartialTyping a context p P u) ∧ ∃ row, sameType a (.variant row) T = true)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := h)
  case inject =>
    intro context tag payload P row u fuel hp _ _ _ l p eq
    cases eq; exact ⟨⟨P, hp⟩, row, sameType_refl _ _⟩
  case conversion =>
    intro context term actual expected u _ same ih l p eq
    obtain ⟨typed, row, s⟩ := ih l p eq
    exact ⟨typed, row, sameType_trans s same⟩
  all_goals inv_other

theorem arms_find {a : Assumptions} {context : Context} {l : String} {body : Term} :
    ∀ {q : Quantity} {arms : List (String × Term)} {row result : Ty} {au : Uses}, ArmsTyping a context q arms row result au →
      arms.find? (fun arm => arm.1 == l) = some (l, body) → ∃ payload bu,
        PartialTyping a (⟨payload, q⟩ :: context) body result bu ∧
        validContext a.shareableVariables [⟨payload, q⟩] = true ∧ q.fits (bu.headD 0) = true ∧
        ∀ j, LinearAt context j → bu.tail.getD j 0 = au.getD j 0
  | _, [], _, _, _, _, found => by simp at found
  | _, (name, b) :: rest, _, _, _, typed, found => by
    cases typed with
    | @cons _ _ _ _ _ payload _ _ bu ru hb _ share fits restTyped agreeing =>
      have bl : bu.tail.length = context.length := by simp [source_uses_length hb]
      have rl := Obend.Core.Proofs.Preservation.arms_uses_length restTyped
      by_cases hn : (name == l) = true
      · simp only [List.find?_cons, hn] at found
        cases found
        refine ⟨payload, bu, hb, share, fits, fun j lin => ?_⟩
        rw [getD_joinUses (bl.trans rl.symm)]
        cases rest with
        | nil => cases restTyped; rw [getD_zeroUses, Nat.max_zero]
        | cons first others =>
          simp only [List.isEmpty_cons, Bool.false_or] at agreeing
          rw [branchesAgree_getD agreeing bl rl lin]; simp
      · simp only [List.find?_cons, hn] at found
        obtain ⟨payload', bu', hb', share', fits', counts⟩ := arms_find restTyped found
        refine ⟨payload', bu', hb', share', fits', fun j lin => ?_⟩
        rw [getD_joinUses (bl.trans rl.symm), counts j lin]
        cases rest with
        | nil => simp at found
        | cons first others =>
          simp only [List.isEmpty_cons, Bool.false_or] at agreeing
          rw [branchesAgree_getD agreeing bl rl lin]; simp

theorem fieldOcc_find (n j : Nat) {name : String} {body : Term} :
    ∀ {fields : List (String × Term)}, fields.find? (fun field => field.1 == name) = some (name, body) →
      (occurrences n body).getD j 0 ≤ (fieldOccurrences n fields).getD j 0
  | [], found => by simp at found
  | (name', b) :: rest, found => by
    simp only [fieldOccurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm)]
    by_cases hn : (name' == name) = true
    · simp only [List.find?_cons, hn] at found; cases found; omega
    · simp only [List.find?_cons, hn] at found
      have := fieldOcc_find n j found; omega

theorem fieldOcc_append (n j : Nat) : ∀ (xs ys : List (String × Term)),
    (fieldOccurrences n (xs ++ ys)).getD j 0 = (fieldOccurrences n xs).getD j 0 + (fieldOccurrences n ys).getD j 0
  | [], ys => by simp only [List.nil_append, fieldOccurrences]; rw [getD_replicate_zero]; simp
  | (_, b) :: xs, ys => by
    simp only [List.cons_append, fieldOccurrences]
    rw [getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm),
      getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm), fieldOcc_append n j xs ys]
    omega

theorem fieldOcc_filter (n j : Nat) (p : String × Term → Bool) : ∀ (xs : List (String × Term)),
    (fieldOccurrences n (xs.filter p)).getD j 0 ≤ (fieldOccurrences n xs).getD j 0
  | [] => by simp
  | (name, b) :: xs => by
    have ih := fieldOcc_filter n j p xs
    by_cases hp : p (name, b) = true
    · simp only [List.filter_cons, hp, if_true, fieldOccurrences]
      rw [getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm),
        getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm)]
      omega
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ite_false, fieldOccurrences]
      rw [getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm)]
      omega

theorem primitive_literals {p : Primitive} {l r res : Term} (h : primitiveResult p l r = some res) (n j : Nat) :
    (occurrences n l).getD j 0 = 0 ∧ (occurrences n r).getD j 0 = 0 ∧ (occurrences n res).getD j 0 = 0 := by
  unfold primitiveResult at h
  split at h <;> (try cases h) <;> simp only [occurrences, getD_replicate_zero, and_self]

theorem le_getD_of_add {x y : Uses} (h : x.length = y.length) (j : Nat) :
    x.getD j 0 ≤ (addUses x y).getD j 0 ∧ y.getD j 0 ≤ (addUses x y).getD j 0 := by
  rw [getD_addUses h]; omega

/-! ### Occurrence counts of each form, pointwise -/

theorem occ_app (n j : Nat) (x y : Term) :
    (occurrences n (.app x y)).getD j 0 = (occurrences n x).getD j 0 + (occurrences n y).getD j 0 := by
  simp only [occurrences]; exact occ_add n x y j

theorem occ_binary (n j : Nat) (p : Primitive) (x y : Term) :
    (occurrences n (.binary p x y)).getD j 0 = (occurrences n x).getD j 0 + (occurrences n y).getD j 0 := by
  simp only [occurrences]; exact occ_add n x y j

theorem occ_fix (n j : Nat) (x y : Term) :
    (occurrences n (.fix x y)).getD j 0 = (occurrences n x).getD j 0 + (occurrences n y).getD j 0 := by
  simp only [occurrences]; exact occ_add n x y j

theorem occ_prototype (n j : Nat) (x y : Term) :
    (occurrences n (.prototype x y)).getD j 0 = (occurrences n x).getD j 0 + (occurrences n y).getD j 0 := by
  simp only [occurrences]; exact occ_add n x y j

theorem occ_extend (n j : Nat) (x : Term) (fields : List (String × Term)) :
    (occurrences n (.extend x fields)).getD j 0 = (occurrences n x).getD j 0 + (fieldOccurrences n fields).getD j 0 := by
  simp only [occurrences]; exact getD_addUses ((occurrences_length _ _).trans (fieldOccurrences_length _ _).symm) j

theorem occ_case (n j : Nat) (x : Term) (arms : List (String × Term)) :
    (occurrences n (.case x arms)).getD j 0 = (occurrences n x).getD j 0 + (armOccurrences n arms).getD j 0 := by
  simp only [occurrences]; exact getD_addUses ((occurrences_length _ _).trans (armOccurrences_length _ _).symm) j

theorem occ_ifZero (n j : Nat) (v z s : Term) :
    (occurrences n (.ifZero v z s)).getD j 0 =
      (occurrences n v).getD j 0 + max ((occurrences n z).getD j 0) ((occurrences (n + 1) s).getD (j + 1) 0) := by
  simp only [occurrences]
  rw [getD_addUses ((occurrences_length _ _).trans (by simp [joinUses, occurrences_length])),
    getD_joinUses ((occurrences_length _ _).trans (by simp [occurrences_length])), getD_tail]

theorem occ_ifBool (n j : Nat) (c x y : Term) :
    (occurrences n (.ifBool c x y)).getD j 0 =
      (occurrences n c).getD j 0 + max ((occurrences n x).getD j 0) ((occurrences n y).getD j 0) := by
  simp only [occurrences]
  rw [getD_addUses ((occurrences_length _ _).trans (by simp [joinUses, occurrences_length])),
    getD_joinUses ((occurrences_length _ _).trans (occurrences_length _ _).symm)]

theorem occ_literal_nat (n j v : Nat) : (occurrences n (.nat v)).getD j 0 = 0 := by
  simp only [occurrences]; exact getD_replicate_zero n j

theorem occ_literal_boolean (n j : Nat) (v : Bool) : (occurrences n (.boolean v)).getD j 0 = 0 := by
  simp only [occurrences]; exact getD_replicate_zero n j

theorem linearFree_zeroUses : ∀ context : Context, linearFree context (zeroUses context) = true
  | [] => rfl
  | _ :: context => by
    have := linearFree_zeroUses context
    simp only [linearFree, zeroUses, List.length_cons, List.replicate_succ, List.zip_cons_cons, List.all_cons] at this ⊢
    simp [this]

/-- A count read through a derivation. -/
theorem occ_of {a : Assumptions} {context : Context} {t : Term} {T : Ty} {u : Uses}
    (h : PartialTyping a context t T u) (j : Nat) : (occurrences context.length t).getD j 0 = u.getD j 0 := by
  rw [← uses_determined h]

/-- Where the substituted binder is `linear` it is used exactly once; otherwise the argument uses no
`linear` hypothesis. Either way the argument's count is added once. -/
theorem image_zero_index (ua x : Uses) (j : Nat) :
    Image 0 ua x j = x.tail.getD j 0 + x.getD 0 0 * ua.getD j 0 := by
  simp [Image, skipAt, getD_tail]

theorem fits_once {q : Quantity} {ub au : Uses} {context : Context} {j : Nat}
    (fits : q.fits (ub.headD 0) = true) (allowed : q = .linear ∨ linearFree context au = true)
    (lin : LinearAt context j) : ub.getD 0 0 * au.getD j 0 = au.getD j 0 := by
  rcases allowed with q' | free
  · subst q'
    have : ub.headD 0 = 1 := by simpa [Quantity.fits] using fits
    cases ub with
    | nil => simp at this
    | cons x xs => simp at this; simp [this]
  · rw [linearFree_getD free lin]; simp

theorem variant_not_activity {a : Assumptions} {row plan response result : Ty}
    (h : sameType a (.variant row) (.computation plan response result) = true) : False := by
  have heads := TypeGraph.equivalent_head ((sameType_iff a _ _).mp h)
  simp [TypeGraph.graph, TypeGraph.observe, TypeGraph.labelHead, AliasExposure.expose,
    AliasExposure.exposeWalk, AliasExposure.constructorHead, TypeGraph.rowTag] at heads

/-- **Linear resource conservation.** A `Step` from a term that checks in `context` uses every
`linear` hypothesis of `context` exactly as often as the term did: none is dropped, none is copied.
`caseInject` is the arm applied to the payload: a scrutinee that uses a `linear` hypothesis binds the
payload `linear` (`caseAllowed`), and the arm uses it once (`Quantity.fits`).
The context is what the term holds; nothing in `Step` discharges a hypothesis (a `perform` does not
step: it yields to the kernel, which is the explicit discharge). -/
public theorem step_conserves_linear {a : Assumptions} {context : Context} {t : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a context t T u) (valid : validContext a.shareableVariables context = true)
    {t' : Term} (step : Step t t') {j : Nat} (lin : LinearAt context j) :
    (occurrences context.length t').getD j 0 = u.getD j 0 := by
  revert valid t' step j lin
  apply PartialTyping.rec
    (motive_1 := fun context t _ u _ => validContext a.shareableVariables context = true → ∀ {t'}, Step t t' →
      ∀ {j}, LinearAt context j → (occurrences context.length t').getD j 0 = u.getD j 0)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (t := typed)
  case conversion =>
    intro context term actual expected u _ _ ih valid t' step j lin
    exact ih valid step lin
  case application =>
    intro context fn arg functionType argumentType domain codomain fu au reuse quantity fnTyped argTyped
      callableEq same allowed ihFn ihArg valid t' step j lin
    have fl := source_uses_length fnTyped
    have al := source_uses_length argTyped
    rw [getD_addUses (fl.trans al.symm)]
    cases step with
    | beta body _ =>
      obtain ⟨ann, ub, hb, fits, vb, same', eq⟩ := lam_inv fnTyped
      have ft := Obend.Core.Proofs.Preservation.closure_callable_type ((sameType_iff a _ _).mp same') callableEq
      rw [ft] at same'
      obtain ⟨_, q, _, _⟩ := TypeGraph.arrow_components ((sameType_iff a _ _).mp same')
      have cond : ann.parameter = .linear ∨ linearFree context au = true := by
        rw [q]
        have : (quantity == .linear || linearFree context au) = true := by
          simp only [argumentAllowed, Bool.and_eq_true] at allowed; exact allowed.1.2
        simpa using this
      have S : Sub a (⟨ann.domain, ann.parameter⟩ :: context) 0
          (fun index => match index with | 0 => arg | n + 1 => .bound n) arg au :=
        ⟨⟨_, rfl, by simpa using cond⟩, substAt_instantiate _, ⟨_, by simpa using argTyped⟩⟩
      have h := subst_counts hb 0 _ _ _ S j (by simpa using lin)
      simp only [List.eraseIdx_cons_zero] at h
      have h' : (occurrences context.length (instantiate body arg)).getD j 0 = Image 0 au ub j := h
      rw [h', image_zero_index, fits_once fits cond lin, eq]
    | application argument s' =>
      rw [occ_app, ihFn valid s' lin, occ_of argTyped]
    | applySpecification m e argument =>
      obtain ⟨mu, eu, ⟨M, hm⟩, ⟨E, he⟩, free, rfl⟩ := specification_inv fnTyped
      rw [occ_app, occ_of he, occ_of argTyped,
        getD_addUses ((source_uses_length hm).trans (source_uses_length he).symm), linearFree_getD free lin]
      omega
  case get =>
    intro context target targetType member uses name fuel targetTyped lookup free ih valid t' step j lin
    cases step with
    | target _ s' => simp only [occurrences]; exact ih valid s' lin
    | field fields _ body found =>
      have le := fieldOcc_find context.length j found
      have total := occ_of targetTyped j
      simp only [occurrences] at total
      rw [linearFree_getD free lin] at total ⊢
      omega
  case extend =>
    intro context target fields targetType row tu fu rowFuel targetTyped fieldsTyped isRow free ihTarget ihFields valid t' step j lin
    have fieldsOcc := occ_of (PartialTyping.record fieldsTyped) j
    simp only [occurrences] at fieldsOcc
    rw [getD_addUses ((source_uses_length targetTyped).trans (source_uses_length (PartialTyping.record fieldsTyped)).symm)]
    cases step with
    | extendTarget _ s' => rw [occ_extend, ihTarget valid s' lin, fieldsOcc]
    | extendRecord inherited _ =>
      have targetOcc := occ_of targetTyped j
      simp only [occurrences] at targetOcc
      rw [linearFree_getD free lin] at targetOcc ⊢
      simp only [occurrences, extendFields]
      rw [fieldOcc_append, fieldsOcc]
      have := fieldOcc_filter context.length j (fun prior => !(fields.any fun field => field.1 == prior.1)) inherited
      omega
  case reflect =>
    intro context target specType targetType uses prior free ih valid t' step j lin
    cases step with
    | reflectPrototype spec target' =>
      obtain ⟨su, tu, ⟨S, hs⟩, ⟨T', ht⟩, rfl⟩ := prototype_inv prior
      have := (le_getD_of_add ((source_uses_length hs).trans (source_uses_length ht).symm) j).1
      rw [occ_of hs, linearFree_getD free lin] at *; omega
    | reflectStep s' => simp only [occurrences]; exact ih valid s' lin
  case metadata =>
    intro context target metadataType extensionType uses prior free ih valid t' step j lin
    cases step with
    | metadataSpecification m e =>
      obtain ⟨mu, eu, ⟨M, hm⟩, ⟨E, he⟩, mfree, rfl⟩ := specification_inv prior
      rw [occ_of hm, linearFree_getD mfree lin, linearFree_getD free lin]
    | metadataStep s' => simp only [occurrences]; exact ih valid s' lin
  case project =>
    intro context target specType targetType uses prior free ih valid t' step j lin
    cases step with
    | projectPrototype spec target' =>
      obtain ⟨su, tu, ⟨S, hs⟩, ⟨T', ht⟩, rfl⟩ := prototype_inv prior
      have := (le_getD_of_add ((source_uses_length hs).trans (source_uses_length ht).symm) j).2
      rw [occ_of ht, linearFree_getD free lin] at *; omega
    | projectStep s' => simp only [occurrences]; exact ih valid s' lin
  case mix =>
    intro context lower upper lowerType upperType self inherited middle provided lu uu lowerTyped upperTyped
      lowerCallable upperCallable captures selfShare inheritedShare middleShare ihL ihU valid t' step j lin
    cases step with
    | mix =>
      let R := Obend.Core.Proofs.Preservation.reusable_mix_body lowerTyped upperTyped lowerCallable upperCallable
        captures selfShare inheritedShare middleShare valid
      rw [occ_of R.derivation, linearFree_getD (linearFree_of_reusableCaptures R.captures) lin,
        linearFree_getD (linearFree_of_reusableCaptures captures) lin]
  case fix =>
    intro context spec inheritedTerm specType inherited target su iu specTyped callableEq inheritedTyped targetShare
      inheritedAllowed captures ihS ihI valid t' step j lin
    cases step with
    | fix =>
      have ifree : linearFree context iu = true := by
        simp only [argumentAllowed, Bool.and_eq_true] at inheritedAllowed
        simpa using inheritedAllowed.1.2
      have sz := linearFree_getD (linearFree_of_reusableCaptures captures) lin
      have iz := linearFree_getD ifree lin
      rw [getD_addUses ((source_uses_length specTyped).trans (source_uses_length inheritedTyped).symm),
        occ_app, occ_app, occ_fix, occ_of specTyped, occ_of inheritedTyped, sz, iz]
  case binary =>
    intro context primitive left right input output lu ru primitiveEq leftTyped rightTyped ihL ihR valid t' step j lin
    rw [getD_addUses ((source_uses_length leftTyped).trans (source_uses_length rightTyped).symm)]
    cases step with
    | binaryLeft _ _ s' => rw [occ_binary, ihL valid s' lin, occ_of rightTyped]
    | binaryRight _ _ _ s' => rw [occ_binary, ihR valid s' lin, occ_of leftTyped]
    | primitive _ _ _ _ _ _ h =>
      obtain ⟨l0, r0, res0⟩ := primitive_literals h context.length j
      rw [← occ_of leftTyped, ← occ_of rightTyped, l0, r0, res0]
  case ifZero =>
    intro context value zero successor result vu zu su valueTyped zeroTyped successorTyped successorSafe agreeing
      ihV ihZ ihS valid t' step j lin
    have zl := source_uses_length zeroTyped
    have sl : su.tail.length = context.length := by simp [source_uses_length successorTyped]
    have agree := branchesAgree_getD agreeing zl sl lin
    rw [getD_addUses ((source_uses_length valueTyped).trans (by simp [joinUses, zl, sl])), getD_joinUses (zl.trans sl.symm)]
    cases step with
    | condition _ _ s' =>
      have hs := occ_of successorTyped (j + 1)
      simp only [List.length_cons] at hs
      rw [occ_ifZero, ihV valid s' lin, occ_of zeroTyped, hs, getD_tail]
    | zero _ _ =>
      rw [← occ_of valueTyped, occ_literal_nat, occ_of zeroTyped, agree]; simp
    | successor n _ _ =>
      have S : Sub a (⟨.natural, .unrestricted⟩ :: context) 0
          (fun index => match index with | 0 => .nat n | k + 1 => .bound k) (.nat n) (zeroUses context) :=
        ⟨⟨_, rfl, .inr (by simpa using linearFree_zeroUses context)⟩,
          substAt_instantiate _, ⟨_, by simpa using PartialTyping.natural (assumptions := a) context n⟩⟩
      have h := subst_counts successorTyped 0 _ _ _ S j (by simpa using lin)
      simp only [List.eraseIdx_cons_zero] at h
      have h' : (occurrences context.length (instantiate successor (.nat n))).getD j 0 =
        Image 0 (zeroUses context) su j := h
      rw [h', image_zero_index, getD_zeroUses, ← occ_of valueTyped, occ_literal_nat, ← agree]; simp
  case case =>
    intro context scrutinee arms row result su au q scrutineeTyped armsTyped distinct allowed ihS ihA valid t' step j lin
    have sl := source_uses_length scrutineeTyped
    have al := Obend.Core.Proofs.Preservation.arms_uses_length armsTyped
    rw [getD_addUses (sl.trans al.symm)]
    cases step with
    | caseTarget _ s' =>
      have ha : (armOccurrences context.length arms).getD j 0 = au.getD j 0 := by
        have := occ_of (PartialTyping.case scrutineeTyped armsTyped distinct allowed) j
        rw [occ_case, getD_addUses (sl.trans al.symm), occ_of scrutineeTyped] at this; omega
      rw [occ_case, ihS valid s' lin, ha]
    | caseInject l p _ body found =>
      obtain ⟨⟨P, hp⟩, _⟩ := inject_inv scrutineeTyped
      obtain ⟨payload, bu, hb, share, fits, counts⟩ := arms_find armsTyped found
      have cond : q = .linear ∨ linearFree context su = true := by
        simp only [caseAllowed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at allowed; exact allowed.1
      have S : Sub a (⟨payload, q⟩ :: context) 0
          (fun index => match index with | 0 => p | k + 1 => .bound k) p su :=
        ⟨⟨_, rfl, by simpa using cond⟩, substAt_instantiate _, ⟨_, by simpa using hp⟩⟩
      have h := subst_counts hb 0 _ _ _ S j (by simpa using lin)
      simp only [List.eraseIdx_cons_zero] at h
      have h' : (occurrences context.length (instantiate body p)).getD j 0 = Image 0 su bu j := h
      rw [h', image_zero_index, fits_once fits cond lin, counts j lin]; omega
  case ifBool =>
    intro context condition whenTrue whenFalse result cu tu fu conditionTyped trueTyped falseTyped agreeing
      ihC ihT ihF valid t' step j lin
    have tl := source_uses_length trueTyped
    have fl := source_uses_length falseTyped
    have agree := branchesAgree_getD agreeing tl fl lin
    rw [getD_addUses ((source_uses_length conditionTyped).trans (by simp [joinUses, tl, fl])), getD_joinUses (tl.trans fl.symm)]
    cases step with
    | ifCondition _ _ s' => rw [occ_ifBool, ihC valid s' lin, occ_of trueTyped, occ_of falseTyped]
    | ifTrue _ _ => rw [← occ_of conditionTyped, occ_literal_boolean, occ_of trueTyped, agree]; simp
    | ifFalse _ _ => rw [← occ_of conditionTyped, occ_literal_boolean, occ_of falseTyped, ← agree]; simp
  case done =>
    intro context value planType response result uses valueTyped pure ih valid t' step j lin
    cases step with
    | done _ => exact occ_of valueTyped j
  case effectCase =>
    intro context scrutinee arms planType response row result su au q scrutineeTyped armsTyped pure distinct allowed ihS ihA
      valid t' step j lin
    have sl := source_uses_length scrutineeTyped
    have al := Obend.Core.Proofs.Preservation.arms_uses_length armsTyped
    rw [getD_addUses (sl.trans al.symm)]
    cases step with
    | caseTarget _ s' =>
      have ha : (armOccurrences context.length arms).getD j 0 = au.getD j 0 := by
        have := occ_of (PartialTyping.effectCase scrutineeTyped armsTyped pure distinct allowed) j
        rw [occ_case, getD_addUses (sl.trans al.symm), occ_of scrutineeTyped] at this; omega
      rw [occ_case, ihS valid s' lin, ha]
    | caseInject l p _ body found =>
      obtain ⟨_, row', same⟩ := inject_inv scrutineeTyped
      exact (variant_not_activity same).elim
  all_goals (intros; first | trivial | (rename_i st _ _; cases st))

/-- Along a reduction every term of which checks in the context, every `linear` count is the
initial one. Source subject reduction is not proved here (the proved preservation is the machine's,
`typed_stepRaw_preserved`), so typing along the path is a premise. -/
public theorem steps_conserve_linear {a : Assumptions} {context : Context} {t t' : Term}
    (valid : validContext a.shareableVariables context = true) (steps : Steps t t')
    (typed : ∀ s, Steps t s → Steps s t' → ∃ T us, PartialTyping a context s T us)
    {j : Nat} (lin : LinearAt context j) :
    (occurrences context.length t').getD j 0 = (occurrences context.length t).getD j 0 := by
  induction steps with
  | refl => rfl
  | @next initial middle result step rest ih =>
    obtain ⟨T, us, h⟩ := typed initial (.refl _) (.next step rest)
    rw [ih (fun s hs hr => typed s (.next step hs) hr), step_conserves_linear h valid step lin, occ_of h]

end Obend.Core.Proofs.Conservation
