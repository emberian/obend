module
/- Contextual open-code splice (`contextual_msubst_uses`), inert hole refusal/scoping,
   resourceful aggregate contracts (`split_accounts`, `machine_split_passes_all`, `terminal_owes`),
   per-field graded `Σ⊗`/`Σ&` record conservation (`graded_sigma_tensor_conserves_linear`,
   `heap_linear_conserved`), and all-path `joinUses` reading (`Wave C2-Core`, `5 → 1`). -/
public import Obend.Core.Check
public import Obend.Core.Code
public import Obend.Core.Invariant
public import Obend.Core.Proofs.SubjectReduction
public import Obend.Core.Proofs.SubjectReduction.Substitution
public import Obend.Tactic.Cases
import all Obend.Core.Check
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution

/-! ## Consolidated from `lean/Obend/Core/Proofs/Hole.lean` -/
namespace Obend.Core.Proofs.Hole
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Invariant Obend.Core.Machine
set_option autoImplicit false

public theorem demanded_hole_refused (heap : Array Cell) (env : Environment)
    (stack : List Frame) (n : Nat) (σ : List Term) :
    stepRaw ⟨heap, .evaluate (.hole n σ) env, stack⟩ =
      ⟨heap, .refused .unresolvedHole, stack⟩ := by
  rfl

/-- Weak-head evaluation does not demand an unused argument. -/
public theorem ignored_hole_evaluates (n : Nat) (σ : List Term) :
    Evaluates (.app (.lam (.nat 7)) (.hole n σ)) (.nat 7) := by
  refine ⟨.next (.beta _ _) ?_, .natural 7⟩
  simpa [instantiate, Term.substitute] using (Steps.refl (.nat 7))

public theorem rename_hole_payload :
    (Term.hole 9 [.bound 0, .lam (.bound 1)]).rename Nat.succ =
      .hole 9 [.bound 1, .lam (.bound 2)] := by
  simp [Term.rename, liftRename]

public theorem substitute_hole_payload :
    (Term.hole 9 [.bound 0, .lam (.bound 1)]).substitute (fun _ => .nat 7) =
      .hole 9 [.nat 7, .lam (.nat 7)] := by
  simp [Term.substitute, liftSubstitution, Term.rename]

public theorem scoped_hole_payload (depth n : Nat) (σ : List Term) :
    Scoped depth (.hole n σ) ↔ ∀ t ∈ σ, Scoped depth t := by
  constructor
  · intro h
    obend_cases h with []
  · intro h
    exact .hole h

end Obend.Core.Proofs.Hole

/-! ## Consolidated from `lean/Obend/Core/Proofs/Aggregate.lean` -/
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

/-! ## Consolidated from `lean/Obend/Core/Proofs/GradedRecord.lean` -/
namespace Obend.Core.Proofs.GradedRecord
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Machine Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation
open Obend.Core.Proofs.Aggregate
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences fieldOccurrences)
set_option autoImplicit false

/-! ## 1. Per-Field Graded Record Quantities (`Σ⊗` and `Σ&`) -/

/-- A record field annotated with its own resource modality `qᵢ` (`Σ⊗` / `Σ&`). -/
public structure GradedFieldSpec where
  name : String
  quantity : Quantity
  uses : Uses
  bodyUses : Nat

/-- A per-field graded `Σ⊗` record elimination is well-graded in `context` when:
1. Every field whose grade is not `.linear` (e.g., `tag = 0` with `.unrestricted` or `.affine`) is
   `linearFree` with respect to `context` (holds no linear custody handles from `context`).
2. The split continuation uses each field `f` a number of times `f.bodyUses` compatible with its
   own grade `f.quantity.fits f.bodyUses = true`. -/
public def GradedSigmaTensor (context : Context) (specs : List GradedFieldSpec) : Prop :=
  ∀ s ∈ specs,
    (s.quantity = .linear ∨ linearFree context s.uses = true) ∧
    s.quantity.fits s.bodyUses = true

/-- Weighted linear contribution of a single graded field after substituting into the continuation:
the continuation uses the field `s.bodyUses` times, multiplying the field's own context usage `s.uses`. -/
public def gradedFieldContribution (s : GradedFieldSpec) (j : Nat) : Nat :=
  s.bodyUses * s.uses.getD j 0

/-- Raw unscaled linear contribution of a field in the record literal before elimination. -/
public def rawFieldContribution (s : GradedFieldSpec) (j : Nat) : Nat :=
  s.uses.getD j 0

/-- **Key lemma for per-field graded `Σ⊗`**: For any linear hypothesis `LinearAt context j`, a
well-graded field `s` contributes the exact same linear count `s.uses.getD j 0` after substitution
into the continuation (`s.bodyUses * s.uses.getD j 0`) as in the record literal itself, regardless
of whether `s.quantity` is `.linear`, `.affine` (dropped `0` times), or `.unrestricted` (duplicated
`k` times). Shareable siblings (`tag = 0`) never need to be consumed linearly! -/
public theorem graded_field_conserves_linear {context : Context} {s : GradedFieldSpec}
    (hAllowed : s.quantity = .linear ∨ linearFree context s.uses = true)
    (hFits : s.quantity.fits s.bodyUses = true)
    {j : Nat} (lin : LinearAt context j) :
    gradedFieldContribution s j = rawFieldContribution s j := by
  unfold gradedFieldContribution rawFieldContribution
  rcases hAllowed with hLin | hFree
  · rw [hLin] at hFits
    have hOne : s.bodyUses = 1 := by simpa [Quantity.fits] using hFits
    rw [hOne, Nat.one_mul]
  · rw [linearFree_getD hFree lin, Nat.mul_zero]

/-- **Per-field graded `Σ⊗` conservation (`graded_sigma_tensor_conserves_linear`)**:
Across any list of per-field graded record components `specs` satisfying `GradedSigmaTensor`, the sum
of weighted field occurrences in the split continuation equals the sum of raw field occurrences in the
record literal at every `LinearAt context j` position. -/
public theorem graded_sigma_tensor_conserves_linear {context : Context} {specs : List GradedFieldSpec}
    (hGraded : GradedSigmaTensor context specs) {j : Nat} (lin : LinearAt context j) :
    (specs.map (fun s => gradedFieldContribution s j)).sum =
      (specs.map (fun s => rawFieldContribution s j)).sum := by
  induction specs with
  | nil => rfl
  | cons s rest ih =>
    have hs := hGraded s List.mem_cons_self
    have hrest : GradedSigmaTensor context rest :=
      fun s' hs' => hGraded s' (List.mem_cons_of_mem _ hs')
    simp only [List.map_cons, List.sum_cons]
    rw [graded_field_conserves_linear hs.1 hs.2 lin, ih hrest]

/-- Concrete witness: `{held = h, tag = 0}` where `held` has grade `.linear` (`bodyUses = 1`) and
`tag` has grade `.unrestricted` (`bodyUses = 0`, dropped by the continuation, or `bodyUses = 3`,
duplicated by the continuation) conserves the linear handle `h` at context index `0`. -/
public theorem held_and_shareable_tag_example (tagUses : Nat) :
    let ctx : Context := [⟨.custody 0, .linear⟩]
    let heldSpec : GradedFieldSpec := ⟨"held", .linear, [1], 1⟩
    let tagSpec : GradedFieldSpec := ⟨"tag", .unrestricted, [0], tagUses⟩
    GradedSigmaTensor ctx [heldSpec, tagSpec] ∧
      ([heldSpec, tagSpec].map (fun s => gradedFieldContribution s 0)).sum =
        ([heldSpec, tagSpec].map (fun s => rawFieldContribution s 0)).sum := by
  intro ctx heldSpec tagSpec
  have hGraded : GradedSigmaTensor ctx [heldSpec, tagSpec] := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨.inl rfl, rfl⟩
    · exact ⟨.inr rfl, rfl⟩
  refine ⟨hGraded, graded_sigma_tensor_conserves_linear hGraded ⟨⟨.custody 0, .linear⟩, rfl, rfl⟩⟩

/-- **Additive `Σ&` record projection (`graded_sigma_with_get_conserves_linear`)**:
When a record is eliminated via additive projection `Term.get (.record fields) name`, if every field
is `linearFree` in `context` (an additive `Σ&` record of shareable/droppable components), projecting
any field `body` conserves `0` linear uses for every `LinearAt context j`. -/
public theorem graded_sigma_with_get_conserves_linear {a : Assumptions} {context : Context}
    {fields : List (String × Term)} {name : String} {body : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a context (.get (.record fields) name) T u)
    (valid : validContext a.shareableVariables context = true)
    (found : fields.find? (fun f => f.1 == name) = some (name, body))
    {j : Nat} (lin : LinearAt context j) :
    (occurrences context.length body).getD j 0 = u.getD j 0 ∧ u.getD j 0 = 0 := by
  refine ⟨step_conserves_linear typed valid (.field fields name body found) lin,
    linearFree_getD (get_target_linearFree typed) lin⟩

/-! ## 2. Machine-Level Heap-Address Linear Conservation (`heap_linear_conserved`) -/

/-- Count how many times heap address `a` appears in an address list. -/
public def addressCount (a : Address) (addrs : List Address) : Nat :=
  addrs.count a

/-- Extract the target indirection addresses from a stack prefix of destructor argument frames
`splitFrames indirectionAddrs`. -/
public def frameAddresses : List Frame → List Address
  | [] => []
  | .argument (.bound 0) [addr] :: rest => addr :: frameAddresses rest
  | _ :: rest => frameAddresses rest

public theorem frameAddresses_splitFrames (addrs : List Address) :
    frameAddresses (splitFrames addrs) = addrs := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    simp only [splitFrames, List.map_cons, frameAddresses]
    rw [← splitFrames, ih]

/-- Permutations preserve `addressCount` for every heap address `a`. -/
public theorem Perm.addressCount_eq {xs ys : List Address} (h : xs.Perm ys) (a : Address) :
    addressCount a xs = addressCount a ys :=
  List.Perm.count_eq h a

/-- In a duplicate-free list of heap addresses (such as distinct linear cell allocations), every
member address has exact reference count `1`. -/
public theorem addressCount_eq_one_of_nodup_mem {addrs : List Address} {a : Address}
    (hNodup : addrs.Nodup) (hMem : a ∈ addrs) :
    addressCount a addrs = 1 := by
  unfold addressCount
  induction addrs with
  | nil => cases hMem
  | cons x xs ih =>
    simp only [List.nodup_cons] at hNodup
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hMem
    · rw [List.count_cons_self]
      have hzero : xs.count a = 0 := List.count_eq_zero.mpr hNodup.1
      omega
    · have hne : x ≠ a := fun h => hNodup.1 (h ▸ hMem)
      rw [List.count_cons_of_ne hne]
      exact ih hNodup.2 hMem

/-- **`heap_linear_conserved` (Machine-Level Heap-Address Linear Conservation)**:
When the machine executes a `.split` destructor step on a record `.record fields` with distinct field
labels and a covering name list `names` (`splitValues fields names = some addresses`):
1. The machine transitions to `machine_split_step` with `allocated := allocateFields heap addresses (splitCells addresses.length)`.
2. The number of indirection argument frames pushed onto the stack equals the number of record fields (`addresses.length = fields.length`).
3. For every heap address `a : Address`, the number of times `a` is referenced in the destructor's extracted `addresses` equals the number of times `a` is stored in the record's fields `fields.map Prod.snd` (`addressCount a addresses = addressCount a (fields.map Prod.snd)`).
4. Whenever the record's field addresses are distinct (`(fields.map Prod.snd).Nodup`, as holds for freshly allocated linear cells), every field address `a ∈ fields.map Prod.snd` has exact reference count `1` in `addresses` (`addressCount a addresses = 1`): no linear heap cell address is dropped or duplicated by the machine destructor. -/
public theorem heap_linear_conserved
    (heap : Array Cell) (fields : List (String × Address)) (names : List String)
    (function : Term) (environment : Environment) (rest : List Frame) (addresses : List Address)
    (distinct : (fields.map Prod.fst).Nodup) (nodup : names.Nodup)
    (covered : ∀ f ∈ fields, f.1 ∈ names)
    (found : splitValues fields names = some addresses) :
    let allocated := allocateFields heap addresses (splitCells addresses.length)
    stepRaw ⟨heap, .returned (.record fields), .split names function environment :: rest⟩ =
      ⟨allocated.1, .evaluate function environment, splitFrames (allocated.2.map Prod.snd) ++ rest⟩ ∧
    (allocated.2.map Prod.snd).length = fields.length ∧
    (∀ a : Address, addressCount a addresses = addressCount a (fields.map Prod.snd)) ∧
    ((fields.map Prod.snd).Nodup → ∀ a ∈ fields.map Prod.snd, addressCount a addresses = 1) := by
  intro allocated
  have hPerm : addresses.Perm (fields.map Prod.snd) :=
    machine_split_passes_all distinct nodup covered found
  refine ⟨machine_split_step heap fields names function environment rest addresses found, ?_, ?_, ?_⟩
  · rw [List.length_map, allocateFields_length, splitCells_length]
    have := hPerm.length_eq
    simpa using this
  · intro a
    exact Perm.addressCount_eq hPerm a
  · intro hAddrNodup a ha
    rw [Perm.addressCount_eq hPerm a]
    exact addressCount_eq_one_of_nodup_mem hAddrNodup ha

end Obend.Core.Proofs.GradedRecord

/-! ## Consolidated from `lean/Obend/Core/Proofs/JoinReading.lean` -/
namespace Obend.Core.Proofs.JoinReading
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.MachineTyping
open Obend.Core.Proofs.Conservation Obend.Core.Proofs.SubjectReduction
open Obend.Core.Proofs.BidirectionalCompleteness (occurrences uses_determined)
set_option autoImplicit false

/-! ### All-path usage -/

/-- At a join on a decided condition, the count is the larger of the counts of the two terms the
join may step to (`ifTrue`, `ifFalse`): the count is taken over every path, not the one taken. -/
public theorem join_count_is_max_of_paths (n : Nat) (cond : Bool) (whenTrue whenFalse : Term) (j : Nat) :
    (occurrences n (.ifBool (.boolean cond) whenTrue whenFalse)).getD j 0 =
      max ((occurrences n whenTrue).getD j 0) ((occurrences n whenFalse).getD j 0) ∧
    Step (.ifBool (.boolean cond) whenTrue whenFalse) (if cond then whenTrue else whenFalse) := by
  refine ⟨?_, ?_⟩
  · have lt := occurrences_length n whenTrue
    have lf := occurrences_length n whenFalse
    simp only [occurrences]
    rw [getD_addUses (by simp [joinUses, lt, lf]), getD_replicate_zero, Nat.zero_add,
      getD_joinUses (lt.trans lf.symm)]
  · cases cond
    · exact .ifFalse _ _
    · exact .ifTrue _ _

/-- **The count bounds every path.** Along any reduction of a term that checks (valid context,
within budget), the count of every reduct at every hypothesis that is not `unrestricted` is at most
the initial count (and equal at `linear` ones: `steps_conserve_linear'`). -/
public theorem count_bounds_every_path {a : Assumptions} {Γ : Context} {t t' : Term} {T : Ty} {u : Uses}
    (typed : PartialTyping a Γ t T u) (valid : validContext a.shareableVariables Γ = true)
    (safe : safeUses Γ u = true) (steps : Steps t t') :
    Below Γ (occurrences Γ.length t') u := by
  induction steps generalizing T u with
  | refl => rw [← uses_determined typed]; exact fun _ _ _ _ => Nat.le_refl _
  | next step rest ih =>
    obtain ⟨T1, u1, h1, s1, b1, _, _⟩ := step_preserves_typing typed valid safe step
    exact below_trans (ih h1 s1) b1

/-! ### Only the support is read at `unrestricted` -/

/-- Two usage vectors that agree at every tracked position and have the same zeros at every
`unrestricted` one. -/
@[expose] public def SameReading (Γ : Context) (x y : Uses) : Prop :=
  x.length = Γ.length ∧ y.length = Γ.length ∧ ∀ j b, Γ[j]? = some b →
    (b.quantity = .unrestricted → (x.getD j 0 = 0 ↔ y.getD j 0 = 0)) ∧
    (b.quantity ≠ .unrestricted → x.getD j 0 = y.getD j 0)

/-- **Every consumer reads only the support at `unrestricted`.** -/
public theorem consumers_read_support {V : List Nat} {Γ : Context} {x y : Uses} (h : SameReading Γ x y) :
    safeUses Γ x = safeUses Γ y ∧ linearFree Γ x = linearFree Γ y ∧
      reusableCaptures V Γ x = reusableCaptures V Γ y := by
  obtain ⟨lx, ly, H⟩ := h
  refine ⟨Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_⟩
  · rw [safeUses_iff, safeUses_iff]
    refine ⟨fun ⟨_, s⟩ => ⟨ly, fun j b hb => ?_⟩, fun ⟨_, s⟩ => ⟨lx, fun j b hb => ?_⟩⟩
    all_goals
      have := s j b hb
      by_cases q : b.quantity = .unrestricted
      · rw [q] at this ⊢; rfl
      · first | rw [← (H j b hb).2 q]; exact this | rw [(H j b hb).2 q]; exact this
  · rw [linearFree_iff lx, linearFree_iff ly]
    refine ⟨fun s j b hb => ?_, fun s j b hb => ?_⟩
    all_goals
      by_cases q : b.quantity = .linear
      · have qu : b.quantity ≠ .unrestricted := by rw [q]; decide
        have e := (H j b hb).2 qu
        rcases s j b hb with z | n
        · first | (left; rw [← e]; exact z) | (left; rw [e]; exact z)
        · exact absurd q n
      · exact .inr q
  · rw [captures_iff, captures_iff]
    refine ⟨fun ⟨_, s⟩ => ⟨ly, fun j b hb => ?_⟩, fun ⟨_, s⟩ => ⟨lx, fun j b hb => ?_⟩⟩
    all_goals
      rcases s j b hb with z | r
      · by_cases q : b.quantity = .unrestricted
        · left; first | exact ((H j b hb).1 q).mp z | exact ((H j b hb).1 q).mpr z
        · left; first | (rw [← (H j b hb).2 q]; exact z) | (rw [(H j b hb).2 q]; exact z)
      · exact .inr r

/-- `max` and `+` have the same zeros: at `unrestricted` positions the two joins read alike. -/
public theorem join_add_same_zeros {x y : Uses} (h : x.length = y.length) (j : Nat) :
    (joinUses x y).getD j 0 = 0 ↔ (addUses x y).getD j 0 = 0 := by
  rw [getD_joinUses h, getD_addUses h]; omega

/-- At `affine` positions the join must be `max`: a hypothesis used once on each branch is used at
most once, and `+` would count it twice and refuse it. -/
public theorem affine_join_needs_max :
    safeUses [⟨.natural, .affine⟩] (occurrences 1 (.ifBool (.boolean true) (.bound 0) (.bound 0))) = true ∧
    safeUses [⟨.natural, .affine⟩]
      (addUses (occurrences 1 (.boolean true)) (addUses (occurrences 1 (.bound 0)) (occurrences 1 (.bound 0)))) =
        false := by decide

/-! ### Never demand, never cost -/

/-- `(λ(y : unrestricted ℕ). y + y) h` in `h : unrestricted ℕ`. -/
@[expose] public def doubling : Term := .app (.lam (.binary .add (.bound 0) (.bound 0))) (.bound 0)
@[expose] public def doublingAnnotation : LambdaAnnotation := ⟨.natural, .natural, .unrestricted, .reusable⟩
@[expose] public def unrestrictedNat : Context := [⟨.natural, .unrestricted⟩]

theorem doubling_typed :
    PartialTyping {} unrestrictedNat doubling .natural [1] := by
  have body := PartialTyping.binary (assumptions := {})
    (context := ⟨doublingAnnotation.domain, doublingAnnotation.parameter⟩ :: unrestrictedNat)
    (primitive := .add) (input := .natural) (output := .natural) rfl
    (.bound (index := 0) (binding := ⟨.natural, .unrestricted⟩) rfl)
    (.bound (index := 0) (binding := ⟨.natural, .unrestricted⟩) rfl)
  have lam := PartialTyping.lambda (annotation := doublingAnnotation) body (by decide) (by decide)
    (by decide) (by decide)
  exact PartialTyping.application lam (.bound (index := 0) (context := unrestrictedNat)
    (binding := ⟨.natural, .unrestricted⟩) rfl) rfl rfl
    (by decide)

/-- **The count is not a demand bound.** At an `unrestricted` hypothesis, a checked term counting it
once steps to one counting it twice: the count bounds no number of demands along a run. -/
public theorem count_not_demand_bound :
    PartialTyping {} unrestrictedNat doubling .natural [1] ∧
      Step doubling (.binary .add (.bound 0) (.bound 0)) ∧
      (occurrences 1 doubling).getD 0 0 = 1 ∧
      (occurrences 1 (.binary .add (.bound 0) (.bound 0))).getD 0 0 = 2 := by
  refine ⟨doubling_typed, ?_, by decide, by decide⟩
  have := Step.beta (.binary .add (.bound 0) (.bound 0)) (.bound 0)
  simpa [doubling, instantiate, Term.substitute] using this

/-- **The count is not consumption.** A hypothesis counted once is demanded by no step: the join's
untaken branch holds it, and the run discards it. -/
public theorem count_not_consumption :
    (occurrences 1 (.ifBool (.boolean true) (.nat 0) (.bound 0))).getD 0 0 = 1 ∧
      Step (.ifBool (.boolean true) (.nat 0) (.bound 0)) (.nat 0) ∧
      (occurrences 1 (.nat 0)).getD 0 0 = 0 ∧ ∀ t', ¬ Step (.nat 0) t' :=
  ⟨by decide, .ifTrue _ _, by decide, fun _ s => value_no_step (.natural 0) s⟩

/-- **The count is not cost.** Two terms with the same count, of which one takes a step and the
other takes none. -/
public theorem count_not_cost :
    occurrences 1 (.app (.lam (.bound 0)) (.bound 0)) = occurrences 1 (.bound 0) ∧
      Step (.app (.lam (.bound 0)) (.bound 0)) (.bound 0) ∧ ∀ t', ¬ Step (.bound 0) t' :=
  ⟨by decide, by simpa [instantiate, Term.substitute] using Step.beta (.bound 0) (.bound 0),
    fun _ s => by cases s⟩

end Obend.Core.Proofs.JoinReading

/-! ## Consolidated from `lean/Obend/Core/Proofs/Splice.lean` -/
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
  have dc : PartialTyping cv.assumptions Ψ cv.term A k.uses := by
    rw [← (Obend.Core.Bidirectional.checkAgainst_sound kA).1]; exact k.derivation
  have df : PartialTyping cv.assumptions Ψ fv.term b.type kf.uses := by
    rw [← fθ, ← (Obend.Core.Bidirectional.checkAgainst_sound kfB).1]; exact kf.derivation
  have uc := uses_determined dc
  have uf := uses_determined df
  dsimp only at safe allowed ⊢
  rw [← uc, ← uf] at safe ⊢
  rw [← uf] at allowed
  obtain ⟨u', h, sf, le, lin⟩ := splice_typed dc k.contextValid hx df allowed safe
  obtain ⟨s, hs, -⟩ := Obend.Core.Code.typed_has_code h sf k.contextValid k.assumptionsValid cv.kinds
  refine ⟨s, hs, ?_, ?_⟩
  · intro j; rw [hs, ← uses_determined h]; exact le j
  · intro j l; rw [hs, ← uses_determined h]; exact lin j l

end Obend.Core.Proofs.Splice
