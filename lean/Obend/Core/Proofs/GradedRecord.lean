module
/- Per-field graded record quantities (`Σ⊗` / `Σ&`) and machine-level heap-address linear
conservation (`G3`, WS 27).

1. **Per-field graded record quantities (`Σ⊗` vs `Σ&`, following Abel–Danielsson–Eriksson 2023)**:
   In a mixed resourceful record such as `{held = h, tag = 0}`, field `held` carries grade `.linear`
   while sibling field `tag` carries grade `.unrestricted` (or `.affine`). Under per-field graded
   `Σ⊗` elimination (`GradedSigmaTensor`), the continuation binds each field `i` at its own grade
   `qᵢ`: linear fields satisfy `qᵢ = .linear` (`fits` ⇒ used exactly once), whereas shareable
   sibling fields (`qᵢ ≠ .linear`) are required to be `linearFree` in the outer context and may be
   used 0, 1, or many times according to `qᵢ.fits` without forcing the shareable sibling `tag` to be
   consumed linearly (`graded_sigma_tensor_conserves_linear`).
2. **Machine-level heap-address linear conservation (`heap_linear_conserved`)**:
   Lifts source-level destructor conservation (`split_accounts`, `machine_split_passes_all`) to explicit
   machine heap-address reference counts (`addressCount`) across `stepRaw` on `.split` frames and
   indirection cells (`splitCells` / `splitFrames`). -/
public import Obend.Core.Proofs.Aggregate
import all Obend.Core.Check
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.Aggregate

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
