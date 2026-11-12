module
/-
# Obend.Judge.VpaComplementAndJson — Boolean-closed visibly pushdown policies, the JSON grammar
under redaction, Merkle inclusion of a single span, and the span-disclosure judge
**§1 Visibly pushdown automata (Alur and Madhusudan, STOC 2004).** The alphabet is tagged
`call s`, `ret s`, `int a`. A `DetVpa` has total transitions; a return pops only a symbol pushed
under its own sort, and an unmatched return is the sink. Liveness and the stack's sorts depend on
the word alone (`runFrom_skel`), so products are synchronized: `accepts_intersect` and
`accepts_union` on every word, `accepts_complement` on every well-matched word. Emptiness is
certified by a summary relation closed under internal steps, calls and returns
(`verifyVpaEmpty_sound`); `verifyVpaContainment_sound` is `L(M₁) ⊆ L(M₂)`. `vpaContainmentJudge`
means that inclusion, refuses with a separating word, and is complete on queries with a closed
summary whose initial row is exact.
**§2 The JSON grammar (RFC 8259) in one pass.** `stepJson` reads one byte: values, the six
structural characters in their places, strings with the eight short escapes and `\uXXXX` and no
byte below `0x20`, numbers, the three literals, whitespace; a key holds no backslash and each
object's keys are pairwise distinct (`json_object_keys_nodup`). `checkJsonRedaction doc l r mask`
accepts a span that starts in a value string outside any escape, stays inside that string, ends in
the starting machine state, and a mask of printable bytes without `"` or `\`.
`jsonRedaction_preserves_valid_parse_and_keys`: the redacted document has the original's verdict,
key sets and machine state at every cut after the span. `jsonRedaction_confinement`: two accepted
redactions of documents that agree outside their spans give the same bytes and the same parse.
**§3 Merkle inclusion of one span.** Leaves are `0x00 ‖ be8(len) ‖ span`, nodes `0x01 ‖ l ‖ r`,
the root digest `0x02 ‖ leaf(count) ‖ top`, all under one customization string given as a
parameter; an odd node is promoted. `rootHash_binds`: the 32-byte `top` binds the leaf count.
`verifySpanMerkleInclusion_complete`, and `verifySpanMerkleInclusion_top_binding`: a span that
verifies against a `top` is the span at that index, or two different messages have one digest.
**§4** `jsonSpanJudge` / `vpa-json-span@1`: a disclosed document is the splice, parses as the
original, and the hidden span opens to the certificate's root.
Not here: a declarative RFC 8259 grammar with a soundness theorem for `stepJson` (the machine is
the definition; its rejections are exercised by vectors); a parser from bytes to a value tree
(`Obend.Vault.Lsafe` commits to one). Raw strings validate UTF-8, including scalar bounds.
-/
public import Obend.Judge.Class
public import Obend.Judge.SymbolicRegexBisim
public section
namespace Obend.Judge.VpaJson
open Obend.Codec.DetCbor
open Obend.Judge.Commit (Hasher cshakeHasher HashCollision keysDistinctB keysDistinctB_sound
  spliceByteArray spliceByteArray_toList hexOf unhex natField countSpan countSpan_injective)
set_option autoImplicit false
/-! ## 1. Determinized visibly pushdown automata -/
/-- A type with a list of all its elements. -/
class FinEnum (α : Type) where
  elems : List α
  complete : ∀ a : α, a ∈ elems
instance : FinEnum Bool := ⟨[false, true], fun b => by cases b <;> simp⟩
instance : FinEnum Unit := ⟨[()], fun _ => by simp⟩
/-- A tagged symbol: a call or a return of a bracket sort, or an internal letter. -/
inductive Sym (S L : Type) where
  | call (s : S)
  | ret (s : S)
  | int (a : L)
  deriving DecidableEq
/-- **A deterministic visibly pushdown automaton** with total transitions. -/
structure DetVpa (S L Q Γ : Type) where
  init : Q
  acc : Q → Bool
  stepInt : Q → L → Q
  /-- the target state and the pushed symbol -/
  stepCall : Q → S → Q × Γ
  /-- from the state, the popped symbol and the sort -/
  stepRet : Q → Γ → S → Q
section Vpa
variable {S L Q Γ Q₁ Γ₁ Q₂ Γ₂ : Type} [DecidableEq S]
/-- A return pops only a symbol pushed under its own sort. -/
def sortMatch (pushed popped : S) : Bool := decide (pushed = popped)
theorem sortMatch_spec {a b : S} (h : sortMatch a b = true) : a = b := of_decide_eq_true h
/-- One step of a live configuration; `none` is the sink. -/
def stepCfg (M : DetVpa S L Q Γ) (c : Q × List (Γ × S)) : Sym S L → Option (Q × List (Γ × S))
  | .int a => some (M.stepInt c.1 a, c.2)
  | .call s => some ((M.stepCall c.1 s).1, ((M.stepCall c.1 s).2, s) :: c.2)
  | .ret s =>
    match c.2 with
    | [] => none
    | top :: rest => if sortMatch top.2 s then some (M.stepRet c.1 top.1 s, rest) else none
/-- The run from a configuration. -/
def runFrom (M : DetVpa S L Q Γ) :
    Option (Q × List (Γ × S)) → List (Sym S L) → Option (Q × List (Γ × S))
  | c, [] => c
  | c, x :: w => runFrom M (c.bind fun c => stepCfg M c x) w
/-- **The total deterministic run** of a word. -/
def runDetVpa (M : DetVpa S L Q Γ) (w : List (Sym S L)) : Option (Q × List (Γ × S)) :=
  runFrom M (some (M.init, [])) w
/-- Acceptance: a live run that ends in an accepting state with the stack empty. -/
def accepts (M : DetVpa S L Q Γ) (w : List (Sym S L)) : Bool :=
  match runDetVpa M w with
  | some (q, []) => M.acc q
  | _ => false
theorem runFrom_none (M : DetVpa S L Q Γ) : ∀ w : List (Sym S L), runFrom M none w = none
  | [] => rfl
  | _ :: w => by simp only [runFrom, Option.bind_none]; exact runFrom_none M w
/-- The stack of sorts, with no automaton. -/
def stepSorts (st : List S) : Sym S L → Option (List S)
  | .int _ => some st
  | .call s => some (s :: st)
  | .ret s =>
    match st with
    | [] => none
    | top :: rest => if sortMatch top s then some rest else none
def sortsFrom : Option (List S) → List (Sym S L) → Option (List S)
  | c, [] => c
  | c, x :: w => sortsFrom (c.bind fun st => stepSorts st x) w
/-- **Well-matched**: every return closes the innermost open call of its sort, and none is open
at the end. -/
def wellMatched (w : List (Sym S L)) : Bool :=
  match sortsFrom (some ([] : List S)) w with
  | some [] => true
  | _ => false
/-- The sorts on a configuration's stack. -/
def skel (c : Q × List (Γ × S)) : List S := c.2.map (·.2)
theorem stepCfg_skel (M : DetVpa S L Q Γ) (c : Q × List (Γ × S)) (x : Sym S L) :
    (stepCfg M c x).map skel = stepSorts (skel c) x := by
  obtain ⟨q, st⟩ := c
  cases x with
  | int a => rfl
  | call s => rfl
  | ret s =>
    cases st with
    | nil => rfl
    | cons top rest =>
      simp only [stepCfg, skel, List.map_cons, stepSorts]
      cases sortMatch top.2 s <;> rfl
/-- **The stack discipline is the word's**: liveness and the stack's sorts do not depend on the
automaton. -/
theorem runFrom_skel (M : DetVpa S L Q Γ) :
    ∀ (w : List (Sym S L)) (c : Option (Q × List (Γ × S))),
      (runFrom M c w).map skel = sortsFrom (c.map skel) w
  | [], _ => rfl
  | x :: w, c => by
    simp only [runFrom, sortsFrom]
    rw [runFrom_skel M w]
    congr 1
    cases c with
    | none => rfl
    | some c => exact stepCfg_skel M c x
/-- A word is not well-matched and rejected, or its run ends live with an empty stack. -/
theorem accepts_cases (M : DetVpa S L Q Γ) (w : List (Sym S L)) :
    (wellMatched w = false ∧ accepts M w = false) ∨
      ∃ q, runDetVpa M w = some (q, []) ∧ wellMatched w = true ∧ accepts M w = M.acc q := by
  have hs : (runDetVpa M w).map skel = sortsFrom (some []) w := runFrom_skel M w (some (M.init, []))
  unfold accepts wellMatched
  cases hr : runDetVpa M w with
  | none => rw [hr] at hs; rw [← hs]; exact Or.inl ⟨rfl, rfl⟩
  | some c =>
    obtain ⟨q, st⟩ := c
    rw [hr] at hs
    rw [← hs]
    cases st with
    | nil => exact Or.inr ⟨q, rfl, rfl, rfl⟩
    | cons _ _ => exact Or.inl ⟨rfl, rfl⟩
theorem accepts_wellMatched {M : DetVpa S L Q Γ} {w : List (Sym S L)} (h : accepts M w = true) :
    wellMatched w = true := by
  rcases accepts_cases M w with ⟨_, h'⟩ | ⟨_, _, hw, _⟩
  · rw [h] at h'; cases h'
  · exact hw
/-- **The complement**: the same transitions, the accepting states inverted. -/
def complementVpa (M : DetVpa S L Q Γ) : DetVpa S L Q Γ := { M with acc := fun q => !M.acc q }
theorem runFrom_complement (M : DetVpa S L Q Γ) :
    ∀ (w : List (Sym S L)) (c : Option (Q × List (Γ × S))),
      runFrom (complementVpa M) c w = runFrom M c w
  | [], _ => rfl
  | x :: w, c => by
    simp only [runFrom]
    have : (c.bind fun c => stepCfg (complementVpa M) c x) = c.bind fun c => stepCfg M c x := by
      cases c with
      | none => rfl
      | some c => cases x <;> rfl
    rw [this, runFrom_complement M w]
/-- **Exact complementation on well-matched words.** -/
theorem accepts_complement (M : DetVpa S L Q Γ) {w : List (Sym S L)} (h : wellMatched w = true) :
    accepts (complementVpa M) w = !accepts M w := by
  rcases accepts_cases M w with ⟨h', _⟩ | ⟨q, hr, _, ha⟩
  · rw [h] at h'; cases h'
  · rw [ha]
    have hc : runDetVpa (complementVpa M) w = some (q, []) := by
      rw [← hr]; exact runFrom_complement M w _
    unfold accepts
    rw [hc]
    rfl
theorem accepts_complement_iff (M : DetVpa S L Q Γ) {w : List (Sym S L)} (h : wellMatched w = true) :
    accepts (complementVpa M) w = true ↔ accepts M w = false := by
  rw [accepts_complement M h]; cases accepts M w <;> simp
/-- The synchronized product: both automata step on every symbol and push together. -/
def prodVpa (f : Bool → Bool → Bool) (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) :
    DetVpa S L (Q₁ × Q₂) (Γ₁ × Γ₂) where
  init := (M₁.init, M₂.init)
  acc q := f (M₁.acc q.1) (M₂.acc q.2)
  stepInt q a := (M₁.stepInt q.1 a, M₂.stepInt q.2 a)
  stepCall q s :=
    (((M₁.stepCall q.1 s).1, (M₂.stepCall q.2 s).1), ((M₁.stepCall q.1 s).2, (M₂.stepCall q.2 s).2))
  stepRet q γ s := (M₁.stepRet q.1 γ.1 s, M₂.stepRet q.2 γ.2 s)
/-- **Intersection.** -/
def intersectVpa (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) := prodVpa (· && ·) M₁ M₂
/-- **Union.** -/
def unionVpa (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) := prodVpa (· || ·) M₁ M₂
def projL (c : (Q₁ × Q₂) × List ((Γ₁ × Γ₂) × S)) : Q₁ × List (Γ₁ × S) :=
  (c.1.1, c.2.map fun g => (g.1.1, g.2))
def projR (c : (Q₁ × Q₂) × List ((Γ₁ × Γ₂) × S)) : Q₂ × List (Γ₂ × S) :=
  (c.1.2, c.2.map fun g => (g.1.2, g.2))
theorem stepCfg_proj (f : Bool → Bool → Bool) (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂)
    (c : (Q₁ × Q₂) × List ((Γ₁ × Γ₂) × S)) (x : Sym S L) :
    (stepCfg (prodVpa f M₁ M₂) c x).map projL = stepCfg M₁ (projL c) x ∧
      (stepCfg (prodVpa f M₁ M₂) c x).map projR = stepCfg M₂ (projR c) x := by
  obtain ⟨q, st⟩ := c
  cases x with
  | int a => exact ⟨rfl, rfl⟩
  | call s => exact ⟨rfl, rfl⟩
  | ret s =>
    cases st with
    | nil => exact ⟨rfl, rfl⟩
    | cons top rest =>
      simp only [stepCfg, projL, projR, List.map_cons]
      cases sortMatch top.2 s <;> exact ⟨rfl, rfl⟩
/-- Each projection of the product's run is the run of that automaton. -/
theorem runFrom_proj (f : Bool → Bool → Bool) (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) :
    ∀ (w : List (Sym S L)) (c : Option ((Q₁ × Q₂) × List ((Γ₁ × Γ₂) × S))),
      (runFrom (prodVpa f M₁ M₂) c w).map projL = runFrom M₁ (c.map projL) w ∧
        (runFrom (prodVpa f M₁ M₂) c w).map projR = runFrom M₂ (c.map projR) w
  | [], _ => ⟨rfl, rfl⟩
  | x :: w, c => by
    simp only [runFrom]
    rw [(runFrom_proj f M₁ M₂ w _).1, (runFrom_proj f M₁ M₂ w _).2]
    cases c with
    | none => exact ⟨rfl, rfl⟩
    | some c =>
      exact ⟨congrArg (runFrom M₁ · w) (stepCfg_proj f M₁ M₂ c x).1,
        congrArg (runFrom M₂ · w) (stepCfg_proj f M₁ M₂ c x).2⟩
/-- The product accepts by `f` of the two verdicts, for every word: both runs are live or both
are in the sink, with stacks of one height. -/
theorem accepts_prod (f : Bool → Bool → Bool) (hf : f false false = false)
    (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) (w : List (Sym S L)) :
    accepts (prodVpa f M₁ M₂) w = f (accepts M₁ w) (accepts M₂ w) := by
  have h1 : (runDetVpa (prodVpa f M₁ M₂) w).map projL = runDetVpa M₁ w :=
    (runFrom_proj f M₁ M₂ w (some ((M₁.init, M₂.init), []))).1
  have h2 : (runDetVpa (prodVpa f M₁ M₂) w).map projR = runDetVpa M₂ w :=
    (runFrom_proj f M₁ M₂ w (some ((M₁.init, M₂.init), []))).2
  unfold accepts
  rw [← h1, ← h2]
  cases runDetVpa (prodVpa f M₁ M₂) w with
  | none => exact hf.symm
  | some c =>
    obtain ⟨q, st⟩ := c
    cases st with
    | nil => rfl
    | cons _ _ => exact hf.symm
/-- **Intersection is conjunction of verdicts, on every word.** -/
theorem accepts_intersect (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) (w : List (Sym S L)) :
    accepts (intersectVpa M₁ M₂) w = (accepts M₁ w && accepts M₂ w) :=
  accepts_prod _ rfl M₁ M₂ w
/-- **Union is disjunction of verdicts, on every word.** -/
theorem accepts_union (M₁ : DetVpa S L Q₁ Γ₁) (M₂ : DetVpa S L Q₂ Γ₂) (w : List (Sym S L)) :
    accepts (unionVpa M₁ M₂) w = (accepts M₁ w || accepts M₂ w) :=
  accepts_prod _ rfl M₁ M₂ w
/-! ### Emptiness by a summary relation, and containment -/
variable [FinEnum S] [FinEnum L] [DecidableEq Q]
/-- The summary relation is closed: it has the initial entry, and from each summarized state it
has the internal successors, the call target as an entry, and the return through every summary
of that entry. -/
def summaryClosed (M : DetVpa S L Q Γ) (sum : List (Q × Q)) : Bool :=
  decide ((M.init, M.init) ∈ sum) &&
    sum.all fun eq =>
      (FinEnum.elems (α := L)).all (fun a => decide ((eq.1, M.stepInt eq.2 a) ∈ sum)) &&
      (FinEnum.elems (α := S)).all fun s =>
        decide (((M.stepCall eq.2 s).1, (M.stepCall eq.2 s).1) ∈ sum) &&
        sum.all fun e2 => decide (e2.1 = (M.stepCall eq.2 s).1 →
          (eq.1, M.stepRet e2.2 (M.stepCall eq.2 s).2 s) ∈ sum)
/-- No state summarized from the initial entry accepts. -/
def summaryRejects (M : DetVpa S L Q Γ) (sum : List (Q × Q)) : Bool :=
  sum.all fun eq => decide (eq.1 = M.init → M.acc eq.2 = false)
/-- **The emptiness check.** -/
def verifyVpaEmpty (M : DetVpa S L Q Γ) (sum : List (Q × Q)) : Bool :=
  summaryClosed M sum && summaryRejects M sum
omit [DecidableEq S] in
theorem summaryClosed_spec {M : DetVpa S L Q Γ} {sum : List (Q × Q)}
    (h : summaryClosed M sum = true) :
    (M.init, M.init) ∈ sum ∧ (∀ e q a, (e, q) ∈ sum → (e, M.stepInt q a) ∈ sum) ∧
      ∀ e q s, (e, q) ∈ sum → ((M.stepCall q s).1, (M.stepCall q s).1) ∈ sum ∧
        ∀ q2, ((M.stepCall q s).1, q2) ∈ sum → (e, M.stepRet q2 (M.stepCall q s).2 s) ∈ sum := by
  simp only [summaryClosed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun e q a he => (h.2 (e, q) he).1 a (FinEnum.complete a), fun e q s he => ?_⟩
  obtain ⟨h1, h2⟩ := (h.2 (e, q) he).2 s (FinEnum.complete s)
  exact ⟨h1, fun q2 hq2 => h2 (_, q2) hq2 rfl⟩
/-- From entry `e`, the stack returns through the relation down to the initial entry. -/
def Chain (M : DetVpa S L Q Γ) (sum : List (Q × Q)) : Q → List (Γ × S) → Prop
  | e, [] => e = M.init
  | e, top :: rest =>
    ∃ e', (∀ q2, (e, q2) ∈ sum → (e', M.stepRet q2 top.1 top.2) ∈ sum) ∧ Chain M sum e' rest
/-- The invariant of live configurations. -/
def Inv (M : DetVpa S L Q Γ) (sum : List (Q × Q)) (c : Q × List (Γ × S)) : Prop :=
  ∃ e, (e, c.1) ∈ sum ∧ Chain M sum e c.2
theorem inv_step {M : DetVpa S L Q Γ} {sum : List (Q × Q)} (hc : summaryClosed M sum = true)
    {c c' : Q × List (Γ × S)} {x : Sym S L} (hi : Inv M sum c) (hs : stepCfg M c x = some c') :
    Inv M sum c' := by
  have hsp := summaryClosed_spec hc
  obtain ⟨q, st⟩ := c
  obtain ⟨e, he, hch⟩ := hi
  cases x with
  | int a =>
    simp only [stepCfg, Option.some.injEq] at hs
    subst hs
    exact ⟨e, hsp.2.1 e q a he, hch⟩
  | call s =>
    simp only [stepCfg, Option.some.injEq] at hs
    subst hs
    obtain ⟨h1, h2⟩ := hsp.2.2 e q s he
    exact ⟨(M.stepCall q s).1, h1, e, h2, hch⟩
  | ret s =>
    cases st with
    | nil => simp [stepCfg] at hs
    | cons top rest =>
      simp only [stepCfg] at hs
      split at hs
      · rename_i hm
        have hss : top.2 = s := sortMatch_spec hm
        simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨e', hret, hch'⟩ := hch
        exact ⟨e', hss ▸ hret q he, hch'⟩
      · cases hs
theorem inv_run {M : DetVpa S L Q Γ} {sum : List (Q × Q)} (hc : summaryClosed M sum = true) :
    ∀ (w : List (Sym S L)) (c c' : Q × List (Γ × S)), Inv M sum c →
      runFrom M (some c) w = some c' → Inv M sum c'
  | [], c, c', hi, hr => by cases hr; exact hi
  | x :: w, c, c', hi, hr => by
    simp only [runFrom, Option.bind_some] at hr
    cases hs : stepCfg M c x with
    | none => rw [hs, runFrom_none] at hr; cases hr
    | some c₁ => rw [hs] at hr; exact inv_run hc w c₁ c' (inv_step hc hi hs) hr
/-- **An accepted emptiness certificate**: the automaton accepts no word. -/
theorem verifyVpaEmpty_sound {M : DetVpa S L Q Γ} {sum : List (Q × Q)} :
    verifyVpaEmpty M sum = true → ∀ w : List (Sym S L), accepts M w = false := by
  intro h w
  simp only [verifyVpaEmpty, Bool.and_eq_true] at h
  rcases accepts_cases M w with ⟨_, h'⟩ | ⟨q, hr, _, ha⟩
  · exact h'
  · obtain ⟨e, he, hch⟩ :=
      inv_run h.1 w (M.init, []) (q, []) ⟨M.init, (summaryClosed_spec h.1).1, rfl⟩ hr
    have hrej := h.2
    simp only [summaryRejects, List.all_eq_true, decide_eq_true_eq] at hrej
    rw [ha]
    exact hrej (e, q) he hch
/-- **The containment check**: an emptiness certificate for `M₁ ∩ ¬M₂`. -/
def verifyVpaContainment [DecidableEq Q₁] [DecidableEq Q₂] (M₁ : DetVpa S L Q₁ Γ₁)
    (M₂ : DetVpa S L Q₂ Γ₂) (sum : List ((Q₁ × Q₂) × (Q₁ × Q₂))) : Bool :=
  verifyVpaEmpty (intersectVpa M₁ (complementVpa M₂)) sum
/-- **Certified containment**: every word `M₁` accepts, `M₂` accepts. -/
theorem verifyVpaContainment_sound [DecidableEq Q₁] [DecidableEq Q₂] {M₁ : DetVpa S L Q₁ Γ₁}
    {M₂ : DetVpa S L Q₂ Γ₂} {sum : List ((Q₁ × Q₂) × (Q₁ × Q₂))} :
    verifyVpaContainment M₁ M₂ sum = true →
      ∀ w : List (Sym S L), accepts M₁ w = true → accepts M₂ w = true := by
  intro h w h1
  have he := verifyVpaEmpty_sound h w
  rw [accepts_intersect, h1, Bool.true_and, accepts_complement M₂ (accepts_wellMatched h1)] at he
  cases h2 : accepts M₂ w with
  | true => rfl
  | false => rw [h2] at he; cases he
/-- Append an element that is not there yet. -/
def addNew {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else acc ++ [x]
/-- One round of successors of a summary relation. -/
def summaryStep (M : DetVpa S L Q Γ) (sum : List (Q × Q)) : List (Q × Q) :=
  sum.foldl (fun acc eq =>
    (FinEnum.elems (α := S)).foldl (fun acc s =>
      sum.foldl (fun acc e2 =>
        if e2.1 = (M.stepCall eq.2 s).1 then
          addNew acc (eq.1, M.stepRet e2.2 (M.stepCall eq.2 s).2 s)
        else acc) (addNew acc ((M.stepCall eq.2 s).1, (M.stepCall eq.2 s).1)))
      ((FinEnum.elems (α := L)).foldl (fun acc a => addNew acc (eq.1, M.stepInt eq.2 a)) acc)) sum
/-- **The summary search** (untrusted): saturate from the initial entry at a fuel. -/
def saturateSummary (M : DetVpa S L Q Γ) : Nat → List (Q × Q) → List (Q × Q)
  | 0, sum => sum
  | n + 1, sum => if summaryClosed M sum then sum else saturateSummary M n (summaryStep M sum)
def emitVpaSummary (M : DetVpa S L Q Γ) (fuel : Nat) : List (Q × Q) :=
  saturateSummary M fuel [(M.init, M.init)]
/-! ### The containment judge -/
/-- A containment query. -/
structure VpaQuery (S L Q₁ Γ₁ Q₂ Γ₂ : Type) where
  left : DetVpa S L Q₁ Γ₁
  right : DetVpa S L Q₂ Γ₂
/-- `L(left) ⊆ L(right)`. -/
def VpaIncluded (q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂) : Prop :=
  ∀ w : List (Sym S L), accepts q.left w = true → accepts q.right w = true
/-- The word is accepted on the left and rejected on the right. -/
def separates (q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂) (w : List (Sym S L)) : Bool :=
  accepts q.left w && !accepts q.right w
omit [FinEnum S] [FinEnum L] in
theorem separates_refutes {q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂} {w : List (Sym S L)}
    (h : separates q w = true) : ¬ VpaIncluded q := by
  simp only [separates, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hi
  rw [hi w h.1] at h
  exact absurd h.2 (by decide)
def firstSomeOf {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs => match f x with
    | some b => some b
    | none => firstSomeOf f xs
theorem firstSomeOf_spec {α β : Type} {f : α → Option β} : ∀ {xs : List α} {b : β},
    firstSomeOf f xs = some b → ∃ x, f x = some b
  | [], _, h => by cases h
  | x :: xs, b, h => by
    simp only [firstSomeOf] at h
    cases hf : f x with
    | some b' => rw [hf] at h; exact ⟨x, by rw [hf]; exact h⟩
    | none => rw [hf] at h; exact firstSomeOf_spec h
/-- Every symbol of the tagged alphabet. -/
def allSyms : List (Sym S L) :=
  (FinEnum.elems (α := S)).map .call ++ (FinEnum.elems (α := S)).map .ret ++
    (FinEnum.elems (α := L)).map .int
/-- A separating extension of `w` by at most `depth` symbols. -/
def cexWord (q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂) (syms : List (Sym S L)) :
    Nat → List (Sym S L) → Option (List (Sym S L))
  | 0, w => if separates q w then some w else none
  | n + 1, w =>
    if separates q w then some w else firstSomeOf (fun x => cexWord q syms n (w ++ [x])) syms
omit [FinEnum S] [FinEnum L] in
theorem cexWord_sound (q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂) (syms : List (Sym S L)) :
    ∀ (n : Nat) (w w' : List (Sym S L)), cexWord q syms n w = some w' → separates q w' = true
  | 0, w, w', h => by
    simp only [cexWord] at h
    split at h
    · rename_i hs; cases h; exact hs
    · cases h
  | n + 1, w, w', h => by
    simp only [cexWord] at h
    split at h
    · rename_i hs; cases h; exact hs
    · obtain ⟨x, hx⟩ := firstSomeOf_spec h
      exact cexWord_sound q syms n _ w' hx
/-- A containment is refused with a separating word. -/
inductive VpaRefusal (S L : Type) where
  | counterexample (w : List (Sym S L))
variable [DecidableEq Q₁] [DecidableEq Q₂]
/-- The verdict: an accepted summary, else a separating word found within the grade, else
undecided. -/
def vpaCheck (grade : Nat) (q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂) (sum : List ((Q₁ × Q₂) × (Q₁ × Q₂))) :
    Judge.Verdict (VpaRefusal S L) :=
  if verifyVpaContainment q.left q.right sum then .ok
  else match Judge.deepen (fun d => cexWord q allSyms d []) grade with
    | some w => .refused (.counterexample w) [w.length]
    | none => .uncovered
/-- The entry row of the initial state is exact: each state in it is reached by a word whose
run ends with the stack empty. -/
def InitRowExact (M : DetVpa S L Q Γ) (sum : List (Q × Q)) : Prop :=
  ∀ q, (M.init, q) ∈ sum → ∃ w : List (Sym S L), runDetVpa M w = some (q, [])
/-- **Completeness on exact summaries.** A closed summary of `M₁ ∩ ¬M₂` whose initial row is
exact is an accepted certificate whenever the containment holds. -/
theorem exact_summary_accepted {q : VpaQuery S L Q₁ Γ₁ Q₂ Γ₂}
    {sum : List ((Q₁ × Q₂) × (Q₁ × Q₂))}
    (hc : summaryClosed (intersectVpa q.left (complementVpa q.right)) sum = true)
    (hx : InitRowExact (intersectVpa q.left (complementVpa q.right)) sum) (hi : VpaIncluded q) :
    verifyVpaContainment q.left q.right sum = true := by
  simp only [verifyVpaContainment, verifyVpaEmpty, Bool.and_eq_true, summaryRejects,
    List.all_eq_true, decide_eq_true_eq]
  refine ⟨hc, fun eq hm he => ?_⟩
  obtain ⟨e, st⟩ := eq
  simp only at he
  subst he
  obtain ⟨w, hw⟩ := hx st hm
  have ha : accepts (intersectVpa q.left (complementVpa q.right)) w =
      (intersectVpa q.left (complementVpa q.right)).acc st := by
    unfold accepts; rw [hw]
  rw [← ha, accepts_intersect]
  cases h1 : accepts q.left w with
  | false => rfl
  | true =>
    rw [Bool.true_and, accepts_complement q.right (accepts_wellMatched h1), hi w h1]
    rfl
/-- **The containment judge.** -/
instance vpaContainmentJudge :
    Judge (VpaQuery S L Q₁ Γ₁ Q₂ Γ₂) (List ((Q₁ × Q₂) × (Q₁ × Q₂))) where
  Clause := VpaRefusal S L
  Meaning q _ := VpaIncluded q
  check := vpaCheck
  sound := by
    intro r q c h
    unfold vpaCheck at h
    split at h
    · rename_i hb; exact verifyVpaContainment_sound hb
    · split at h <;> cases h
  refutes _ := true
  refuted := by
    intro r q c k p h _ c' hm
    unfold vpaCheck at h
    split at h
    · cases h
    · split at h
      · rename_i w hw
        obtain ⟨i, _, hi⟩ := Judge.deepen_some _ hw
        exact separates_refutes (cexWord_sound q allSyms i [] w hi) hm
      · cases h
  Fragment q := ∃ sum, summaryClosed (intersectVpa q.left (complementVpa q.right)) sum = true ∧
    InitRowExact (intersectVpa q.left (complementVpa q.right)) sum
  complete := by
    rintro q ⟨sum, hc, hx⟩ ⟨_, hi⟩
    refine ⟨sum, 0, ?_⟩
    simp only [vpaCheck, exact_summary_accepted hc hx hi, ↓reduceIte]
  mono := by
    intro r r' q c le h
    simp only [vpaCheck] at h ⊢
    cases hb : verifyVpaContainment q.left q.right c with
    | true => rfl
    | false =>
      rw [hb] at h
      cases hd : Judge.deepen (fun d => cexWord q allSyms d []) r with
      | some w => rw [Judge.deepen_mono _ hd le]
      | none => rw [hd] at h; simp at h
end Vpa
/-- Every well-matched word over two bracket sorts. -/
def balancedVpa : DetVpa Bool Unit Unit Unit :=
  ⟨(), fun _ => true, fun q _ => q, fun q _ => (q, ()), fun q _ _ => q⟩
/-- The well-matched words whose brackets are all of sort `true`. -/
def oneSortVpa : DetVpa Bool Unit Bool Unit :=
  ⟨true, fun q => q, fun q _ => q, fun q s => (q && s, ()), fun q _ _ => q⟩
example : verifyVpaContainment oneSortVpa balancedVpa
    (emitVpaSummary (intersectVpa oneSortVpa (complementVpa balancedVpa)) 8) = true := by
  decide +kernel
example : verifyVpaContainment balancedVpa oneSortVpa
    (emitVpaSummary (intersectVpa balancedVpa (complementVpa oneSortVpa)) 8) = false := by
  decide +kernel
example : verifyVpaEmpty (intersectVpa oneSortVpa (complementVpa balancedVpa))
    (emitVpaSummary (intersectVpa oneSortVpa (complementVpa balancedVpa)) 8) = true := by
  decide +kernel
example : cexWord ⟨balancedVpa, oneSortVpa⟩ allSyms 2 [] = some [.call false, .ret false] := by
  decide +kernel
/-! ## 2. The JSON grammar in one pass, redaction, and the canonical commitment -/
/-- Inside a string: plain, after `\`, inside `\uXXXX` (pairing UTF-16 surrogates so lone or
redaction-split surrogates are refused), or inside raw UTF-8 continuation bytes. -/
inductive StrSub where
  | normal
  | esc
  | u0
  | hexD
  | hex (left : Nat)
  | hiSurr (left : Nat)
  | afterHi
  | loEsc
  | loU
  | loD
  | utf8 (left lo hi : Nat)
  deriving DecidableEq
/-- Inside a number (RFC 8259 §6). -/
inductive NumSub where
  | minus | zero | int | dot | frac | e | esign | exp
  deriving DecidableEq
/-- Where the grammar is. -/
inductive JMode where
  /-- a value is expected; `canClose` directly after `[` -/
  | value (canClose : Bool)
  /-- a key is expected; `canClose` directly after `{` -/
  | key (canClose : Bool)
  | colon
  /-- a value has ended -/
  | after
  | str (isKey : Bool) (sub : StrSub)
  | num (sub : NumSub)
  /-- the bytes of `true`, `false` or `null` still to come -/
  | lit (rest : List UInt8)
  deriving DecidableEq
/-- An open bracket: object or array, and an object's keys so far. -/
structure JFrame where
  isObj : Bool
  keys : List ByteArray
  deriving DecidableEq
/-- The machine state. `closed` collects the key sets of the objects already closed. -/
structure JState where
  mode : JMode
  stack : List JFrame
  curKey : ByteArray
  closed : List (List ByteArray)
  ok : Bool
  deriving DecidableEq
def JState.init : JState := ⟨.value false, [], ByteArray.empty, [], true⟩
def isWs (b : UInt8) : Bool := b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d
def isDigit (b : UInt8) : Bool := decide (0x30 ≤ b.toNat) && decide (b.toNat ≤ 0x39)
def isHexDigit (b : UInt8) : Bool :=
  isDigit b || (decide (0x41 ≤ b.toNat) && decide (b.toNat ≤ 0x46)) ||
    (decide (0x61 ≤ b.toNat) && decide (b.toNat ≤ 0x66))
/-- The byte after a backslash in a short escape: `"` `\` `/` `b` `f` `n` `r` `t`. -/
def isEscapeByte (b : UInt8) : Bool :=
  b == 0x22 || b == 0x5c || b == 0x2f || b == 0x62 || b == 0x66 || b == 0x6e || b == 0x72 || b == 0x74
inductive StrOut where
  | cont (sub : StrSub)
  | close
  | bad
/-- One byte inside a string. -/
def stepStr : StrSub → UInt8 → StrOut
  | .normal, b =>
    if b == 0x22 then .close else if b == 0x5c then .cont .esc
    else if b.toNat < 0x20 then .bad else if b.toNat < 0x80 then .cont .normal
    else if 0xc2 ≤ b.toNat ∧ b.toNat ≤ 0xdf then .cont (.utf8 0 0x80 0xbf)
    else if b == 0xe0 then .cont (.utf8 1 0xa0 0xbf)
    else if b == 0xed then .cont (.utf8 1 0x80 0x9f)
    else if 0xe1 ≤ b.toNat ∧ b.toNat ≤ 0xef then .cont (.utf8 1 0x80 0xbf)
    else if b == 0xf0 then .cont (.utf8 2 0x90 0xbf)
    else if b == 0xf4 then .cont (.utf8 2 0x80 0x8f)
    else if 0xf1 ≤ b.toNat ∧ b.toNat ≤ 0xf3 then .cont (.utf8 2 0x80 0xbf) else .bad
  | .esc, b => if isEscapeByte b then .cont .normal else if b == 0x75 then .cont .u0 else .bad
  | .u0, b => if b == 0x44 || b == 0x64 then .cont .hexD
      else if isHexDigit b then .cont (.hex 2) else .bad
  | .hexD, b => if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x37 then .cont (.hex 1)
      else if b == 0x38 || b == 0x39 || b == 0x41 || b == 0x42 || b == 0x61 || b == 0x62 then
        .cont (.hiSurr 1)
      else .bad
  | .hiSurr n, b =>
    if isHexDigit b then (match n with | 0 => .cont .afterHi | k + 1 => .cont (.hiSurr k)) else .bad
  | .afterHi, b => if b == 0x5c then .cont .loEsc else .bad
  | .loEsc, b => if b == 0x75 then .cont .loU else .bad
  | .loU, b => if b == 0x44 || b == 0x64 then .cont .loD else .bad
  | .loD, b =>
    if (0x43 ≤ b.toNat ∧ b.toNat ≤ 0x46) ∨ (0x63 ≤ b.toNat ∧ b.toNat ≤ 0x66) then .cont (.hex 1)
    else .bad
  | .hex n, b =>
    if isHexDigit b then (match n with | 0 => .cont .normal | k + 1 => .cont (.hex k)) else .bad
  | .utf8 n lo hi, b =>
    if lo ≤ b.toNat ∧ b.toNat ≤ hi then
      match n with | 0 => .cont .normal | k + 1 => .cont (.utf8 k 0x80 0xbf)
    else .bad
/-- One byte inside a number; `none` when the byte does not continue it. -/
def stepNum : NumSub → UInt8 → Option NumSub
  | .minus, b => if b == 0x30 then some .zero else if isDigit b then some .int else none
  | .zero, b => if b == 0x2e then some .dot else if b == 0x65 || b == 0x45 then some .e else none
  | .int, b =>
    if isDigit b then some .int else if b == 0x2e then some .dot
    else if b == 0x65 || b == 0x45 then some .e else none
  | .dot, b => if isDigit b then some .frac else none
  | .frac, b => if isDigit b then some .frac else if b == 0x65 || b == 0x45 then some .e else none
  | .e, b => if b == 0x2b || b == 0x2d then some .esign else if isDigit b then some .exp else none
  | .esign, b => if isDigit b then some .exp else none
  | .exp, b => if isDigit b then some .exp else none
/-- The number may end here. -/
def numFinal (s : NumSub) : Bool := s matches .zero | .int | .frac | .exp
def failJ (st : JState) : JState := { st with ok := false }
/-- `}`: the innermost bracket is an object and its keys are pairwise distinct. -/
def closeObject (st : JState) : JState :=
  match st.stack with
  | f :: rest =>
    if f.isObj && keysDistinctB f.keys then
      { st with mode := .after, stack := rest, closed := f.keys :: st.closed }
    else failJ st
  | [] => failJ st
/-- `]`: the innermost bracket is an array. -/
def closeArray (st : JState) : JState :=
  match st.stack with
  | f :: rest => if f.isObj then failJ st else { st with mode := .after, stack := rest }
  | [] => failJ st
/-- A byte after a complete value: whitespace, a comma inside a bracket, or the closing bracket. -/
def afterValue (st : JState) (b : UInt8) : JState :=
  if isWs b then { st with mode := .after }
  else if b == 0x2c then
    match st.stack with
    | f :: _ => { st with mode := if f.isObj then .key false else .value false }
    | [] => failJ st
  else if b == 0x5d then closeArray st
  else if b == 0x7d then closeObject st
  else failJ st
/-- The first byte of a value. -/
def startValue (st : JState) (b : UInt8) : JState :=
  if b == 0x7b then { st with mode := .key true, stack := ⟨true, []⟩ :: st.stack }
  else if b == 0x5b then { st with mode := .value true, stack := ⟨false, []⟩ :: st.stack }
  else if b == 0x22 then { st with mode := .str false .normal }
  else if b == 0x2d then { st with mode := .num .minus }
  else if b == 0x30 then { st with mode := .num .zero }
  else if isDigit b then { st with mode := .num .int }
  else if b == 0x74 then { st with mode := .lit [0x72, 0x75, 0x65] }
  else if b == 0x66 then { st with mode := .lit [0x61, 0x6c, 0x73, 0x65] }
  else if b == 0x6e then { st with mode := .lit [0x75, 0x6c, 0x6c] }
  else failJ st
def pushKey (k : ByteArray) : List JFrame → List JFrame
  | f :: rest => { f with keys := k :: f.keys } :: rest
  | [] => []
/-- **One byte of the JSON grammar.** -/
def stepJson (st : JState) (b : UInt8) : JState :=
  match st.mode with
  | .str isKey sub =>
    match stepStr sub b with
    | .bad => failJ st
    | .cont sub' =>
      if isKey then
        { st with mode := .str true sub', curKey := st.curKey.push b, ok := st.ok && b != 0x5c }
      else { st with mode := .str false sub' }
    | .close =>
      if isKey then
        { st with mode := .colon, stack := pushKey st.curKey st.stack, curKey := ByteArray.empty }
      else { st with mode := .after }
  | .value canClose =>
    if isWs b then st else if canClose && b == 0x5d then closeArray st else startValue st b
  | .key canClose =>
    if isWs b then st else if b == 0x22 then { st with mode := .str true .normal }
    else if canClose && b == 0x7d then closeObject st else failJ st
  | .colon => if isWs b then st else if b == 0x3a then { st with mode := .value false } else failJ st
  | .after => afterValue st b
  | .num sub =>
    match stepNum sub b with
    | some sub' => { st with mode := .num sub' }
    | none => if numFinal sub then afterValue st b else failJ st
  | .lit rest =>
    match rest with
    | c :: cs => if b == c then { st with mode := if cs.isEmpty then .after else .lit cs } else failJ st
    | [] => failJ st
/-- The reasoning-tier run. -/
def specRunJson (bs : List UInt8) (st : JState) : JState := bs.foldl stepJson st
/-- A fold over the span `[i, e)` of a buffer, by cursor. -/
def foldBytes {σ : Type} (f : σ → UInt8 → σ) (doc : ByteArray) : Nat → Nat → Nat → σ → σ
  | 0, _, _, st => st
  | fuel + 1, i, e, st => if i < e then foldBytes f doc fuel (i + 1) e (f st (byteAt doc i)) else st
theorem foldBytes_eq {σ : Type} (f : σ → UInt8 → σ) (doc : ByteArray) :
    ∀ (fuel i e : Nat) (st : σ), e ≤ doc.size → e - i ≤ fuel →
      foldBytes f doc fuel i e st = ((doc.data.toList.drop i).take (e - i)).foldl f st
  | 0, i, e, st, _, hf => by
    have hi : ¬ i < e := by omega
    rw [slice_nil doc i e hi]
    rfl
  | fuel + 1, i, e, st, he, hf => by
    unfold foldBytes
    by_cases hi : i < e
    · rw [ite_eq_left hi, slice_cons doc i e hi he]
      exact foldBytes_eq f doc fuel (i + 1) e _ he (by omega)
    · rw [ite_eq_right hi, slice_nil doc i e hi]
      rfl
/-- The machine state after the first `i` bytes. -/
def jsonStateAt (doc : ByteArray) (i : Nat) : JState :=
  foldBytes stepJson doc (min i doc.size) 0 (min i doc.size) JState.init
theorem jsonStateAt_eq (doc : ByteArray) (i : Nat) :
    jsonStateAt doc i = specRunJson (doc.data.toList.take i) JState.init := by
  unfold jsonStateAt specRunJson
  rw [foldBytes_eq stepJson doc _ 0 _ _ (Nat.min_le_right _ _) (by omega)]
  simp only [List.drop_zero, Nat.sub_zero]
  by_cases h : i ≤ doc.size
  · rw [Nat.min_eq_left h]
  · have h1 : doc.data.toList.length ≤ i := by rw [toList_length]; omega
    rw [Nat.min_eq_right (by omega), List.take_of_length_le h1,
      List.take_of_length_le (Nat.le_of_eq (toList_length doc))]
/-- The machine state after the whole document. -/
def jsonRun (doc : ByteArray) : JState := jsonStateAt doc doc.size
theorem jsonRun_eq (doc : ByteArray) : jsonRun doc = specRunJson doc.data.toList JState.init := by
  rw [jsonRun, jsonStateAt_eq, List.take_of_length_le (Nat.le_of_eq (toList_length doc))]
/-- Nothing refused, every bracket closed, and a complete value read. -/
def jsonAccepting (st : JState) : Bool :=
  st.ok && st.stack.isEmpty &&
    match st.mode with
    | .after => true
    | .num sub => numFinal sub
    | _ => false
/-- **The JSON grammar**: the document is one RFC 8259 value with unique keys in every object. -/
def runFullJsonGrammar (doc : ByteArray) : Bool := jsonAccepting (jsonRun doc)
/-- The key sets of the document's objects, innermost-closed first. -/
def jsonObjectKeys (doc : ByteArray) : List (List ByteArray) := (jsonRun doc).closed
/-- A step leaves the closed key sets alone or adds one set of pairwise distinct keys. -/
def ClosedStep (st st' : JState) : Prop :=
  st'.closed = st.closed ∨ ∃ ks : List ByteArray, ks.Nodup ∧ st'.closed = ks :: st.closed
theorem closeObject_closed (st : JState) : ClosedStep st (closeObject st) := by
  unfold closeObject
  split
  · split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact Or.inr ⟨_, keysDistinctB_sound h.2, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl
theorem closeArray_closed (st : JState) : ClosedStep st (closeArray st) := by
  unfold closeArray
  repeat' split
  all_goals exact Or.inl rfl
theorem afterValue_closed (st : JState) (b : UInt8) : ClosedStep st (afterValue st b) := by
  unfold afterValue
  repeat' split
  all_goals first | exact Or.inl rfl | exact closeArray_closed st | exact closeObject_closed st
theorem startValue_closed (st : JState) (b : UInt8) : ClosedStep st (startValue st b) := by
  unfold startValue
  repeat' split
  all_goals exact Or.inl rfl
theorem stepJson_closed (st : JState) (b : UInt8) : ClosedStep st (stepJson st b) := by
  unfold stepJson
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact closeArray_closed st
    | exact closeObject_closed st
    | exact afterValue_closed st b
    | exact startValue_closed st b
theorem specRunJson_closed_nodup : ∀ (bs : List UInt8) (st : JState),
    (∀ ks ∈ st.closed, ks.Nodup) → ∀ ks ∈ (specRunJson bs st).closed, ks.Nodup
  | [], _, h => h
  | b :: bs, st, h => by
    refine specRunJson_closed_nodup bs (stepJson st b) ?_
    rcases stepJson_closed st b with he | ⟨ks, hn, he⟩
    · rw [he]; exact h
    · rw [he]
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hn
      · exact h k hk
/-- **Unique keys at every depth**: every object the grammar closed has pairwise distinct keys. -/
theorem json_object_keys_nodup (doc : ByteArray) : ∀ ks ∈ jsonObjectKeys doc, ks.Nodup := by
  unfold jsonObjectKeys
  rw [jsonRun_eq]
  exact specRunJson_closed_nodup _ _ (fun _ hk => by cases hk)
/-! ### Redaction -/
/-- **A byte a mask may write**: printable ASCII other than `"` and `\`. -/
def isSafeMaskByte (b : UInt8) : Bool :=
  decide (0x20 ≤ b.toNat) && decide (b.toNat ≤ 0x7e) && b != 0x22 && b != 0x5c
/-- Inside a value string, with nothing refused. -/
def inValueString (st : JState) : Bool :=
  st.ok && match st.mode with
    | .str false _ => true
    | _ => false
/-- Walk a span, staying inside the value string after every byte. -/
def walkInterior : JState → List UInt8 → Option JState
  | st, [] => some st
  | st, b :: bs => if inValueString (stepJson st b) then walkInterior (stepJson st b) bs else none
theorem walkInterior_run : ∀ (bs : List UInt8) (st st' : JState),
    walkInterior st bs = some st' → specRunJson bs st = st'
  | [], _, _, h => by cases h; rfl
  | b :: bs, st, st', h => by
    simp only [walkInterior] at h
    split at h
    · exact walkInterior_run bs _ st' h
    · cases h
/-- **The redaction check**: the span starts in a value string outside any escape, every byte of
it stays inside that string, the machine is back in the starting state at its end, and the mask
is made of safe bytes. -/
def checkJsonRedaction (doc : ByteArray) (l r : Nat) (mask : ByteArray) : Bool :=
  decide (l ≤ r) && decide (r ≤ doc.size) &&
    decide ((jsonStateAt doc l).mode = .str false .normal) &&
    decide (walkInterior (jsonStateAt doc l) ((doc.data.toList.drop l).take (r - l)) =
      some (jsonStateAt doc l)) &&
    mask.data.toList.all isSafeMaskByte
/-- A safe byte inside a value string leaves the whole machine state unchanged. -/
theorem stepJson_safe {st : JState} {b : UInt8} (hm : st.mode = .str false .normal)
    (hb : isSafeMaskByte b = true) : stepJson st b = st := by
  simp only [isSafeMaskByte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
  obtain ⟨⟨⟨h20, h7e⟩, hq⟩, hbs⟩ := hb
  have h1 : (b == 0x22) = false := beq_eq_false_iff_ne.2 hq
  have h2 : (b == 0x5c) = false := beq_eq_false_iff_ne.2 hbs
  have h3 : decide (b.toNat < 0x20) = false := decide_eq_false (by omega)
  obtain ⟨mode, stack, curKey, closed, ok⟩ := st
  simp only at hm
  subst hm
  simp [stepJson, stepStr, h1, h2, show ¬ b.toNat < 0x20 by omega,
    show b.toNat < 0x80 by omega]
theorem specRunJson_safe {st : JState} (hm : st.mode = .str false .normal) :
    ∀ (bs : List UInt8), bs.all isSafeMaskByte = true → specRunJson bs st = st
  | [], _ => rfl
  | b :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [specRunJson, List.foldl_cons]
    rw [stepJson_safe hm h.1]
    exact specRunJson_safe hm bs h.2
theorem specRunJson_append (xs ys : List UInt8) (st : JState) :
    specRunJson (xs ++ ys) st = specRunJson ys (specRunJson xs st) := by
  simp only [specRunJson, List.foldl_append]
/-- The core of redaction: after the mask the machine is where it was after the span, so any
continuation runs alike. -/
theorem redaction_core {doc : ByteArray} {l r : Nat} {mask : ByteArray}
    (h : checkJsonRedaction doc l r mask = true) (t : List UInt8) :
    specRunJson (doc.data.toList.take l ++ mask.data.toList ++ t) JState.init =
      specRunJson (doc.data.toList.take r ++ t) JState.init := by
  simp only [checkJsonRedaction, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlr, _⟩, hmode⟩, hwalk⟩, hmask⟩ := h
  rw [jsonStateAt_eq] at hmode hwalk
  have hsplit : doc.data.toList.take r =
      doc.data.toList.take l ++ (doc.data.toList.drop l).take (r - l) := by
    have : r = l + (r - l) := by omega
    rw [this, List.take_add]
    simp
  rw [hsplit, specRunJson_append, specRunJson_append, specRunJson_append, specRunJson_append,
    specRunJson_safe hmode _ hmask, walkInterior_run _ _ _ hwalk]
/-- After an accepted redaction the whole run ends in the original's final state. -/
theorem jsonRedaction_run {doc : ByteArray} {l r : Nat} {mask : ByteArray}
    (h : checkJsonRedaction doc l r mask = true) :
    jsonRun (spliceByteArray doc l r mask) = jsonRun doc := by
  rw [jsonRun_eq, jsonRun_eq, spliceByteArray_toList, redaction_core h, List.take_append_drop]
/-- **Redaction preserves the parse.** After an accepted redaction the document has the
original's grammar verdict and the original's object key sets, and at every cut `j` bytes after
the mask the machine (bracket stack included) is in the state the original was in `j` bytes
after the span. -/
theorem jsonRedaction_preserves_valid_parse_and_keys {doc : ByteArray} {l r : Nat}
    {mask : ByteArray} (h : checkJsonRedaction doc l r mask = true) :
    runFullJsonGrammar (spliceByteArray doc l r mask) = runFullJsonGrammar doc ∧
      jsonObjectKeys (spliceByteArray doc l r mask) = jsonObjectKeys doc ∧
      ∀ j, specRunJson (doc.data.toList.take l ++ mask.data.toList ++
          (doc.data.toList.drop r).take j) JState.init = jsonStateAt doc (r + j) := by
  have hrun := jsonRedaction_run h
  refine ⟨by unfold runFullJsonGrammar; rw [hrun], by unfold jsonObjectKeys; rw [hrun], fun j => ?_⟩
  rw [redaction_core h, jsonStateAt_eq, List.take_add]
/-- **Redaction confinement.** Two documents whose redactions are both accepted and that agree
outside their spans redact to the same bytes, so they have one final machine state, verdict and
object key sets: what differs inside the spans reaches nothing the grammar reads. -/
theorem jsonRedaction_confinement {doc₁ doc₂ : ByteArray} {l r₁ r₂ : Nat} {mask : ByteArray}
    (h₁ : checkJsonRedaction doc₁ l r₁ mask = true) (h₂ : checkJsonRedaction doc₂ l r₂ mask = true)
    (hpre : doc₁.data.toList.take l = doc₂.data.toList.take l)
    (hpost : doc₁.data.toList.drop r₁ = doc₂.data.toList.drop r₂) :
    spliceByteArray doc₁ l r₁ mask = spliceByteArray doc₂ l r₂ mask ∧ jsonRun doc₁ = jsonRun doc₂ ∧
      runFullJsonGrammar doc₁ = runFullJsonGrammar doc₂ ∧ jsonObjectKeys doc₁ = jsonObjectKeys doc₂ := by
  have he : spliceByteArray doc₁ l r₁ mask = spliceByteArray doc₂ l r₂ mask := by
    apply byteArray_eq_of_toList
    rw [spliceByteArray_toList, spliceByteArray_toList, hpre, hpost]
  have hrun : jsonRun doc₁ = jsonRun doc₂ := by
    rw [← jsonRedaction_run h₁, ← jsonRedaction_run h₂, he]
  exact ⟨he, hrun, by unfold runFullJsonGrammar; rw [hrun], by unfold jsonObjectKeys; rw [hrun]⟩
/-! ## 3. Merkle inclusion of a single span -/
/-- The customization string of the span tree. -/
def spanTag : String := "obend.judge.span.merkle.v1"
/-- The first bytes of a leaf message and of a node message. -/
def leafPrefix : UInt8 := 0x00
def nodePrefix : UInt8 := 0x01
def rootPrefix : UInt8 := 0x02
/-- A leaf message: the prefix, the span's length in eight bytes, the span. -/
def leafMsg (span : ByteArray) : ByteArray :=
  ⟨(leafPrefix :: (beNat 8 span.size ++ span.data.toList)).toArray⟩
def pairMsg (pre : UInt8) (l r : ByteArray) : ByteArray :=
  ⟨(pre :: (l.data.toList ++ r.data.toList)).toArray⟩
/-- A node message: the prefix and the two children. -/
def nodeMsg (l r : ByteArray) : ByteArray := pairMsg nodePrefix l r
def rootMsg (countDigest top : ByteArray) : ByteArray := pairMsg rootPrefix countDigest top
def leafHash (H : Hasher) (tag : String) (span : ByteArray) : ByteArray := H.hash tag (leafMsg span)
def nodeHash (H : Hasher) (tag : String) (l r : ByteArray) : ByteArray := H.hash tag (nodeMsg l r)
theorem leafMsg_injective {a b : ByteArray} (h : leafMsg a = leafMsg b) : a = b := by
  have hl := congrArg (fun x : ByteArray => x.data.toList) h
  simp only [leafMsg, List.cons.injEq, true_and] at hl
  exact byteArray_eq_of_toList
    (List.append_inj hl (by rw [beNat_length, beNat_length])).2
theorem pairMsg_injective {pre : UInt8} {a b c d : ByteArray} (h : pairMsg pre a b = pairMsg pre c d)
    (hs : a.size = c.size) : a = c ∧ b = d := by
  have hl := congrArg (fun x : ByteArray => x.data.toList) h
  simp only [pairMsg, List.cons.injEq, true_and] at hl
  obtain ⟨h1, h2⟩ := List.append_inj hl (by rw [toList_length, toList_length, hs])
  exact ⟨byteArray_eq_of_toList h1, byteArray_eq_of_toList h2⟩
theorem nodeMsg_injective {a b c d : ByteArray} (h : nodeMsg a b = nodeMsg c d)
    (hs : a.size = c.size) : a = c ∧ b = d := pairMsg_injective h hs
/-- **Domain separation**: no leaf message is a node message. -/
theorem leafMsg_ne_nodeMsg (span l r : ByteArray) : leafMsg span ≠ nodeMsg l r := by
  intro h
  have hl := congrArg (fun x : ByteArray => x.data.toList.head?) h
  simp [leafMsg, nodeMsg, pairMsg, leafPrefix, nodePrefix] at hl
/-- A span whose leaf digest is a node digest gives two different messages with one digest. -/
theorem leaf_as_node_collision (H : Hasher) (tag : String) {span l r : ByteArray}
    (h : leafHash H tag span = nodeHash H tag l r) :
    ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash tag m₁ = H.hash tag m₂ :=
  ⟨leafMsg span, nodeMsg l r, leafMsg_ne_nodeMsg span l r, h⟩
/-- One level up: adjacent pairs hashed, an odd last node promoted. -/
def pairUp (H : Hasher) (tag : String) : List ByteArray → List ByteArray
  | a :: b :: rest => nodeHash H tag a b :: pairUp H tag rest
  | [a] => [a]
  | [] => []
/-- The top of the tree over a level, at a fuel. -/
def treeTop (H : Hasher) (tag : String) : Nat → List ByteArray → ByteArray
  | 0, lvl => lvl.headD ByteArray.empty
  | f + 1, lvl => if lvl.length ≤ 1 then lvl.headD ByteArray.empty else treeTop H tag f (pairUp H tag lvl)
/-- The committed root: the leaf count and the 32-byte top (the digest of count and tree top). -/
structure SpanRoot where
  count : Nat
  top : ByteArray
  deriving DecidableEq
def rootHash (H : Hasher) (tag : String) (count : Nat) (treeTop : ByteArray) : ByteArray :=
  H.hash tag (rootMsg (leafHash H tag (countSpan count)) treeTop)
/-- **The root binds the count**: one root digest, one count and one tree top, or a collision. -/
theorem rootHash_binds (H : Hasher) (tag : String) {n₁ n₂ : Nat} {t₁ t₂ : ByteArray}
    (h : rootHash H tag n₁ t₁ = rootHash H tag n₂ t₂) :
    (n₁ = n₂ ∧ t₁ = t₂) ∨ ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash tag m₁ = H.hash tag m₂ := by
  by_cases hm : rootMsg (leafHash H tag (countSpan n₁)) t₁ =
      rootMsg (leafHash H tag (countSpan n₂)) t₂
  · obtain ⟨hc, ht⟩ := pairMsg_injective hm ((H.size_eq _ _).trans (H.size_eq _ _).symm)
    by_cases hl : leafMsg (countSpan n₁) = leafMsg (countSpan n₂)
    · exact Or.inl ⟨countSpan_injective (leafMsg_injective hl), ht⟩
    · exact Or.inr ⟨_, _, hl, hc⟩
  · exact Or.inr ⟨_, _, hm, h⟩
/-- **The root of a span set.** -/
def spanMerkleRoot (H : Hasher) (tag : String) (spans : List ByteArray) : SpanRoot :=
  ⟨spans.length, rootHash H tag spans.length (treeTop H tag spans.length (spans.map (leafHash H tag)))⟩
/-- **Span roots of different lengths do not share a `top`**, short of a collision. -/
theorem spanMerkleRoot_top_binds_count (H : Hasher) (tag : String) {s₁ s₂ : List ByteArray}
    (h : (spanMerkleRoot H tag s₁).top = (spanMerkleRoot H tag s₂).top) :
    s₁.length = s₂.length ∨ ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash tag m₁ = H.hash tag m₂ :=
  (rootHash_binds H tag (n₁ := s₁.length) (n₂ := s₂.length) h).imp And.left id
/-- Climb from a node at index `i` of a level of `n` nodes, consuming one sibling per level
unless the node is a promoted last one. -/
def climbSpan (H : Hasher) (tag : String) : Nat → Nat → Nat → ByteArray → List ByteArray → Option ByteArray
  | 0, _, _, _, _ => none
  | f + 1, n, i, c, path =>
    if n ≤ 1 then (if path.isEmpty then some c else none)
    else if i % 2 = 0 ∧ i + 1 = n then climbSpan H tag f ((n + 1) / 2) (i / 2) c path
    else
      match path with
      | [] => none
      | sib :: rest =>
        if sib.size = 32 then
          climbSpan H tag f ((n + 1) / 2) (i / 2)
            (if i % 2 = 0 then nodeHash H tag c sib else nodeHash H tag sib c) rest
        else none
/-- An inclusion proof: the index and the siblings, leaf level first. -/
structure SpanProof where
  index : Nat
  siblings : List ByteArray
def topMatches (H : Hasher) (tag : String) (root : SpanRoot) (computed : ByteArray) : Bool :=
  decide (rootHash H tag root.count computed = root.top)
/-- **Verify one span against a root.** -/
def verifySpanMerkleInclusion (H : Hasher) (tag : String) (root : SpanRoot) (span : ByteArray) (p : SpanProof) :
    Bool :=
  decide (p.index < root.count) &&
    match climbSpan H tag root.count root.count p.index (leafHash H tag span) p.siblings with
    | some c => topMatches H tag root c
    | none => false
theorem pairUp_length (H : Hasher) (tag : String) : ∀ l : List ByteArray, (pairUp H tag l).length = (l.length + 1) / 2
  | [] => rfl
  | [_] => by simp [pairUp]
  | _ :: _ :: rest => by
    simp only [pairUp, List.length_cons, pairUp_length H tag rest]
    omega
theorem pairUp_sizes (H : Hasher) (tag : String) : ∀ l : List ByteArray, (∀ y ∈ l, y.size = 32) →
    ∀ y ∈ pairUp H tag l, y.size = 32
  | [], _, _, hy => by cases hy
  | [a], h, y, hy => h y hy
  | a :: b :: rest, h, y, hy => by
    simp only [pairUp, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact H.size_eq _ _
    · exact pairUp_sizes H tag rest (fun z hz => h z (by simp [hz])) y hy
/-- Where the node at index `i` goes one level up: promoted, a left child, or a right child. -/
theorem pairUp_get (H : Hasher) (tag : String) : ∀ (l : List ByteArray) (i : Nat) (x : ByteArray), l[i]? = some x →
    (i % 2 = 0 ∧ i + 1 = l.length ∧ (pairUp H tag l)[i / 2]? = some x) ∨
    (i % 2 = 0 ∧ ∃ y, l[i + 1]? = some y ∧ (pairUp H tag l)[i / 2]? = some (nodeHash H tag x y)) ∨
    (i % 2 = 1 ∧ ∃ y, l[i - 1]? = some y ∧ (pairUp H tag l)[i / 2]? = some (nodeHash H tag y x))
  | [], _, _, h => by simp at h
  | [a], i, x, h => by
    cases i with
    | zero => simp at h; subst h; exact Or.inl ⟨rfl, rfl, rfl⟩
    | succ i => simp at h
  | a :: b :: rest, i, x, h => by
    match i, h with
    | 0, h => simp at h; subst h; exact Or.inr (Or.inl ⟨rfl, b, rfl, rfl⟩)
    | 1, h => simp at h; subst h; exact Or.inr (Or.inr ⟨rfl, a, rfl, rfl⟩)
    | i + 2, h =>
      have h' : rest[i]? = some x := by simpa using h
      have e2 : (i + 2) / 2 = i / 2 + 1 := by omega
      have hp : (pairUp H tag (a :: b :: rest))[(i + 2) / 2]? = (pairUp H tag rest)[i / 2]? := by
        rw [e2]; rfl
      rcases pairUp_get H tag rest i x h' with ⟨h1, h2, h3⟩ | ⟨h1, y, h2, h3⟩ | ⟨h1, y, h2, h3⟩
      · exact Or.inl ⟨by omega, by simp only [List.length_cons]; omega, by rw [hp]; exact h3⟩
      · refine Or.inr (Or.inl ⟨by omega, y, ?_, by rw [hp]; exact h3⟩)
        simpa using h2
      · refine Or.inr (Or.inr ⟨by omega, y, ?_, by rw [hp]; exact h3⟩)
        have hi : i + 2 - 1 = (i - 1) + 2 := by omega
        rw [hi]
        simpa using h2
/-- The lockstep argument: a climb that reaches the top of a level's tree started from that
level's node at the index, or a node message collides. -/
theorem climb_binds (H : Hasher) (tag : String) : ∀ (f : Nat) (lvl : List ByteArray) (i : Nat)
    (c x : ByteArray) (path : List ByteArray), (∀ y ∈ lvl, y.size = 32) → c.size = 32 →
    lvl[i]? = some x → climbSpan H tag f lvl.length i c path = some (treeTop H tag f lvl) →
    c = x ∨ ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash tag m₁ = H.hash tag m₂
  | 0, _, _, _, _, _, _, _, _, h => by simp [climbSpan] at h
  | f + 1, lvl, i, c, x, path, hsz, hc, hx, h => by
    have hxs : x.size = 32 := hsz x (List.mem_of_getElem? hx)
    have hilt : i < lvl.length := (List.getElem?_eq_some_iff.1 hx).1
    simp only [climbSpan, treeTop] at h
    by_cases hn : lvl.length ≤ 1
    · simp only [hn, ↓reduceIte] at h
      have hi0 : i = 0 := by omega
      subst hi0
      match lvl, hx with
      | y :: _, hx =>
        simp at hx; subst hx
        split at h
        · simp at h; exact Or.inl h
        · cases h
    · simp only [hn, ↓reduceIte] at h
      have hlen := pairUp_length H tag lvl
      have hsz' := pairUp_sizes H tag lvl hsz
      rcases pairUp_get H tag lvl i x hx with ⟨h1, h2, h3⟩ | ⟨h1, y, h2, h3⟩ | ⟨h1, y, h2, h3⟩
      · have hp : i % 2 = 0 ∧ i + 1 = lvl.length := ⟨h1, h2⟩
        simp only [hp, and_self, ↓reduceIte] at h
        rw [← hlen] at h
        exact climb_binds H tag f (pairUp H tag lvl) (i / 2) c x path hsz' hc h3 h
      · have hy : i + 1 < lvl.length := (List.getElem?_eq_some_iff.1 h2).1
        have hp : ¬ (i % 2 = 0 ∧ i + 1 = lvl.length) := fun hh => by omega
        simp only [hp, ↓reduceIte] at h
        match path, h with
        | sib :: rest, h =>
          simp only [h1, ↓reduceIte] at h
          split at h
          · rename_i hsib
            rw [← hlen] at h
            rcases climb_binds H tag f (pairUp H tag lvl) (i / 2) _ _ rest hsz' (H.size_eq _ _) h3 h with
              he | hcol
            · by_cases hm : nodeMsg c sib = nodeMsg x y
              · exact Or.inl (nodeMsg_injective hm (hc.trans hxs.symm)).1
              · exact Or.inr ⟨_, _, hm, he⟩
            · exact Or.inr hcol
          · cases h
      · have hp : ¬ (i % 2 = 0 ∧ i + 1 = lvl.length) := fun hh => by omega
        have hodd : ¬ i % 2 = 0 := by omega
        have hys : y.size = 32 := hsz y (List.mem_of_getElem? h2)
        simp only [hp, ↓reduceIte] at h
        match path, h with
        | sib :: rest, h =>
          simp only [hodd, ↓reduceIte] at h
          split at h
          · rename_i hsib
            rw [← hlen] at h
            rcases climb_binds H tag f (pairUp H tag lvl) (i / 2) _ _ rest hsz' (H.size_eq _ _) h3 h with
              he | hcol
            · by_cases hm : nodeMsg sib c = nodeMsg y x
              · exact Or.inl (nodeMsg_injective hm (hsib.trans hys.symm)).2
              · exact Or.inr ⟨_, _, hm, he⟩
            · exact Or.inr hcol
          · cases h
/-- **Inclusion proofs bind, by the `top` alone.** A span that verifies at an index against a root
whose `top` is that of a span set, whatever count it claims, is that span, or a collision. -/
theorem verifySpanMerkleInclusion_top_binding (H : Hasher) (tag : String) {spans : List ByteArray}
    {root : SpanRoot} {span : ByteArray} {p : SpanProof}
    (htop : root.top = (spanMerkleRoot H tag spans).top) :
    verifySpanMerkleInclusion H tag root span p = true →
    spans[p.index]? = some span ∨
      ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash tag m₁ = H.hash tag m₂ := by
  intro h
  simp only [verifySpanMerkleInclusion, Bool.and_eq_true] at h
  obtain ⟨hidx', hm⟩ := h
  split at hm
  · rename_i c hcl
    have hr : rootHash H tag root.count c =
        rootHash H tag spans.length (treeTop H tag spans.length (spans.map (leafHash H tag))) :=
      (of_decide_eq_true hm).trans htop
    rcases rootHash_binds H tag hr with ⟨hn, hc⟩ | hcol
    case inr => exact Or.inr hcol
    rw [hn] at hcl hidx'
    have hidx : p.index < spans.length := of_decide_eq_true hidx'
    rw [hc] at hcl
    have hlen : (spans.map (leafHash H tag)).length = spans.length := List.length_map _
    have hget : (spans.map (leafHash H tag))[p.index]? = some (leafHash H tag (spans[p.index]'hidx)) := by
      simp [List.getElem?_eq_getElem hidx]
    have hcl' : climbSpan H tag spans.length (spans.map (leafHash H tag)).length p.index (leafHash H tag span)
        p.siblings = some (treeTop H tag spans.length (spans.map (leafHash H tag))) := by rw [hlen]; exact hcl
    rcases climb_binds H tag spans.length _ p.index _ _ p.siblings
        (fun y hy => by
          obtain ⟨s, _, rfl⟩ := List.mem_map.1 hy
          exact H.size_eq _ _)
        (H.size_eq _ _) hget hcl' with he | hcol
    · by_cases hmsg : leafMsg span = leafMsg (spans[p.index]'hidx)
      · exact Or.inl (by rw [List.getElem?_eq_getElem hidx, leafMsg_injective hmsg])
      · exact Or.inr ⟨_, _, hmsg, he⟩
    · exact Or.inr hcol
  · cases hm
/-- The siblings on the way up from index `i`. -/
def spanPath (H : Hasher) (tag : String) : Nat → List ByteArray → Nat → List ByteArray
  | 0, _, _ => []
  | f + 1, lvl, i =>
    if lvl.length ≤ 1 then []
    else if i % 2 = 0 then
      match lvl[i + 1]? with
      | some y => y :: spanPath H tag f (pairUp H tag lvl) (i / 2)
      | none => spanPath H tag f (pairUp H tag lvl) (i / 2)
    else lvl.getD (i - 1) ByteArray.empty :: spanPath H tag f (pairUp H tag lvl) (i / 2)
/-- **The inclusion proof of the span at an index.** -/
def spanMerkleProof (H : Hasher) (tag : String) (spans : List ByteArray) (i : Nat) : SpanProof :=
  ⟨i, spanPath H tag spans.length (spans.map (leafHash H tag)) i⟩
theorem climb_complete (H : Hasher) (tag : String) : ∀ (f : Nat) (lvl : List ByteArray) (i : Nat) (x : ByteArray),
    (∀ y ∈ lvl, y.size = 32) → lvl[i]? = some x → lvl.length ≤ f →
    climbSpan H tag f lvl.length i x (spanPath H tag f lvl i) = some (treeTop H tag f lvl)
  | 0, lvl, i, x, _, hx, hf => by
    have : lvl = [] := List.length_eq_zero_iff.1 (by omega)
    subst this; simp at hx
  | f + 1, lvl, i, x, hsz, hx, hf => by
    have hilt : i < lvl.length := (List.getElem?_eq_some_iff.1 hx).1
    simp only [climbSpan, treeTop, spanPath]
    by_cases hn : lvl.length ≤ 1
    · simp only [hn, ↓reduceIte, List.isEmpty_nil]
      have hi0 : i = 0 := by omega
      subst hi0
      match lvl, hx with
      | y :: _, hx => simp at hx; subst hx; rfl
    · simp only [hn, ↓reduceIte]
      have hlen := pairUp_length H tag lvl
      have hsz' := pairUp_sizes H tag lvl hsz
      have hf' : (pairUp H tag lvl).length ≤ f := by rw [hlen]; omega
      rcases pairUp_get H tag lvl i x hx with ⟨h1, h2, h3⟩ | ⟨h1, y, h2, h3⟩ | ⟨h1, y, h2, h3⟩
      · have hnone : lvl[i + 1]? = none := List.getElem?_eq_none (by omega)
        rw [ite_eq_left ⟨h1, h2⟩]
        simp only [h1, ↓reduceIte, hnone]
        rw [← hlen]
        exact climb_complete H tag f (pairUp H tag lvl) (i / 2) x hsz' h3 hf'
      · have hy : i + 1 < lvl.length := (List.getElem?_eq_some_iff.1 h2).1
        have hp : ¬ (i % 2 = 0 ∧ i + 1 = lvl.length) := fun hh => by omega
        have hys : y.size = 32 := hsz y (List.mem_of_getElem? h2)
        rw [ite_eq_right hp]
        simp only [h1, h2, hys, ↓reduceIte]
        rw [← hlen]
        exact climb_complete H tag f (pairUp H tag lvl) (i / 2) _ hsz' h3 hf'
      · have hp : ¬ (i % 2 = 0 ∧ i + 1 = lvl.length) := fun hh => by omega
        have hodd : ¬ i % 2 = 0 := by omega
        have hys : y.size = 32 := hsz y (List.mem_of_getElem? h2)
        have hgd : lvl.getD (i - 1) ByteArray.empty = y := by
          rw [List.getD_eq_getElem?_getD, h2]; rfl
        rw [ite_eq_right hp]
        simp only [hodd, hgd, hys, ↓reduceIte]
        rw [← hlen]
        exact climb_complete H tag f (pairUp H tag lvl) (i / 2) _ hsz' h3 hf'
/-- **Completeness**: the honest proof of the span at any index verifies. -/
theorem verifySpanMerkleInclusion_complete (H : Hasher) (tag : String) (spans : List ByteArray) (i : Nat)
    (hi : i < spans.length) :
    verifySpanMerkleInclusion H tag (spanMerkleRoot H tag spans) (spans[i]'hi)
      (spanMerkleProof H tag spans i) = true := by
  have hlen : (spans.map (leafHash H tag)).length = spans.length := List.length_map _
  have hget : (spans.map (leafHash H tag))[i]? = some (leafHash H tag (spans[i]'hi)) := by
    simp [List.getElem?_eq_getElem hi]
  have hcl := climb_complete H tag spans.length (spans.map (leafHash H tag)) i _
    (fun y hy => by
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 hy
      exact H.size_eq _ _) hget (Nat.le_of_eq hlen)
  rw [hlen] at hcl
  simp [verifySpanMerkleInclusion, spanMerkleRoot, spanMerkleProof, hi, hcl, topMatches]
/-! ## 4. The span-disclosure judge and the byte format `vpa-json-span@1` -/
/-- A disclosure claim: `redacted` is `doc` with the span `[l, r)` replaced by `mask`. -/
structure JsonSpanClaim where
  doc : ByteArray
  l : Nat
  r : Nat
  mask : ByteArray
  redacted : ByteArray
/-- The certificate: a commitment to spans of the document and the opening of the hidden one. -/
structure JsonSpanCert where
  root : SpanRoot
  proof : SpanProof
def hiddenSpan (o : JsonSpanClaim) : ByteArray := o.doc.extract o.l o.r
/-- The document as three spans: before the hidden span, the hidden span, after it. -/
def spansOf (o : JsonSpanClaim) : List ByteArray :=
  [o.doc.extract 0 o.l, hiddenSpan o, o.doc.extract o.r o.doc.size]
def jsonSpanCertOf (o : JsonSpanClaim) : JsonSpanCert :=
  ⟨spanMerkleRoot cshakeHasher spanTag (spansOf o), spanMerkleProof cshakeHasher spanTag (spansOf o) 1⟩
/-- An accepted disclosure: the disclosed bytes are the splice and parse as the original does, and
under every span set with the certificate's root the opened leaf is the hidden span (or collision). -/
def JsonSpanMeaning (o : JsonSpanClaim) (c : JsonSpanCert) : Prop :=
  o.redacted = spliceByteArray o.doc o.l o.r o.mask ∧
    runFullJsonGrammar o.redacted = runFullJsonGrammar o.doc ∧
    jsonObjectKeys o.redacted = jsonObjectKeys o.doc ∧
    ∀ spans : List ByteArray, spanMerkleRoot cshakeHasher spanTag spans = c.root →
      spans[c.proof.index]? = some (hiddenSpan o) ∨
        ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ cshakeHasher.hash spanTag m₁ = cshakeHasher.hash spanTag m₂
inductive JsonSpanRefusal where
  /-- the disclosed bytes are not the document with the span replaced: refutes the claim -/
  | notTheSplice
  /-- the span is not confined to one value string, or the mask is not safe -/
  | unconfined
  /-- the opening does not reach the root -/
  | unopened
  deriving DecidableEq
def jsonSpanCheck (o : JsonSpanClaim) (c : JsonSpanCert) : Judge.Verdict JsonSpanRefusal :=
  if o.redacted ≠ spliceByteArray o.doc o.l o.r o.mask then .refused .notTheSplice []
  else if checkJsonRedaction o.doc o.l o.r o.mask = false then .refused .unconfined [o.l, o.r]
  else if verifySpanMerkleInclusion cshakeHasher spanTag c.root (hiddenSpan o) c.proof = false then
    .refused .unopened [c.proof.index]
  else .ok
theorem jsonSpanCheck_ok {o : JsonSpanClaim} {c : JsonSpanCert} (h : jsonSpanCheck o c = .ok) :
    o.redacted = spliceByteArray o.doc o.l o.r o.mask ∧
      checkJsonRedaction o.doc o.l o.r o.mask = true ∧
      verifySpanMerkleInclusion cshakeHasher spanTag c.root (hiddenSpan o) c.proof = true := by
  unfold jsonSpanCheck at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      split at h
      · cases h
      · rename_i h3
        exact ⟨Decidable.not_not.mp h1, by simpa using h2, by simpa using h3⟩
/-- **The span-disclosure judge.** A splice mismatch refutes the claim under every certificate;
completeness is claimed where the redaction check confines the span. -/
instance jsonSpanJudge : Judge JsonSpanClaim JsonSpanCert where
  Clause := JsonSpanRefusal
  Meaning := JsonSpanMeaning
  check _ := jsonSpanCheck
  sound := by
    intro _ o c h
    obtain ⟨hs, hr, hi⟩ := jsonSpanCheck_ok h
    obtain ⟨hv, hk, _⟩ := jsonRedaction_preserves_valid_parse_and_keys hr
    refine ⟨hs, by rw [hs]; exact hv, by rw [hs]; exact hk, fun spans hroot => ?_⟩
    rw [← hroot] at hi
    exact verifySpanMerkleInclusion_top_binding cshakeHasher spanTag rfl hi
  refutes k := decide (k = .notTheSplice)
  refuted := by
    intro _ o c k p h hk c' hm
    have hk' : k = .notTheSplice := of_decide_eq_true hk
    subst hk'
    unfold jsonSpanCheck at h
    split at h
    · rename_i hne; exact hne hm.1
    · split at h
      · cases h
      · split at h <;> cases h
  Fragment o := o.l ≤ o.r ∧ o.r ≤ o.doc.size ∧
    (jsonStateAt o.doc o.l).mode = .str false .normal ∧
    walkInterior (jsonStateAt o.doc o.l) ((o.doc.data.toList.drop o.l).take (o.r - o.l)) =
      some (jsonStateAt o.doc o.l) ∧ ∀ b ∈ o.mask.data.toList, isSafeMaskByte b = true
  complete := by
    rintro o hfrag ⟨_, hm⟩
    have hr : checkJsonRedaction o.doc o.l o.r o.mask = true := by
      simpa only [checkJsonRedaction, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        and_assoc] using hfrag
    have hi : verifySpanMerkleInclusion cshakeHasher spanTag (jsonSpanCertOf o).root (hiddenSpan o)
        (jsonSpanCertOf o).proof = true :=
      verifySpanMerkleInclusion_complete cshakeHasher spanTag (spansOf o) 1 (by simp [spansOf])
    refine ⟨jsonSpanCertOf o, 0, ?_⟩
    show jsonSpanCheck o (jsonSpanCertOf o) = .ok
    simp [jsonSpanCheck, hm.1, hr, hi]
  mono := by intro _ _ _ _ _ _; rfl
def encodeJsonSpanClaim (o : JsonSpanClaim) : String :=
  ":".intercalate [hexOf o.doc, toString o.l, toString o.r, hexOf o.mask, hexOf o.redacted]
def decodeJsonSpanClaim (s : String) : Except String JsonSpanClaim :=
  match s.splitOn ":" with
  | [d, l, r, m, x] =>
    match unhex d, natField l, natField r, unhex m, unhex x with
    | .ok d, .ok l, .ok r, .ok m, .ok x => .ok ⟨d, l, r, m, x⟩
    | _, _, _, _, _ => .error "a span claim is hex:dec:dec:hex:hex"
  | _ => .error "a span claim is five fields"
def encodeJsonSpanCert (c : JsonSpanCert) : String :=
  ":".intercalate (toString c.root.count :: hexOf c.root.top :: toString c.proof.index ::
    c.proof.siblings.map hexOf)
def decodeJsonSpanCert (s : String) : Except String JsonSpanCert :=
  match s.splitOn ":" with
  | n :: t :: i :: sibs =>
    match natField n, unhex t, natField i, sibs.mapM unhex with
    | .ok n, .ok t, .ok i, .ok ss => .ok ⟨⟨n, t⟩, ⟨i, ss⟩⟩
    | _, _, _, _ => .error "a span certificate is dec:hex:dec then hex siblings"
  | _ => .error "a span certificate has at least three fields"
def plantedJsonSpanClaim : JsonSpanClaim := ⟨⟨#[]⟩, 0, 0, ⟨#[]⟩, ⟨#[0]⟩⟩
theorem plantedJsonSpan_refused :
    ∃ k p, jsonSpanJudge.check 0 plantedJsonSpanClaim (jsonSpanCertOf plantedJsonSpanClaim) =
      .refused k p := by
  have hne : plantedJsonSpanClaim.redacted ≠ spliceByteArray plantedJsonSpanClaim.doc
      plantedJsonSpanClaim.l plantedJsonSpanClaim.r plantedJsonSpanClaim.mask := by
    intro h
    have hl := congrArg (fun b : ByteArray => b.data.toList.length) h
    simp [plantedJsonSpanClaim, spliceByteArray_toList] at hl
  refine ⟨.notTheSplice, [], ?_⟩
  show jsonSpanCheck plantedJsonSpanClaim (jsonSpanCertOf plantedJsonSpanClaim) = _
  unfold jsonSpanCheck
  rw [ite_eq_left hne]
/-- **The registered format** `vpa-json-span@1` (cSHAKE256 runs compiled). -/
@[expose] def jsonSpanFormat : Judge.Format where
  name := "vpa-json-span"
  version := "1"
  Obj := JsonSpanClaim
  Cert := JsonSpanCert
  decodeObj := decodeJsonSpanClaim
  decodeCert := decodeJsonSpanCert
  trust := .compiled
  regime := .decidable
  bad := (plantedJsonSpanClaim, jsonSpanCertOf plantedJsonSpanClaim)
  badGrade := 0
  bad_refused := plantedJsonSpan_refused
end Obend.Judge.VpaJson
end
