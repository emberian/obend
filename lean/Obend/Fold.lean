module
/-
# Obend.Fold — the audited fold: admission as a fold whose rows read pinned facts

`review/GENERALIZATION-20261031.md` §2 G1. An ADMISSION judges a list of rows by a left fold over an
accumulator `W × Rest`: the world component `W` (what rows read facts from) and the rest. Each row is
judged by `step` against the accumulator alone, refusing by a named clause; `reads acc row` are the
facts a row reads, `look w f` what the world says of one. The laws are fields:

- `keeps_world`: a row that is not a world MOVE leaves the world component;
- `step_of_reads`: on a row that is not a move, two accumulators that differ only in the world give
  the same verdict when they agree on every fact the row reads;
- `observe_ok`: a world move the admission's `allowed` relation permits is accepted as a row.

Theorems, once for every admission:

- `receipt_sufficient`: a stranger holding the accumulator's roots (its `Rest`) and the row's
  OPENINGS (each read fact with its value) recomputes the verdict at any world agreeing with them;
- `step_of_pins`: when what a world says of a fact is a function of a pin (a `World`'s
  `holds_congr`), equal pins on the row's reads suffice;
- `Family.step` composes a family of admissions over interleaved rows sharing the world component,
  and `project` recovers each member's own fold from the joint one, the other members' rows seen as
  world moves (`observe`), provided each member's moves are moves the others allow (`Guarantee`: the
  rely–guarantee condition, stated per row).

Instances: `Legal` (`Obend.Run.Fold.legalAdmission`, `legal_iff_fold`); the shared-World composition
of runners (`Obend.Run.Shared`).
-/
@[expose] public section

namespace Obend.Fold

/-- An audited fold over rows `Row`, with world component `W`, the rest of the accumulator `Rest`,
facts `Fact` a row reads, and refusals `Clause`. -/
structure Admission (W Rest Row Fact Clause : Type) where
  step : W × Rest → Row → Except Clause (W × Rest)
  reads : W × Rest → Row → List Fact
  look : W → Fact → Bool
  /-- the rows that move the world (they read the step relation, not facts) -/
  moves : Row → Bool
  /-- the row that moves the world to `w` -/
  observe : W → Row
  /-- the world moves this admission accepts -/
  allowed : W → W → Bool
  keeps_world : ∀ a r b, moves r = false → step a r = .ok b → b.1 = a.1
  step_of_reads : ∀ (a : W × Rest) (w' : W) (r : Row), moves r = false →
    (∀ f ∈ reads a r, look a.1 f = look w' f) → step (w', a.2) r = (step a r).map fun b => (w', b.2)
  observe_ok : ∀ (w w' : W) (l : Rest), allowed w w' = true → step (w, l) (observe w') = .ok (w', l)

variable {W Rest Row Fact Clause : Type}

/-- The fold. -/
def Admission.run (A : Admission W Rest Row Fact Clause) (a : W × Rest) (rows : List Row) :
    Except Clause (W × Rest) :=
  rows.foldlM A.step a

/-- What a row opens: each fact it reads, with what the world says of it. -/
def Admission.openings (A : Admission W Rest Row Fact Clause) (a : W × Rest) (r : Row) : List (Fact × Bool) :=
  (A.reads a r).map fun f => (f, A.look a.1 f)

/-- **A receipt suffices**: the accumulator's roots and the row's openings decide the verdict. At
any world that agrees with the openings, the row is judged as it was, and an accepted row reaches
the same rest. -/
theorem receipt_sufficient (A : Admission W Rest Row Fact Clause) (a : W × Rest) (r : Row)
    (hm : A.moves r = false) (w' : W) (hw : ∀ p ∈ A.openings a r, A.look w' p.1 = p.2) :
    A.step (w', a.2) r = (A.step a r).map fun b => (w', b.2) :=
  A.step_of_reads a w' r hm fun f hf => by
    have := hw (f, A.look a.1 f) (List.mem_map.2 ⟨f, hf, rfl⟩)
    exact this.symm

/-- **Pins suffice**: when what a world says of a fact is a function of the pin of the fact's cell,
equal pins on the row's reads give the same verdict. -/
theorem step_of_pins {Cell Pin : Type} (A : Admission W Rest Row Fact Clause) (cell : Fact → Cell)
    (pin : W → Cell → Pin) (hlook : ∀ w w' f, pin w (cell f) = pin w' (cell f) → A.look w f = A.look w' f)
    (a : W × Rest) (r : Row) (hm : A.moves r = false) (w' : W)
    (hp : ∀ f ∈ A.reads a r, pin a.1 (cell f) = pin w' (cell f)) :
    A.step (w', a.2) r = (A.step a r).map fun b => (w', b.2) :=
  A.step_of_reads a w' r hm fun f hf => hlook _ _ f (hp f hf)

/-! ## Composition over a shared world component, and projection -/

section
variable {ι : Type} [DecidableEq ι] {L : ι → Type} {R : ι → Type} {C : ι → Type}

/-- Replace member `i`'s component. -/
def dupd (ls : (i : ι) → L i) (i : ι) (l : L i) : (j : ι) → L j :=
  fun j => if h : j = i then h ▸ l else ls j

theorem dupd_same (ls : (i : ι) → L i) (i : ι) (l : L i) : dupd ls i l i = l := by
  simp [dupd]

theorem dupd_ne (ls : (i : ι) → L i) {i j : ι} (l : L i) (h : j ≠ i) : dupd ls i l j = ls j := by
  simp [dupd, h]

/-- The joint step of a family sharing the world component: a row of member `i` is judged by `i`
against the shared world and `i`'s own rest. -/
def Family.step (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (a : W × ((i : ι) → L i)) :
    (Σ i, R i) → Except (Σ i, C i) (W × ((i : ι) → L i))
  | ⟨i, r⟩ =>
    match (A i).step (a.1, a.2 i) r with
    | .ok b => .ok (b.1, dupd a.2 i b.2)
    | .error c => .error ⟨i, c⟩

theorem Family.step_ok (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (a : W × ((i : ι) → L i))
    {i : ι} {r : R i} {b : W × L i} (h : (A i).step (a.1, a.2 i) r = .ok b) :
    Family.step A a ⟨i, r⟩ = .ok (b.1, dupd a.2 i b.2) := by
  simp only [Family.step, h]

/-- The rows member `i` sees of a joint run: its own rows, and every other member's accepted row as
the world move it made. -/
def project (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (i : ι) :
    W × ((i : ι) → L i) → List (Σ i, R i) → List (R i)
  | _, [] => []
  | a, ⟨j, r⟩ :: rs =>
    match Family.step A a ⟨j, r⟩ with
    | .ok b =>
      (if h : j = i then [h ▸ r] else [(A i).observe b.1]) ++ project A i b rs
    | .error _ => []

/-- Every member's accepted row is a world move every other member allows. -/
def Guarantee (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) : Prop :=
  ∀ i j, i ≠ j → ∀ (a : W × L j) (r : R j) (b : W × L j), (A j).step a r = .ok b → (A i).allowed a.1 b.1 = true

/-- **Projection**: when the joint fold succeeds, every member's own fold over the rows it sees
succeeds, ending at the shared world and its own component. -/
theorem project_run (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (hg : Guarantee A) (i : ι) :
    ∀ (rows : List (Σ i, R i)) (a b : W × ((i : ι) → L i)),
      rows.foldlM (Family.step A) a = .ok b →
      ((project A i a rows).foldlM (A i).step (a.1, a.2 i)) = .ok (b.1, b.2 i)
  | [], a, b, h => by
    simp only [List.foldlM_nil] at h; cases h; rfl
  | ⟨j, r⟩ :: rs, a, b, h => by
    simp only [List.foldlM_cons] at h
    cases hs : Family.step A a ⟨j, r⟩ with
    | error c => rw [hs] at h; cases h
    | ok a' =>
      rw [hs] at h
      have ih := project_run A hg i rs a' b h
      simp only [project, hs, List.foldlM_append]
      simp only [Family.step] at hs
      cases hj : (A j).step (a.1, a.2 j) r with
      | error c => rw [hj] at hs; cases hs
      | ok c' =>
        rw [hj] at hs
        cases hs
        by_cases e : j = i
        · subst e
          simp only [↓reduceDIte, List.foldlM_cons, List.foldlM_nil, hj]
          simp only [dupd_same] at ih
          simpa [bind, Except.bind, pure, Except.pure] using ih
        · simp only [e, ↓reduceDIte, List.foldlM_cons, List.foldlM_nil]
          have hobs : (A i).step (a.1, a.2 i) ((A i).observe c'.1) = .ok (c'.1, a.2 i) :=
            (A i).observe_ok _ _ _ (hg i j (Ne.symm e) _ r c' hj)
          rw [hobs]
          have : dupd a.2 j c'.2 i = a.2 i := dupd_ne a.2 c'.2 (Ne.symm e)
          simp only at ih
          rw [this] at ih
          simpa [bind, Except.bind, pure, Except.pure] using ih


/-! ## Projection of the moves only

`project` hands a member every other member's accepted row as a world move, including rows that
leave the world as it was. `projectMoves` hands it only the rows that MOVE (`moves`): a foreign row
that keeps the world is invisible to the member, as an operation another party performs on its own
state should be. The rely–guarantee condition weakens with it (`GuaranteeMoves`: only moving rows
must be allowed by the others), and `project_moves_run` is `project_run` for it. -/

/-- The rows member `i` sees of a joint run: its own rows, and every other member's accepted MOVE. -/
def projectMoves (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (i : ι) :
    W × ((i : ι) → L i) → List (Σ i, R i) → List (R i)
  | _, [] => []
  | a, ⟨j, r⟩ :: rs =>
    match Family.step A a ⟨j, r⟩ with
    | .ok b =>
      (if h : j = i then [h ▸ r] else if (A j).moves r then [(A i).observe b.1] else []) ++
        projectMoves A i b rs
    | .error _ => []

/-- Every member's accepted MOVE is a world move every other member allows. -/
def GuaranteeMoves (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) : Prop :=
  ∀ i j, i ≠ j → ∀ (a : W × L j) (r : R j) (b : W × L j), (A j).moves r = true →
    (A j).step a r = .ok b → (A i).allowed a.1 b.1 = true

theorem Guarantee.moves {A : (i : ι) → Admission W (L i) (R i) Fact (C i)} (hg : Guarantee A) :
    GuaranteeMoves A := fun i j h a r b _ hs => hg i j h a r b hs

/-- **Projection of the moves**: when the joint fold succeeds, every member's own fold over its
rows and the others' moves succeeds, ending at the shared world and its own component. -/
theorem project_moves_run (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (hg : GuaranteeMoves A) (i : ι) :
    ∀ (rows : List (Σ i, R i)) (a b : W × ((i : ι) → L i)),
      rows.foldlM (Family.step A) a = .ok b →
      ((projectMoves A i a rows).foldlM (A i).step (a.1, a.2 i)) = .ok (b.1, b.2 i)
  | [], a, b, h => by
    simp only [List.foldlM_nil] at h; cases h; rfl
  | ⟨j, r⟩ :: rs, a, b, h => by
    simp only [List.foldlM_cons] at h
    cases hs : Family.step A a ⟨j, r⟩ with
    | error c => rw [hs] at h; cases h
    | ok a' =>
      rw [hs] at h
      have ih := project_moves_run A hg i rs a' b h
      simp only [projectMoves, hs, List.foldlM_append]
      simp only [Family.step] at hs
      cases hj : (A j).step (a.1, a.2 j) r with
      | error c => rw [hj] at hs; cases hs
      | ok c' =>
        rw [hj] at hs
        cases hs
        by_cases e : j = i
        · subst e
          simp only [↓reduceDIte, List.foldlM_cons, List.foldlM_nil, hj]
          simp only [dupd_same] at ih
          simpa [bind, Except.bind, pure, Except.pure] using ih
        · have hne : dupd a.2 j c'.2 i = a.2 i := dupd_ne a.2 c'.2 (Ne.symm e)
          simp only at ih
          rw [hne] at ih
          cases hm : (A j).moves r
          · have hw : c'.1 = a.1 := (A j).keeps_world _ r c' hm hj
            simp only [e, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, List.nil_append]
            rw [← hw]
            exact ih
          · simp only [e, ↓reduceDIte, ↓reduceIte, List.foldlM_cons, List.foldlM_nil]
            have hobs : (A i).step (a.1, a.2 i) ((A i).observe c'.1) = .ok (c'.1, a.2 i) :=
              (A i).observe_ok _ _ _ (hg i j (Ne.symm e) _ r c' hm hj)
            rw [hobs]
            simpa [bind, Except.bind, pure, Except.pure] using ih

/-- The projection of a fold's rows splits at an accepted prefix. -/
theorem projectMoves_append (A : (i : ι) → Admission W (L i) (R i) Fact (C i)) (i : ι) :
    ∀ (rows more : List (Σ i, R i)) (a b : W × ((i : ι) → L i)),
      rows.foldlM (Family.step A) a = .ok b →
      projectMoves A i a (rows ++ more) = projectMoves A i a rows ++ projectMoves A i b more
  | [], more, a, b, h => by simp only [List.foldlM_nil] at h; cases h; rfl
  | ⟨j, r⟩ :: rs, more, a, b, h => by
    simp only [List.foldlM_cons] at h
    cases hs : Family.step A a ⟨j, r⟩ with
    | error c => rw [hs] at h; cases h
    | ok a' =>
      rw [hs] at h
      simp only [List.cons_append, projectMoves, hs, List.append_assoc,
        projectMoves_append A i rs more a' b h]

end

end Obend.Fold

end
