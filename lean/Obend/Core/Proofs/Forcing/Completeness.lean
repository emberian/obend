module
/- Backward simulation, converse forcing completeness, interaction-tree chain adequacy,
   and failure reflection (`Wave C2-Core`).
   Consolidates `Demand`, `Extract`, `Back`, `Converse`, `Interaction` chain bridges, and `BackFail`. -/
public import Obend.Core.Proofs.Forcing.ForwardSim
public import Obend.Core.Proofs.Force
public import Obend.Core.Interaction
public import Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.Forcing.ForwardSim
import all Obend.Core.Proofs.Force
import all Obend.Core.Interaction

namespace Obend.Core.Proofs.Forcing
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Collect
open Obend.Core.Data
open Obend.Core.Invariant
set_option autoImplicit false

/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Demand.lean` -/

/-- A stripped nested run, seen from the base heap `B`: the cells of `B` other than `w`
keep their state in `P`, and every update frame is for `w` or for a cell past `B`. -/
public def StripInv (B P : Array Cell) (w : Nat) (s : State) : Prop :=
  (∀ a, a < B.size → a ≠ w → s.heap[a]? = P[a]?) ∧
    (∀ fr ∈ s.stack, ∀ b, fr = .update b → b = w ∨ B.size ≤ b) ∧ B.size ≤ s.heap.size

/-- The transition enters no suspended cell of `B` but `w`. -/
public def NoPreEntry (B : Array Cell) (w : Nat) (s : State) : Prop :=
  ∀ b o, s.control = .enter b → s.heap[b]? = some (.suspended o) → b < B.size → b = w

theorem stripInv_step {B P : Array Cell} {w : Nat} {s : State} (inv : StripInv B P w s)
    (noPre : NoPreEntry B w s) : StripInv B P w (stepRaw s) := by
  obtain ⟨heapI, stackI, sizeI⟩ := inv
  refine ⟨?_, ?_, Nat.le_trans sizeI (stepRaw_size_mono s)⟩
  · intro a lt ne
    by_cases reads : readsAt s = some a
    · cases ctl : s.control with
      | enter b =>
        have bEq : b = a := by simp [readsAt, ctl] at reads; exact reads
        subst bEq
        rcases stepRaw_enter_cases ctl with ⟨o, su⟩ | ⟨same, _⟩
        · exact absurd (noPre b o ctl su lt) ne
        · rw [same]; exact heapI b lt ne
      | returned v =>
        obtain ⟨rest, top⟩ : ∃ rest, s.stack = .update a :: rest := by
          cases st : s.stack with
          | nil => simp [readsAt, ctl, st] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, ctl, st] at reads
            exact ⟨rest, by rw [reads]⟩
        rcases stackI _ (by rw [top]; exact List.mem_cons_self ..) a rfl with h | h
        · exact absurd h ne
        · omega
      | _ => simp [readsAt, ctl] at reads
    · rw [stepRaw_heap_keep s (by omega) reads]; exact heapI a lt ne
  · intro fr mem b isB
    subst isB
    rcases stepRaw_stack_shape s with same | ⟨fr', push⟩ | ⟨fr0, rest, eq, notUpd, fr', next⟩ | ⟨fr0, rest, eq, next⟩ |
        ⟨fr0, rest, frs, eq, notUpd, frsNo, next, _⟩
    · rw [same] at mem; exact stackI _ mem b rfl
    · rw [push] at mem
      rcases List.mem_cons.mp mem with rfl | mem
      · have ctl := stepRaw_push_update s push rfl
        rcases stepRaw_enter_cases ctl with ⟨o, su⟩ | ⟨_, same⟩
        · by_cases lt : b < B.size
          · exact Or.inl (noPre b o ctl su lt)
          · exact Or.inr (Nat.le_of_not_lt lt)
        · rw [same] at push; have := congrArg List.length push; simp at this
      · exact stackI _ mem b rfl
    · rw [next] at mem
      rcases List.mem_cons.mp mem with rfl | mem
      · have := stepRaw_top_update s eq (by rw [next])
        exact stackI _ (by rw [eq]; exact List.mem_cons_self ..) b this
      · exact stackI _ (by rw [eq]; exact List.mem_cons_of_mem _ mem) b rfl
    · rw [next] at mem; exact stackI _ (by rw [eq]; exact List.mem_cons_of_mem _ mem) b rfl
    · rw [next] at mem
      rcases List.mem_append.mp mem with m | m
      · exact absurd rfl (frsNo _ m b)
      · exact stackI _ (by rw [eq]; exact List.mem_cons_of_mem _ m) b rfl

theorem stripInv_run {B P : Array Cell} {w : Nat} {s : State} (inv : StripInv B P w s) :
    ∀ j, (∀ i, i < j → NoPreEntry B w (exec i s)) → StripInv B P w (exec j s) := by
  intro j
  induction j with
  | zero => intro _; exact inv
  | succ j ih =>
    intro noPre
    rw [exec_succ]
    exact stripInv_step (ih (fun i lt => noPre i (by omega))) (noPre j (by omega))

/-- The map from a heap `P` that extends `B` back to `B`: the identity on `B`, the shift past
`P`'s end; the cells of `P` past `B` (allocated before the nested demand) are left out. -/
public def backMap (B P : Nat) : Nat → Nat := fun a => if a < B then a else a - P + B

/-- **Inside every finished nested evaluation sits a pre-shallow demand.** Following the
first suspended cell of the base heap `B` each nested evaluation enters, one reaches an
evaluation that enters none (besides its own cell): the closed demand of that cell on `B`
finishes and reads, of `B`, only that cell and cached cells; and the run entered it. The
heap `σ` runs on is `B` with some cells (`M`) marked evaluating (the evaluations it is
nested in) and cells allocated past `B`. -/
theorem pending_within (B : Array Cell) (Bvalid : HeapValid B) :
    ∀ (k : Nat) (σ : State) (w : Nat) (o : Closure) (R : List Frame) (M : Nat → Prop),
      σ.control = .enter w → σ.stack = R → σ.heap[w]? = some (.suspended o) → w < B.size →
      B.size ≤ σ.heap.size →
      (∀ a, a < B.size → ¬ M a → σ.heap[a]? = B[a]?) →
      (∀ a, M a → a < B.size ∧ ∃ o', σ.heap[a]? = some (.evaluating o') ∧ B[a]? = some (.suspended o')) →
      1 ≤ k → (∀ j, j < k → active (exec j σ).control = true) →
      (∀ Y, (exec k σ).stack ≠ Y ++ .update w :: R) →
      ∃ w' o' n' Bw vw, B[w']? = some (.suspended o') ∧ Demand B w' n' Bw vw ∧ PreShallow B w' n' ∧
        ∃ i, i < k ∧ (exec i σ).control = .enter w' ∧ (exec i σ).heap[w']? = some (.suspended o') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro σ w o R M ctl st su wB grow agreeB marks pos alive gone
  obtain ⟨p, v, pPos, pLt, inv, stP, ctlP, nextP, strip, dem⟩ := nested_demand ctl st su pos alive gone
  have notMw : ¬ M w := by
    intro h; obtain ⟨_, o', ev, _⟩ := marks w h; rw [su] at ev; cases ev
  have Bw : B[w]? = some (.suspended o) := by rw [← agreeB w wB notMw]; exact su
  let σ0 := demandStart σ.heap w
  have strip0 : StripInv B σ.heap w σ0 :=
    ⟨fun _ _ _ => rfl, fun fr m => by simp [σ0, demandStart] at m, grow⟩
  have ctlAt : ∀ j, j ≤ p + 1 → (exec j σ0).control = (exec j σ).control := by
    intro j hj; rw [strip j hj]; rfl
  have heapAt : ∀ j, j ≤ p + 1 → (exec j σ0).heap = (exec j σ).heap := by
    intro j hj; rw [strip j hj]; rfl
  -- the enters of suspended cells of B, after the first step
  let Q : Nat → Prop := fun j => 1 ≤ j → j ≤ p + 1 →
    ¬ ∃ b o', b < B.size ∧ (exec j σ0).control = .enter b ∧ (exec j σ0).heap[b]? = some (.suspended o')
  have noPreOf : ∀ i, (i = 0 ∨ Q i) → i ≤ p + 1 → NoPreEntry B w (exec i σ0) := by
    intro i h hi b o' c s' lt
    rcases h with rfl | q
    · simp [exec, σ0, demandStart] at c; exact c.symm
    · by_cases i0 : i = 0
      · subst i0; simp [exec, σ0, demandStart] at c; exact c.symm
      · exact absurd ⟨b, o', lt, c, s'⟩ (q (by omega) hi)
  by_cases allQ : ∀ j, Q j
  · -- the nested evaluation enters no other suspended cell of B: it is pre-shallow
    have noPre : ∀ i, i ≤ p + 1 → NoPreEntry B w (exec i σ0) := fun i hi =>
      noPreOf i (Or.inr (allQ i)) hi
    have stripAt : ∀ j, j ≤ p + 2 → StripInv B σ.heap w (exec j σ0) := fun j hj =>
      stripInv_run strip0 j (fun i lt => noPre i (by omega))
    have halts := dem.halts
    -- what the stripped run reads of B
    have readsB : ∀ j, j < p + 2 → ∀ a, readsAt (exec j σ0) = some a → a < B.size →
        Footprint B w a ∧ ¬ M a := by
      intro j hj a reads lt
      have si := stripAt j (by omega)
      cases c : (exec j σ0).control with
      | enter b =>
        have bEq : b = a := by simp [readsAt, c] at reads; exact reads
        subst bEq
        by_cases isW : b = w
        · subst isW; exact ⟨Or.inl rfl, notMw⟩
        · have keep := si.1 b lt isW
          have stuck : ∀ o', (exec j σ0).heap[b]? ≠ some (.evaluating o') := by
            intro o' ev
            have blk := stepRaw_enter_evaluating c ev
            by_cases last : j + 1 < p + 2
            · have := halts.1 (j + 1) last; rw [exec_succ, blk] at this; cases this
            · have jEq : j = p + 1 := by omega
              subst jEq
              have := ctlAt (p + 1) (Nat.le_refl _)
              rw [c, nextP] at this; cases this
          have notSusp : ∀ o', (exec j σ0).heap[b]? ≠ some (.suspended o') := by
            intro o' sus; exact isW (noPre j (by omega) b o' c sus lt)
          by_cases m : M b
          · obtain ⟨_, o', ev, _⟩ := marks b m
            exact absurd (keep.trans ev) (stuck o')
          · refine ⟨?_, m⟩
            rw [keep, agreeB b lt m] at stuck notSusp
            cases hb : B[b]? with
            | none => simp [Array.getElem?_eq_none_iff] at hb; omega
            | some cell => cases cell with
              | suspended o' => exact absurd hb (notSusp o')
              | evaluating o' => exact absurd hb (stuck o')
              | cached o' v' => exact Or.inr ⟨o', v', hb⟩
      | returned rv =>
        obtain ⟨rest, top⟩ : ∃ rest, (exec j σ0).stack = .update a :: rest := by
          cases stk : (exec j σ0).stack with
          | nil => simp [readsAt, c, stk] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, c, stk] at reads
            exact ⟨rest, by rw [reads]⟩
        rcases si.2.1 _ (by rw [top]; exact List.mem_cons_self ..) a rfl with h | h
        · subst h; exact ⟨Or.inl rfl, notMw⟩
        · omega
      | _ => simp [readsAt, c] at reads
    -- the stripped run on σ's heap, mirrored by the demand on B
    let h := backMap B.size σ.heap.size
    let D : Nat → Prop := fun a => a < B.size ∨ σ.heap.size ≤ a
    have start : StateAgree h D M σ0 (demandStart B w) := by
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, fun fr m => by simp [σ0, demandStart] at m, rfl⟩
      · intro a past
        have past' : σ.heap.size ≤ a := past
        refine ⟨Or.inr past', fun mm => by have := (marks a mm).1; omega, ?_⟩
        simp only [h, backMap, show ¬ a < B.size by omega, if_false]
        show a - σ.heap.size + B.size + σ.heap.size = a + B.size; omega
      · intro a b da db eq
        simp only [h, backMap] at eq
        by_cases ha : a < B.size <;> by_cases hb : b < B.size <;> simp only [ha, hb, if_true, if_false] at eq
        · exact eq
        · rcases db with db | db <;> omega
        · rcases da with da | da <;> omega
        · rcases da with da | da <;> rcases db with db | db <;> omega
      · intro a da notM bound
        have aB : a < B.size := by rcases da with da | da; exact da; exact absurd bound (by simp [σ0, demandStart]; omega)
        obtain ⟨c, found⟩ : ∃ c, B[a]? = some c := ⟨B[a], by simp [aB]⟩
        refine ⟨c, by rw [show (σ0.heap) = σ.heap from rfl, agreeB a aB notM]; exact found, ?_, ?_⟩
        · show B[h a]? = some (renameCell h c)
          rw [show h a = a by simp [h, backMap, aB], renameCell_id (fun x m => by
            have := Bvalid _ _ found x m; simp [h, backMap, this])]
          exact found
        · exact fun x m => Or.inl (Bvalid _ _ found x m)
      · show AllIn D [w]; exact fun x m => by simp at m; subst m; exact Or.inl wB
      · show Control.enter w = Control.enter (h w); simp [h, backMap, wB]
    have avoids : ∀ j, j < p + 2 → Avoids M (exec j σ0) := by
      intro j hj a reads mm
      exact (readsB j hj a reads (marks a mm).1).2 mm
    have agreeAt : ∀ j, j ≤ p + 2 → StateAgree h D M (exec j σ0) (exec j (demandStart B w)) :=
      fun j hj => agree_exec start j (fun i lt => avoids i (by omega))
    have fin := agreeAt (p + 2) (Nat.le_refl _)
    rw [dem.final] at fin
    have demB : Demand B w (p + 2) (exec (p + 2) (demandStart B w)).heap (renameValue h v) := by
      refine ⟨⟨fun j lt => ?_, ?_⟩, ?_⟩
      · rw [(agreeAt j (by omega)).active_eq]; exact halts.1 j lt
      · rw [(agreeAt (p + 2) (Nat.le_refl _)).active_eq]; exact halts.2
      · have c := fin.control; have s := fin.stack
        simp only [renameControl, List.map_nil] at c s
        rw [state_ext (s := exec (p + 2) (demandStart B w)), c, s]
    refine ⟨w, o, p + 2, _, _, Bw, demB, ?_, 0, pos, ctl, su⟩
    intro j hj a reads lt
    have rel := agreeAt j (by omega)
    rw [rel.readsAt_eq] at reads
    cases r : readsAt (exec j σ0) with
    | none => rw [r] at reads; cases reads
    | some a' =>
      rw [r] at reads; simp only [Option.map_some, Option.some.injEq] at reads
      have da := rel.readsIn r
      have a'B : a' < B.size := by
        rcases da with da | da
        · exact da
        · simp only [h, backMap, show ¬ a' < B.size by omega, if_false] at reads; omega
      have ha : h a' = a' := by simp [h, backMap, a'B]
      rw [ha] at reads; subst reads
      exact (readsB j (by omega) a' r a'B).1
  · -- the first other suspended cell of B the nested evaluation enters
    obtain ⟨j1, notQ, minQ⟩ := exists_first_fail (P := Q) (by
      apply Classical.byContradiction; intro hc; apply allQ; intro j
      apply Classical.byContradiction; intro hq; exact hc ⟨j, hq⟩)
    have j1Pos : 1 ≤ j1 := by
      apply Classical.byContradiction; intro h0; apply notQ; intro h1; omega
    have j1Le : j1 ≤ p + 1 := by
      apply Classical.byContradiction; intro h0; apply notQ; intro _ h1; omega
    obtain ⟨b, o1, bB, ctlB, suB⟩ : ∃ b o', b < B.size ∧ (exec j1 σ0).control = .enter b ∧
        (exec j1 σ0).heap[b]? = some (.suspended o') := by
      apply Classical.byContradiction; intro hc; exact notQ (fun _ _ => hc)
    have j1LeP : j1 ≤ p := by
      apply Classical.byContradiction; intro h0
      have jEq : j1 = p + 1 := by omega
      subst jEq
      have := ctlAt (p + 1) (Nat.le_refl _); rw [ctlB, nextP] at this; cases this
    have stripJ := stripInv_run strip0 j1 (fun i lt => noPreOf i
      (by by_cases i0 : i = 0; exact Or.inl i0; exact Or.inr (minQ i lt)) (by omega))
    let σ' := exec j1 σ
    have eqσ' : σ' = withStack (exec j1 σ0) R := strip j1 (by omega)
    obtain ⟨⟨Y1, hY1, _⟩, wEval⟩ := inv j1 j1Pos j1LeP
    let M' : Nat → Prop := fun x => M x ∨ x = w
    have r := ih (k - j1) (by omega) σ' b o1 σ'.stack M'
      (by rw [eqσ']; exact ctlB) rfl (by rw [eqσ']; exact suB) bB
      (Nat.le_trans grow (exec_size_mono σ j1))
      (by
        intro a aB notM'
        have ne : a ≠ w := fun e => notM' (Or.inr e)
        have notM : ¬ M a := fun m => notM' (Or.inl m)
        rw [eqσ']; show (exec j1 σ0).heap[a]? = _
        rw [stripJ.1 a aB ne]; exact agreeB a aB notM)
      (by
        intro a m'
        rcases m' with m | rfl
        · obtain ⟨aB, o', ev, bs⟩ := marks a m
          have ne : a ≠ w := fun e => notMw (e ▸ m)
          refine ⟨aB, o', ?_, bs⟩
          rw [eqσ']; show (exec j1 σ0).heap[a]? = _
          rw [stripJ.1 a aB ne]; exact ev
        · exact ⟨wB, o, wEval, Bw⟩)
      (by omega)
      (by intro j lt; show active (exec j (exec j1 σ)).control = true; rw [← exec_add]; exact alive _ (by omega))
      (by
        intro Y eqY
        apply gone (Y ++ .update b :: Y1)
        have : exec (k - j1) σ' = exec k σ := by
          show exec (k - j1) (exec j1 σ) = _; rw [← exec_add, show j1 + (k - j1) = k by omega]
        rw [← this, eqY]
        show Y ++ .update b :: σ'.stack = _
        rw [show σ'.stack = Y1 ++ .update w :: R from hY1]; simp)
    obtain ⟨w', o', n', Bw', vw, bsus, d, ps, i', i'lt, ci, si⟩ := r
    refine ⟨w', o', n', Bw', vw, bsus, d, ps, j1 + i', by omega, ?_, ?_⟩
    · rw [exec_add]; exact ci
    · rw [exec_add]; exact si

public theorem renameControl_id {f : Nat → Nat} {c : Control} (same : ∀ x ∈ controlAddresses c, f x = x) :
    renameControl f c = c := by
  rw [renameControl_congr (g := id) same]
  cases c <;> simp [renameControl, renameValue_id (f := id) (fun _ _ => rfl)]

theorem renameFrame_id {f : Nat → Nat} {fr : Frame} (same : ∀ x ∈ frameAddresses fr, f x = x) :
    renameFrame f fr = fr := by
  rw [renameFrame_congr (g := id) same]
  cases fr <;> simp [renameFrame, renameValue_id (f := id) (fun _ _ => rfl)]

public theorem renameStack_id {f : Nat → Nat} {S : List Frame} (same : ∀ fr ∈ S, ∀ x ∈ frameAddresses fr, f x = x) :
    S.map (renameFrame f) = S := by
  conv => rhs; rw [← List.map_id S]
  exact List.map_congr_left (fun fr m => renameFrame_id (same fr m))

/-- A pre-shallow closed demand leaves every other cell of its base unchanged. -/
theorem preShallow_keeps {e : Pending} (valid : e.Valid) {a : Nat} (lt : a < e.base.size) (ne : a ≠ e.cell) :
    e.final[a]? = e.base[a]? := by
  have := exec_preservesCached (demandStart e.base e.cell) e.steps
  rw [valid.demand.final] at this
  cases h : e.base[a]? with
  | none => simp [Array.getElem?_eq_none_iff] at h; omega
  | some c =>
    by_cases ca : ∃ o w, c = .cached o w
    · obtain ⟨o, w, rfl⟩ := ca; exact this a o w h
    · have keep := exec_heap_keep (demandStart e.base e.cell) (a := a) lt e.steps (fun j lt' reads => by
        rcases valid.shallow j lt' a reads ‹_› with eq | ⟨o, w, cw⟩
        · exact ne eq
        · rw [h] at cw; cases cw; exact ca ⟨o, w, rfl⟩)
      rw [valid.demand.final] at keep; rw [keep]; exact h

/-- **The pending link**: on any valid control and stack of the base, the base forces to the
pending demand's final heap through that demand. -/
theorem pendRel_start {e : Pending} (valid : e.Valid) {c : Control} {S : List Frame}
    (cIn : AllIn (· < e.base.size) (controlAddresses c))
    (sIn : ∀ fr ∈ S, AllIn (· < e.base.size) (frameAddresses fr)) :
    PendRel e (liftMap e.base.size e.final.size) ⟨e.base, c, S⟩ ⟨e.final, c, S⟩ := by
  have ge := Pending.final_ge valid
  have cellLt := Pending.cell_lt valid
  let f0 := liftMap e.base.size e.final.size
  have f0Old : ∀ a, a < e.base.size → f0 a = a := fun a lt => by simp [f0, liftMap, lt]
  refine ⟨⟨valid, Nat.le_refl _, valid.susp, fun _ _ _ h => h, f0Old, ?_, ⟨?_, ?_, ?_⟩,
    fun _ _ _ => rfl, rfl⟩, ?_, ?_, ⟨valid.baseValid, cIn, sIn⟩⟩
  · intro a le; simp only [f0, liftMap, show ¬ a < e.base.size by omega, if_false]; rfl
  · intro a past
    have past' : e.base.size ≤ a := past
    refine ⟨trivial, fun h => by have := Pending.cell_lt valid; omega, ?_⟩
    simp only [f0, liftMap, show ¬ a < e.base.size by omega, if_false]
    show a + (e.final.size - e.base.size) + e.base.size = a + e.final.size; omega
  · intro a b _ _ eq
    simp only [f0, liftMap] at eq
    split at eq <;> split at eq <;> omega
  · intro a _ ne lt
    have lt' : a < e.base.size := lt
    obtain ⟨c0, found⟩ : ∃ c0, e.base[a]? = some c0 := ⟨e.base[a], by simp [lt']⟩
    refine ⟨c0, found, ?_, allIn_everywhere _⟩
    show e.final[f0 a]? = _
    rw [f0Old a lt', preShallow_keeps valid lt' ne, found,
      renameCell_id (fun x m => f0Old x (valid.baseValid _ _ found x m))]
  · show c = renameControl f0 c
    rw [renameControl_id (fun x m => f0Old x (cIn x m))]
  · show S = S.map (renameFrame f0)
    rw [renameStack_id (fun fr m x mx => f0Old x (sIn fr m x mx))]

public theorem demand_cell_lt {B : Array Cell} {y n : Nat} {Bf : Array Cell} {v : RuntimeValue} (d : Demand B y n Bf v) :
    y < B.size ∧ ((∃ o, B[y]? = some (.suspended o)) ∨ (∃ o w, B[y]? = some (.cached o w) ∧ Bf = B)) := by
  have pos : 1 ≤ n := by
    apply Classical.byContradiction; intro h
    have := d.halts.2; rw [show n = 0 by omega] at this; simp [exec, demandStart, active] at this
  cases h : B[y]? with
  | none =>
    exfalso
    have step : stepRaw (demandStart B y) = ⟨B, .refused .missingCell, []⟩ := by simp [stepRaw, demandStart, h]
    by_cases n1 : n = 1
    · subst n1; have := d.final; rw [exec_one, step] at this; cases this
    · have := d.halts.1 1 (by omega); rw [exec_one, step] at this; cases this
  | some c =>
    have lt : y < B.size := bound_of_some h
    cases c with
    | suspended o => exact ⟨lt, Or.inl ⟨o, rfl⟩⟩
    | evaluating o =>
      exfalso
      have step : stepRaw (demandStart B y) = ⟨B, .blackhole y, []⟩ := by simp [stepRaw, demandStart, h]
      by_cases n1 : n = 1
      · subst n1; have := d.final; rw [exec_one, step] at this; cases this
      · have := d.halts.1 1 (by omega); rw [exec_one, step] at this; cases this
    | cached o w =>
      refine ⟨lt, Or.inr ⟨o, w, rfl, ?_⟩⟩
      have s1 : stepRaw (demandStart B y) = ⟨B, .returned w, []⟩ := by simp [stepRaw, demandStart, h]
      have s2 : exec 2 (demandStart B y) = ⟨B, .complete w, []⟩ := by
        rw [show 2 = 1 + 1 from rfl, exec_succ, exec_one, s1]; rfl
      have h2 : Halts (demandStart B y) 2 := by
        refine ⟨fun j lt => ?_, by rw [s2]; rfl⟩
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · rfl
        · rw [exec_one, s1]; rfl
      have := halts_unique d.halts h2; subst this
      have := d.final; rw [s2] at this; simp at this; exact this.1.symm

/-- **A finished closed demand is a forcing chain** (the main induction). On every valid
control and stack of the demand's base heap, the base heap forces to the demand's final
heap, with headroom the cells the demand allocated, by an address map that is the identity
on the base. -/
public theorem demand_forces : ∀ (n : Nat) (B : Array Cell) (y : Nat) (Bf : Array Cell) (v : RuntimeValue),
    HeapValid B → Demand B y n Bf v →
    ∃ F : Nat → Nat, (∀ a, a < B.size → F a = a) ∧
      ∀ (c : Control) (S : List Frame), AllIn (· < B.size) (controlAddresses c) →
        (∀ fr ∈ S, AllIn (· < B.size) (frameAddresses fr)) →
        ForcesBy (Bf.size - B.size) F ⟨B, c, S⟩ ⟨Bf, c, S⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro B y Bf v Bvalid d
  obtain ⟨yB, sus | ⟨o, w, _, BfEq⟩⟩ := demand_cell_lt d
  · obtain ⟨o, su⟩ := sus
    have pos : 1 ≤ n := by
      apply Classical.byContradiction; intro h
      have := d.halts.2; rw [show n = 0 by omega] at this; simp [exec, demandStart, active] at this
    have gone : ∀ Y, (exec n (demandStart B y)).stack ≠ Y ++ [.update y] := by
      intro Y h; rw [d.final] at h; have := congrArg List.length h; simp at this
    obtain ⟨w', o', n', Bw, vw, bsus, dw, ps, i, ilt, ci, si⟩ :=
      pending_within B Bvalid n (demandStart B y) y o [] (fun _ => False) rfl rfl su yB (Nat.le_refl _)
        (fun _ _ _ => rfl) (fun _ h => h.elim) pos d.halts.1 gone
    let e : Pending := ⟨B, w', n', Bw, vw, o'⟩
    have ev : e.Valid := ⟨dw, bsus, ps, Bvalid⟩
    have BwGe : B.size ≤ Bw.size := Pending.final_ge ev
    have BwValid : HeapValid Bw := by
      have := heapValid_exec (addrValid_demandStart Bvalid (Pending.cell_lt ev)) n'
      rw [dw.final] at this; exact this
    have start : PendRel e (liftMap e.base.size e.final.size) (demandStart B y) (demandStart Bw y) :=
      pendRel_start ev (c := .enter y) (S := [])
        (by intro x m; simp [controlAddresses] at m; subst m; exact yB) (fun _ m => by cases m)
    obtain ⟨n2, le2, halts2, _, result⟩ := pend_transfer n _ _ start d.halts
    -- the lazy run entered w' suspended and finished: w' is cached at the end
    have cachedEnd : ∃ oc wc, Bf[w']? = some (.cached oc wc) := by
      obtain ⟨p, vp, _, pLt, inv, _, _, nextP⟩ := nested_pop (σ := exec i (demandStart B y)) (k := n - i)
        ci rfl si (by omega) (fun j lt => by rw [← exec_add]; exact d.halts.1 _ (by omega))
        (fun Y h => by
          rw [← exec_add, show i + (n - i) = n by omega, d.final] at h
          have := congrArg List.length h; simp at this)
      have wLt : w' < (exec p (exec i (demandStart B y))).heap.size := bound_of_some (inv p (by omega) (Nat.le_refl _)).2
      have cachedP : (exec (p + 1) (exec i (demandStart B y))).heap[w']? = some (.cached o' vp) := by
        rw [nextP]; simp [wLt]
      have := exec_preservesCached _ (n - i - (p + 1)) w' o' vp cachedP
      rw [← exec_add, ← exec_add, show i + (p + 1 + (n - i - (p + 1))) = n by omega, d.final] at this
      exact ⟨o', vp, this⟩
    rcases result with pend | ⟨g, agree, cover, ident, _, n2lt, sizeEq⟩
    · exfalso
      obtain ⟨oc, wc, ca⟩ := cachedEnd
      have := pend.heap.cellKept
      rw [d.final] at this; simp only at this; rw [ca] at this; cases this
    · -- the remaining demand of y on Bw is shorter: induction
      have ctlEnd := agree.agree.control
      have stEnd := agree.agree.stack
      rw [d.final] at ctlEnd stEnd
      simp only [renameControl, List.map_nil] at ctlEnd stEnd
      let G := (exec n2 (demandStart Bw y)).heap
      have dG : Demand Bw y n2 G (renameValue g v) := by
        refine ⟨halts2, ?_⟩
        rw [state_ext (s := exec n2 (demandStart Bw y)), ctlEnd, stEnd]
      obtain ⟨F2, F2id, chain2⟩ := ih n2 (by omega) Bw y G _ BwValid dG
      have heapAgree := agree.agree.heap
      rw [d.final] at heapAgree cover sizeEq
      simp only at heapAgree cover sizeEq
      have BfValid : HeapValid Bf := by
        have := heapValid_exec (addrValid_demandStart Bvalid yB) n; rw [d.final] at this; exact this
      have GValid : HeapValid G := heapValid_exec (addrValid_demandStart BwValid (by omega)) n2
      obtain ⟨ginv, inverse, left⟩ := agree_inverse heapAgree cover sizeEq BfValid
      have ginvId : ∀ a, a < B.size → ginv a = a := by
        intro a lt; have := left a (by have := exec_size_mono (demandStart B y) n; rw [d.final] at this; simp [demandStart] at this; omega)
        rw [ident a lt] at this; exact this
      have GsizeEq : G.size = Bf.size := sizeEq
      have GGe : Bw.size ≤ G.size := by
        have := exec_size_mono (demandStart Bw y) n2; simp [demandStart] at this; exact this
      refine ⟨ginv ∘ (F2 ∘ liftMap B.size Bw.size), fun a lt => ?_, fun c S cIn sIn => ?_⟩
      · simp only [Function.comp_apply, liftMap, lt, if_true, F2id a (by omega), ginvId a lt]
      · have l1 : ForcesBy e.gap (liftMap B.size Bw.size) ⟨B, c, S⟩ ⟨Bw, c, S⟩ :=
          .pend (pendRel_start ev cIn sIn) (Nat.le_refl _)
        have l2 := chain2 c S (fun x m => by have := cIn x m; omega)
          (fun fr m x mx => by have := sIn fr m x mx; omega)
        have l3 : ForcesBy 0 ginv ⟨G, c, S⟩ ⟨Bf, c, S⟩ := by
          refine .agree ⟨⟨inverse, allIn_everywhere _, ?_, fun _ _ => allIn_everywhere _, ?_⟩,
            ⟨GValid, fun x m => by show x < G.size; have := cIn x m; omega,
              fun fr m x mx => by show x < G.size; have := sIn fr m x mx; omega⟩⟩ (by show Bf.size ≤ G.size + 0; omega)
          · show c = renameControl ginv c
            rw [renameControl_id (fun x m => ginvId x (cIn x m))]
          · show S = S.map (renameFrame ginv)
            rw [renameStack_id (fun fr m x mx => ginvId x (sIn fr m x mx))]
        refine .trans (.trans l1 l2 (Nat.le_refl _)) l3 ?_
        show e.gap + (G.size - Bw.size) + 0 ≤ Bf.size - B.size
        unfold Pending.gap; simp only [e]; omega
  · subst BfEq
    refine ⟨id, fun _ _ => rfl, fun c S cIn sIn => ?_⟩
    exact .agree (agreeRel_refl ⟨Bvalid, cIn, sIn⟩) (by omega)


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Extract.lean` -/

/-! ## The lexical invariant names only allocated addresses -/

section Lexical
open Obend.Core.Invariant

theorem valueValid_allIn {b : Nat} {v : RuntimeValue} (h : RuntimeValueValid b v) :
    AllIn (· < b) (valueAddresses v) := by
  cases v with
  | closure body env => simp only [RuntimeValueValid] at h; exact h.2
  | natural _ => exact allIn_nil _
  | boolean _ => exact allIn_nil _
  | label _ => exact allIn_nil _
  | record fields =>
    simp only [RuntimeValueValid] at h
    intro x m
    obtain ⟨fld, mem, rfl⟩ := List.mem_map.mp m
    exact h fld mem
  | specification a c =>
    simp only [RuntimeValueValid] at h
    intro x m
    simp only [valueAddresses, List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact h.1
    · exact h.2
  | prototype a c =>
    simp only [RuntimeValueValid] at h
    intro x m
    simp only [valueAddresses, List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl
    · exact h.1
    · exact h.2
  | variant _ p =>
    simp only [RuntimeValueValid] at h
    intro x m
    simp only [valueAddresses, List.mem_singleton] at m
    subst m; exact h

theorem cellValid_allIn {b : Nat} {c : Cell} (h : CellValid b c) : AllIn (· < b) (cellAddresses c) := by
  cases c with
  | suspended o => simp only [CellValid, ClosureValid] at h; exact h.2
  | evaluating o => simp only [CellValid, ClosureValid] at h; exact h.2
  | cached o v =>
    simp only [CellValid, ClosureValid] at h
    exact allIn_append h.1.2 (valueValid_allIn h.2)

theorem frameValid_allIn {b : Nat} {fr : Frame} (h : FrameValid b fr) : AllIn (· < b) (frameAddresses fr) := by
  cases fr with
  | argument term env => simp only [FrameValid, ClosureValid] at h; exact h.2
  | binaryLeft _ term env => simp only [FrameValid, ClosureValid] at h; exact h.2
  | update a =>
    simp only [FrameValid] at h
    intro x m; simp only [frameAddresses, List.mem_singleton] at m; subst m; exact h
  | field _ => exact allIn_nil _
  | reflect => exact allIn_nil _
  | metadata => exact allIn_nil _
  | project => exact allIn_nil _
  | extend fields env => simp only [FrameValid] at h; exact h.1
  | condition z s env => simp only [FrameValid] at h; exact h.1
  | binaryRight _ v => simp only [FrameValid] at h; exact valueValid_allIn h
  | case arms env => simp only [FrameValid] at h; exact h.1
  | ifBool t f env => simp only [FrameValid] at h; exact h.1
  | split _ f env => simp only [FrameValid] at h; exact h.1

theorem controlValid_allIn {b : Nat} {c : Control} (h : ControlValid b c) :
    AllIn (· < b) (controlAddresses c) := by
  cases c with
  | evaluate term env => simp only [ControlValid, ClosureValid] at h; exact h.2
  | enter a =>
    simp only [ControlValid] at h
    intro x m; simp only [controlAddresses, List.mem_singleton] at m; subst m; exact h
  | blackhole a =>
    simp only [ControlValid] at h
    intro x m; simp only [controlAddresses, List.mem_singleton] at m; subst m; exact h
  | yielded a =>
    simp only [ControlValid] at h
    intro x m; simp only [controlAddresses, List.mem_singleton] at m; subst m; exact h
  | returned v => simp only [ControlValid] at h; exact valueValid_allIn h
  | complete v => simp only [ControlValid] at h; exact valueValid_allIn h
  | refused _ => exact allIn_nil _

/-- **The lexical invariant gives address validity.** -/
theorem addrValid_of_lexical {s : State} (lexical : LexicalInvariant s) : AddrValid s :=
  ⟨fun a c found => cellValid_allIn (lexical.1 a c found), controlValid_allIn lexical.2.1,
    fun fr m => frameValid_allIn (lexical.2.2 fr m)⟩

end Lexical

/-! ## The forced side runs whatever the lazy side runs -/

/-- **Fitting transfers along a chain**, with heap headroom of the chain's gap. -/
theorem forces_fits {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {n : Nat} (halts : Halts σ n)
    (fits : FitsFrom L σ n) :
    ∃ n' F', n' ≤ n ∧ Halts τ n' ∧ FitsFrom L' τ n' ∧ ForcesBy gap F' (exec n σ) (exec n' τ) ∧
      ∀ a, a < σ.heap.size → F' a = F a := by
  obtain ⟨n', F', le, haltsT, bounded, rel, ext⟩ := forces_transfer h n halts
  refine ⟨n', F', le, haltsT, fun j' lo hi => ?_, rel, ext⟩
  obtain ⟨j, hj, lj, sz, st⟩ := bounded j' hi
  obtain ⟨fh, fs⟩ := fits j (by omega) hj
  exact ⟨by omega, by omega⟩

/-- **Forcing transfers along a chain**: with no fewer ticks and heap headroom of the gap, the
forced side finishes too, with the renamed value, no fewer ticks left, again in a chain. -/
theorem forces_forceWith {gap : Nat} {F : Nat → Nat} {s t : State} (h : ForcesBy gap F s t) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {T T' : Nat} (le : T ≤ T')
    {v : RuntimeValue} {st : State} {r : Nat} (ran : forceWith (fun _ => true) L T s = (.finished v st, r)) :
    ∃ (F' : Nat → Nat) (st' : State) (r' : Nat),
      forceWith (fun _ => true) L' T' t = (.finished (renameValue F' v) st', r') ∧ r ≤ r' ∧
        ForcesBy gap F' st st' ∧ AllIn (· < st.heap.size) (valueAddresses v) ∧
        (∀ a, a < s.heap.size → F' a = F a) ∧ s.heap.size ≤ st.heap.size := by
  obtain ⟨n, le1, halts, fits, eq, ctl, rEq⟩ := forceWith_finished L T s v st r ran
  obtain ⟨n', F', le2, haltsT, fitsT, rel, ext⟩ := forces_fits h heapRoom stackRoom halts fits
  have ctlT : (exec n' t).control = .complete (renameValue F' v) := by
    rw [rel.renames.1, eq, ctl]; rfl
  refine ⟨F', exec n' t, T' - n', forceWith_of_halts L' T' t n' _ haltsT (by omega) fitsT ctlT, by omega,
    by rw [← eq]; exact rel, ?_, ext, by rw [← eq]; exact exec_size_mono s n⟩
  have := (ForcesBy.lazyValid rel).control
  rw [eq, ctl] at this
  exact this

/-- Two budgets differ only in ticks, the second no smaller. -/
public def TicksLe (b b' : Budget) : Prop := b'.nodes = b.nodes ∧ b'.bytes = b.bytes ∧ b.ticks ≤ b'.ticks

theorem ticksLe_with (b : Budget) {t : Nat} (le : b.ticks ≤ t) : TicksLe b {b with ticks := t} := ⟨rfl, rfl, le⟩

/-- The record fold, along a chain: each field forced on the lazy side is forced on the forced
side at its image under the map the record was renamed by (later maps extend it). -/
theorem foldlM_forces {gap : Nat} {base : Nat} {F0 : Nat → Nat}
    {L L' : Limits} {step : Limits → List (String × Data) × State × Budget → String × Nat →
      Except (Failure × State × Budget) (List (String × Data) × State × Budget)}
    (stepRel : ∀ (acc : List (String × Data)) (st st' : State) (b b' : Budget) (field : String × Nat)
        (out : List (String × Data) × State × Budget) (F : Nat → Nat),
      ForcesBy gap F st st' → field.2 < st.heap.size → TicksLe b b' → step L (acc, st, b) field = .ok out →
      ∃ (out' : List (String × Data) × State × Budget) (F' : Nat → Nat),
        step L' (acc, st', b') (field.1, F field.2) = .ok out' ∧ out'.1 = out.1 ∧ TicksLe out.2.2 out'.2.2 ∧
        ForcesBy gap F' out.2.1 out'.2.1 ∧ (∀ a, a < st.heap.size → F' a = F a) ∧
        st.heap.size ≤ out.2.1.heap.size) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (st st' : State) (b b' : Budget)
      (F : Nat → Nat) (out : List (String × Data) × State × Budget),
      ForcesBy gap F st st' → base ≤ st.heap.size → (∀ a, a < base → F a = F0 a) →
      AllIn (· < base) (fields.map Prod.snd) → TicksLe b b' → fields.foldlM (step L) (acc, st, b) = .ok out →
      ∃ (out' : List (String × Data) × State × Budget) (F' : Nat → Nat),
        (fields.map fun field => (field.1, F0 field.2)).foldlM (step L') (acc, st', b') = .ok out' ∧
        out'.1 = out.1 ∧ TicksLe out.2.2 out'.2.2 ∧ ForcesBy gap F' out.2.1 out'.2.1 ∧
        (∀ a, a < st.heap.size → F' a = F a) ∧ st.heap.size ≤ out.2.1.heap.size := by
  intro fields
  induction fields with
  | nil =>
    intro acc st st' b b' F out rel _ _ _ le folded
    simp [List.foldlM] at folded
    subst folded
    exact ⟨_, F, rfl, rfl, le, rel, fun _ _ => rfl, Nat.le_refl _⟩
  | cons field rest ih =>
    intro acc st st' b b' F out rel baseLe agree inside le folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    have fieldIn : field.2 < base := inside field.2 (by simp)
    obtain ⟨mid', F1, first', same1, le1, rel1, ext1, grow1⟩ :=
      stepRel acc st st' b b' field mid F rel (by omega) le first
    rw [agree _ fieldIn] at first'
    obtain ⟨out', F2, folded', outSame, outLe, outRel, ext2, grow2⟩ :=
      ih mid.1 mid.2.1 mid'.2.1 mid.2.2 mid'.2.2 F1 out rel1 (by omega)
        (fun a lt => by rw [ext1 a (by omega), agree a lt])
        (fun x member => inside x (by simp [member])) le1 restFolded
    refine ⟨out', F2, ?_, outSame, outLe, outRel, fun a lt => by rw [ext2 a (by omega), ext1 a lt], by omega⟩
    simp only [List.map_cons, List.foldlM_cons, except_bind_ok]
    refine ⟨mid', first', ?_⟩
    have shape : mid' = (mid.1, mid'.2.1, mid'.2.2) := by
      obtain ⟨a, b, c⟩ := mid'
      simp only at same1
      rw [same1]
    rw [shape]; exact folded'

/-- **Materialization transfers along a chain**: the renamed value materializes on the forced
side to the same Data, with the same nodes and bytes left and no fewer ticks. -/
theorem forces_materializeWith {L L' : Limits} {gap : Nat} (heapRoom : L.heap + gap ≤ L'.heap)
    (stackRoom : L.stack ≤ L'.stack) :
    ∀ (depth : Nat) (budget budget' : Budget) (value : RuntimeValue) (s t : State) (F : Nat → Nat) (r : Result),
      ForcesBy gap F s t → AllIn (· < s.heap.size) (valueAddresses value) → TicksLe budget budget' →
      materializeWith (fun _ => true) L depth budget value s = .ok r →
      ∃ (r' : Result) (F' : Nat → Nat),
        materializeWith (fun _ => true) L' depth budget' (renameValue F value) t = .ok r' ∧
        r'.value = r.value ∧ TicksLe r.remaining r'.remaining ∧ ForcesBy gap F' r.state r'.state ∧
        s.heap.size ≤ r.state.heap.size ∧ ∀ a, a < s.heap.size → F' a = F a := by
  intro depth
  induction depth with
  | zero => intro budget budget' value s t F r _ _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget budget' value s t F r rel valueIn le found
    obtain ⟨nodes, ticks, bytes⟩ := budget
    obtain ⟨nodes', ticks', bytes'⟩ := budget'
    obtain ⟨hn, hb, ht⟩ := le
    simp only at hn hb ht
    subst nodes' bytes'
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨⟨.natural n, t, ⟨nodes - 1, ticks', bytes - ((toString n).utf8ByteSize + 2)⟩⟩, F, ?_, ?_, ?_, ?_, ?_⟩
          · simp [materializeWith, renameValue, c1, c2]
          · rw [← found]
          · rw [← found]; exact ⟨rfl, rfl, ht⟩
          · rw [← found]; exact rel
          · rw [← found]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨⟨.boolean b, t, ⟨nodes - 1, ticks', bytes - 2⟩⟩, F, ?_, ?_, ?_, ?_, ?_⟩
          · simp [materializeWith, renameValue, c1, c2]
          · rw [← found]
          · rw [← found]; exact ⟨rfl, rfl, ht⟩
          · rw [← found]; exact rel
          · rw [← found]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨⟨.label l, t, ⟨nodes - 1, ticks', bytes - (l.utf8ByteSize + (toString l.utf8ByteSize).utf8ByteSize + 2)⟩⟩,
            F, ?_, ?_, ?_, ?_, ?_⟩
          · simp [materializeWith, renameValue, c1, c2]
          · rw [← found]
          · rw [← found]; exact ⟨rfl, rfl, ht⟩
          · rw [← found]; exact rel
          · rw [← found]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      have payloadIn : payload < s.heap.size := valueIn payload (by simp [valueAddresses])
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          have entered : ForcesBy gap F ⟨s.heap, .enter payload, []⟩ ⟨t.heap, .enter (F payload), []⟩ :=
            rel.reenter (.enter payload) [] (by simp [controlAddresses, payloadIn]) (fun _ m => by cases m)
          cases forced : forceWith (fun _ => true) L ticks ⟨s.heap, .enter payload, []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value retained =>
              obtain ⟨F1, st', r1, forcedT, restLe, rel1, valueIn1, ext1, grow1⟩ :=
                forces_forceWith entered heapRoom stackRoom ht forced
              simp at found
              obtain ⟨a, materialized, rfl⟩ := found
              obtain ⟨a', F2, materialized', aValue, aLe, aRel, aGrow, ext2⟩ :=
                ih _ _ value retained st' F1 a rel1 valueIn1 (ticksLe_with _ (by exact restLe)) materialized
              simp only at grow1
              refine ⟨⟨.variant label a'.value, a'.state, a'.remaining⟩, F2, ?_, by simp [aValue], aLe, aRel,
                by simp only; omega, fun x lt => by rw [ext2 x (by omega), ext1 x lt]⟩
              rw [show renameValue F (.variant label payload) = .variant label (F payload) from rfl]
              simp [materializeWith, c1, c2, forcedT, materialized']
            | _ => simp at found
    | record fields =>
      have fieldsIn : AllIn (· < s.heap.size) (fields.map Prod.snd) := valueIn
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              have key := foldlM_forces (gap := gap) (base := s.heap.size) (F0 := F) (L := L) (L' := L')
                (step := fun L => recordStep (fun _ => true) L depth) ?_ fields []
                s t _ _ F out rel (Nat.le_refl _) (fun _ _ => rfl) fieldsIn (ticksLe_with _ (by exact ht)) folded
              · obtain ⟨out', F', folded', same1, outLe, outRel, ext', grow'⟩ := key
                refine ⟨⟨.record out'.1.reverse, out'.2.1, out'.2.2⟩, F', ?_, by simp [same1], outLe, outRel, grow',
                  ext'⟩
                simp [materializeWith_record, renameValue, c1, c2, c3, c4, folded', Function.comp_def]
              · intro acc st st' b b' field out F stRel inField stLe stepped
                obtain ⟨bn, bt, bb⟩ := b
                obtain ⟨bn', bt', bb'⟩ := b'
                obtain ⟨hn, hb, ht2⟩ := stLe
                simp only at hn hb ht2
                subst bn' bb'
                simp [recordStep] at stepped
                split at stepped
                · simp at stepped
                · rename_i cond
                  have entered : ForcesBy gap F ⟨st.heap, .enter field.2, []⟩ ⟨st'.heap, .enter (F field.2), []⟩ :=
                    stRel.reenter (.enter field.2) [] (by simp [controlAddresses, inField]) (fun _ m => by cases m)
                  cases forced : forceWith (fun _ => true) L bt ⟨st.heap, .enter field.2, []⟩ with
                  | mk outcome rest =>
                    rw [forced] at stepped
                    cases outcome with
                    | finished value retained =>
                      obtain ⟨F1, st'', r1, forcedT, restLe, rel1, valueIn1, ext1, grow1⟩ :=
                        forces_forceWith entered heapRoom stackRoom ht2 forced
                      simp at stepped
                      obtain ⟨a, materialized, rfl⟩ := stepped
                      obtain ⟨a', F2, materialized', aValue, aLe, aRel, aGrow, ext2⟩ :=
                        ih _ _ value retained st'' F1 a rel1 valueIn1 (ticksLe_with _ (by exact restLe)) materialized
                      simp only at grow1
                      refine ⟨((field.1, a'.value) :: acc, a'.state, a'.remaining), F2, ?_, by simp [aValue], aLe, aRel,
                        fun x lt => by rw [ext2 x (by omega), ext1 x lt], by simp only; omega⟩
                      simp [recordStep, cond, forcedT, materialized']
                    | _ => simp at stepped
          · simp at found

/-- **Plan extraction transfers along a chain.** -/
theorem forces_yieldedPlan {gap : Nat} {F : Nat → Nat} {y y' : State} (h : ForcesBy gap F y y') {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {budget : Budget} {r : Result}
    (found : yieldedPlan L budget y = .ok r) :
    ∃ r', yieldedPlan L' budget y' = .ok r' ∧ r'.value = r.value := by
  have valid := h.lazyValid
  obtain ⟨ctlEq, _⟩ := h.renames
  unfold yieldedPlan yieldedPlanWith at found ⊢
  cases hc : y.control with
  | yielded plan =>
    rw [hc] at found
    have planIn : plan < y.heap.size := by
      have := valid.control; rw [hc] at this; exact this plan (by simp [controlAddresses])
    have ctlT : y'.control = .yielded (F plan) := by rw [ctlEq, hc]; rfl
    rw [ctlT]
    simp only at found ⊢
    have entered : ForcesBy gap F ⟨y.heap, .enter plan, []⟩ ⟨y'.heap, .enter (F plan), []⟩ :=
      h.reenter (.enter plan) [] (by simp [controlAddresses, planIn]) (fun _ m => by cases m)
    cases forced : forceWith (fun _ => true) L budget.ticks ⟨y.heap, .enter plan, []⟩ with
    | mk outcome rest =>
      rw [forced] at found
      cases outcome with
      | finished value retained =>
        obtain ⟨F1, st', r1, forcedT, restLe, rel1, valueIn1, _, _⟩ :=
          forces_forceWith entered heapRoom stackRoom (Nat.le_refl _) forced
        simp at found
        obtain ⟨a, materialized, rfl⟩ := found
        obtain ⟨a', F2, materialized', aValue, _, _, _, _⟩ :=
          forces_materializeWith heapRoom stackRoom _ _ _ value retained st' F1 a rel1 valueIn1
            (ticksLe_with _ (by exact restLe)) materialized
        refine ⟨{a' with state := {a'.state with control := .yielded (F plan), stack := y'.stack}}, ?_, aValue⟩
        simp [forcedT, materialized']
      | _ => simp at found
  | _ => rw [hc] at found; simp at found

/-- **Completion transfers along a chain.** -/
theorem forces_complete {gap : Nat} {F : Nat → Nat} {y y' : State} (h : ForcesBy gap F y y') {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) {budget : Budget} {r : Result}
    (found : complete L budget y = .ok r) :
    ∃ r', complete L' budget y' = .ok r' ∧ r'.value = r.value := by
  have valid := h.lazyValid
  obtain ⟨ctlEq, stEq⟩ := h.renames
  unfold complete completeWith at found ⊢
  cases hc : y.control with
  | complete v =>
    cases hs : y.stack with
    | nil =>
      have ctlT : y'.control = .complete (renameValue F v) := by rw [ctlEq, hc]; rfl
      have stT : y'.stack = [] := by rw [stEq, hs]; rfl
      have vIn : AllIn (· < y.heap.size) (valueAddresses v) := by
        have := valid.control; rw [hc] at this; exact this
      rw [hc, hs] at found
      rw [ctlT, stT]
      simp at found ⊢
      obtain ⟨a, materialized, rest⟩ := found
      obtain ⟨a', F2, materialized', aValue, _, _, _, _⟩ :=
        forces_materializeWith heapRoom stackRoom _ _ _ v y y' F a h vIn ⟨rfl, rfl, Nat.le_refl _⟩ materialized
      split at rest
      · rename_i bytes encodedAt
        split at rest
        · simp at rest
        · rename_i small
          simp at rest; subst rest
          refine ⟨a', ⟨a', materialized', ?_⟩, aValue⟩
          simp [aValue, encodedAt, small]
      · simp at rest
    | cons fr rest => rw [hc, hs] at found; simp at found
  | _ => rw [hc] at found; simp at found

/-- **A bounded run that does not suspend transfers along a chain**: both runs are their halting
raw runs, whose ends are again in a chain. -/
theorem forces_runBounded {gap : Nat} {F : Nat → Nat} {s t : State} (h : ForcesBy gap F s t) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) (ticks : Nat)
    (notSusp : ∀ r st, runBounded L ticks s ≠ .suspended r st) :
    ∃ (n n' : Nat) (F' : Nat → Nat), runBounded L ticks s = runBounded L 0 (exec n s) ∧
      runBounded L' ticks t = runBounded L' 0 (exec n' t) ∧ ForcesBy gap F' (exec n s) (exec n' t) := by
  obtain ⟨n, le, halts, fits, eq⟩ := runBounded_halts L ticks s notSusp
  obtain ⟨n', F', le', haltsT, fitsT, rel, _⟩ := forces_fits h heapRoom stackRoom halts fits
  exact ⟨n, n', F', eq, runBounded_of_halts L' ticks t n' haltsT (by omega) fitsT, rel⟩

/-- The terminal outcomes of a chain's two ends correspond. -/
theorem runBounded_zero_forces {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) (L L' : Limits) :
    (∀ v y, runBounded L 0 σ = .finished v y → y = σ ∧ runBounded L' 0 τ = .finished (renameValue F v) τ) ∧
    (∀ p y, runBounded L 0 σ = .yielded p y → y = σ ∧ runBounded L' 0 τ = .yielded (F p) τ) ∧
    (∀ a y, runBounded L 0 σ = .divergent a y → runBounded L' 0 τ = .divergent (F a) τ) ∧
    (∀ reason y, runBounded L 0 σ = .refused reason y → runBounded L' 0 τ = .refused reason τ) := by
  have ctl := h.renames.1
  refine ⟨fun v y ran => ?_, fun p y ran => ?_, fun a y ran => ?_, fun reason y ran => ?_⟩ <;>
    cases hc : σ.control <;> simp only [runBounded, hc] at ran <;> cases ran <;>
    simp [runBounded, ctl, hc, renameControl]

/-- **One segment's four endings transfer along a chain**, with heap headroom of its gap: a
yield whose Plan extracts, a completion that extracts, a divergence, a refusal. -/
public theorem forces_segment {gap : Nat} {F : Nat → Nat} {s t : State} (h : ForcesBy gap F s t) {L L' : Limits}
    (heapRoom : L.heap + gap ≤ L'.heap) (stackRoom : L.stack ≤ L'.stack) (ticks : Nat) (budget : Budget) :
    (∀ plan y r, runBounded L ticks s = .yielded plan y → yieldedPlan L budget y = .ok r →
      ∃ plan' y' r', runBounded L' ticks t = .yielded plan' y' ∧ yieldedPlan L' budget y' = .ok r' ∧
        r'.value = r.value) ∧
    (∀ value y r, runBounded L ticks s = .finished value y → complete L budget y = .ok r →
      ∃ value' y' r', runBounded L' ticks t = .finished value' y' ∧ complete L' budget y' = .ok r' ∧
        r'.value = r.value) ∧
    (∀ address y, runBounded L ticks s = .divergent address y →
      ∃ address' y', runBounded L' ticks t = .divergent address' y') ∧
    (∀ reason y, runBounded L ticks s = .refused reason y → ∃ y', runBounded L' ticks t = .refused reason y') := by
  refine ⟨fun plan y r ran extracted => ?_, fun value y r ran completed => ?_, fun address y ran => ?_,
    fun reason y ran => ?_⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    obtain ⟨same, ranT⟩ := (runBounded_zero_forces rel L L').2.1 plan y ran
    subst same
    obtain ⟨r', extracted', value⟩ := forces_yieldedPlan rel heapRoom stackRoom extracted
    exact ⟨_, _, r', by rw [eqT, ranT], extracted', value⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    obtain ⟨same, ranT⟩ := (runBounded_zero_forces rel L L').1 value y ran
    subst same
    obtain ⟨r', completed', value⟩ := forces_complete rel heapRoom stackRoom completed
    exact ⟨_, _, r', by rw [eqT, ranT], completed', value⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    exact ⟨_, _, by rw [eqT, (runBounded_zero_forces rel L L').2.2.1 address y ran]⟩
  · obtain ⟨n, n', F', eq, eqT, rel⟩ := forces_runBounded h heapRoom stackRoom ticks
      (fun _ _ h' => by rw [ran] at h'; cases h')
    rw [eq] at ran
    exact ⟨_, by rw [eqT, (runBounded_zero_forces rel L L').2.2.2 reason y ran]⟩

/-! ## A successful extraction is a forcing chain -/

/-- **`H` forces to `H'`**: both valid, `H'` extends `H`, and on every valid control and stack of
`H`, `H` forces to `H'` (headroom: the cells `H'` added) by a map that is the identity on `H`. -/
public def HeapForces (H H' : Array Cell) : Prop :=
  HeapValid H ∧ HeapValid H' ∧ H.size ≤ H'.size ∧ ∃ F : Nat → Nat, (∀ a, a < H.size → F a = a) ∧
    ∀ (c : Control) (S : List Frame), AllIn (· < H.size) (controlAddresses c) →
      (∀ fr ∈ S, AllIn (· < H.size) (frameAddresses fr)) →
      ForcesBy (H'.size - H.size) F ⟨H, c, S⟩ ⟨H', c, S⟩

theorem heapForces_refl {H : Array Cell} (valid : HeapValid H) : HeapForces H H :=
  ⟨valid, valid, Nat.le_refl _, id, fun _ _ => rfl, fun _ _ cIn sIn =>
    .agree (agreeRel_refl ⟨valid, cIn, sIn⟩) (by simp)⟩

theorem heapForces_trans {H1 H2 H3 : Array Cell} (one : HeapForces H1 H2) (two : HeapForces H2 H3) :
    HeapForces H1 H3 := by
  obtain ⟨v1, _, le1, F1, id1, ch1⟩ := one
  obtain ⟨_, v3, le2, F2, id2, ch2⟩ := two
  refine ⟨v1, v3, by omega, F2 ∘ F1, fun a lt => by simp [Function.comp_apply, id1 a lt, id2 a (by omega)],
    fun c S cIn sIn => ?_⟩
  exact .trans (ch1 c S cIn sIn) (ch2 c S (allBelow_mono cIn le1) (frames_mono sIn le1)) (by omega)

/-- **A finished closed demand makes its base force to its final heap** (`demand_forces`). -/
theorem heapForces_demand {H : Array Cell} {a n : Nat} {H' : Array Cell} {v : RuntimeValue} (valid : HeapValid H)
    (d : Demand H a n H' v) : HeapForces H H' := by
  obtain ⟨F, Fid, chain⟩ := demand_forces n H a H' v valid d
  have aLt := (demand_cell_lt d).1
  have grow : H.size ≤ H'.size := by
    have := exec_size_mono (demandStart H a) n; rw [d.final] at this; exact this
  have valid' : HeapValid H' := by
    have := heapValid_exec (addrValid_demandStart valid aLt) n; rw [d.final] at this; exact this
  exact ⟨valid, valid', grow, F, Fid, chain⟩

/-- A transition that completes leaves an empty stack. -/
theorem stepRaw_complete_stack {s : State} {v : RuntimeValue} (act : active s.control = true)
    (h : (stepRaw s).control = .complete v) : (stepRaw s).stack = [] := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | returned w =>
    cases stack with
    | nil => rfl
    | cons fr rest =>
      cases fr <;> simp only [stepRaw] at h ⊢ <;> (repeat' split at h) <;> simp_all
  | evaluate term env =>
    cases term <;> simp only [stepRaw] at h <;> (repeat' split at h) <;> simp_all
  | enter a => simp only [stepRaw] at h; split at h <;> simp_all
  | _ => simp [active] at act

/-- **Forcing a cell with the open policy is its closed demand.** -/
theorem forceWith_demand {L : Limits} {T : Nat} {H : Array Cell} {a : Nat} {v : RuntimeValue} {st : State} {r : Nat}
    (ran : forceWith (fun _ => true) L T ⟨H, .enter a, []⟩ = (.finished v st, r)) :
    ∃ n, Demand H a n st.heap v := by
  obtain ⟨n, _, halts, _, eq, ctl, _⟩ := forceWith_finished L T _ v st r ran
  have pos : n ≠ 0 := by
    intro h0; subst h0; have := halts.2; simp [exec, active] at this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have act : active (exec m ⟨H, .enter a, []⟩).control = true := halts.1 m (by omega)
  have stack : st.stack = [] := by
    rw [← eq, exec_succ]; exact stepRaw_complete_stack act (by rw [← exec_succ, eq, ctl])
  refine ⟨m + 1, halts, ?_⟩
  show exec (m + 1) ⟨H, .enter a, []⟩ = _
  rw [eq, state_ext (s := st), ctl, stack]

theorem foldlM_invariant {α β ε : Type} {step : β → α → Except ε β} (P : β → Prop)
    (stepP : ∀ x a y, P x → step x a = .ok y → P y) :
    ∀ (l : List α) (x y : β), P x → l.foldlM step x = .ok y → P y := by
  intro l
  induction l with
  | nil => intro x y px folded; simp [List.foldlM] at folded; subst folded; exact px
  | cons a rest ih =>
    intro x y px folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    exact ih mid y (stepP x a mid px first) restFolded

/-- **A successful materialization is a forcing chain.** -/
theorem materializeWith_heapForces (L : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (s : State) (r : Result), HeapValid s.heap →
      materializeWith (fun _ => true) L depth budget value s = .ok r → HeapForces s.heap r.state.heap := by
  intro depth
  induction depth with
  | zero => intro budget value s r _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget value s r valid found
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact heapForces_refl valid
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact heapForces_refl valid
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · simp at found; rw [← found]; exact heapForces_refl valid
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · cases forced : forceWith (fun _ => true) L budget.ticks ⟨s.heap, .enter payload, []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value retained =>
              obtain ⟨n, d⟩ := forceWith_demand forced
              have one := heapForces_demand valid d
              simp at found
              obtain ⟨a, materialized, rfl⟩ := found
              exact heapForces_trans one (ih _ _ _ a one.2.1 materialized)
            | _ => simp at found
    | record fields =>
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              refine foldlM_invariant (fun x => HeapForces s.heap x.2.1.heap) ?_ fields _ out
                (heapForces_refl valid) folded
              intro x field y px stepped
              simp [recordStep] at stepped
              split at stepped
              · simp at stepped
              · cases forced : forceWith (fun _ => true) L x.2.2.ticks ⟨x.2.1.heap, .enter field.2, []⟩ with
                | mk outcome rest =>
                  rw [forced] at stepped
                  cases outcome with
                  | finished value retained =>
                    obtain ⟨n, d⟩ := forceWith_demand forced
                    have one := heapForces_demand px.2.1 d
                    simp at stepped
                    obtain ⟨a, materialized, rfl⟩ := stepped
                    exact heapForces_trans px (heapForces_trans one (ih _ _ _ a one.2.1 materialized))
                  | _ => simp at stepped
          · simp at found

/-- **A successful Plan extraction is a forcing chain**: the yielded heap forces to the
extraction's heap. -/
theorem yieldedPlan_heapForces {L : Limits} {budget : Budget} {y : State} {r : Result} (valid : HeapValid y.heap)
    (found : yieldedPlan L budget y = .ok r) : HeapForces y.heap r.state.heap := by
  unfold yieldedPlan yieldedPlanWith at found
  cases hc : y.control with
  | yielded plan =>
    rw [hc] at found
    simp only at found
    cases forced : forceWith (fun _ => true) L budget.ticks ⟨y.heap, .enter plan, []⟩ with
    | mk outcome rest =>
      rw [forced] at found
      cases outcome with
      | finished value retained =>
        obtain ⟨n, d⟩ := forceWith_demand forced
        have one := heapForces_demand valid d
        simp at found
        obtain ⟨a, materialized, rfl⟩ := found
        exact heapForces_trans one (materializeWith_heapForces L _ _ _ _ a one.2.1 materialized)
      | _ => simp at found
  | _ => rw [hc] at found; simp at found

/-- **The resumed yield forces to the resumed extraction**: resuming a valid yield and resuming
the state its Plan extraction left (the same control and stack over the larger heap) are related
by a forcing chain whose headroom is the cells the extraction added. -/
public theorem yieldedPlan_forces {L : Limits} {budget : Budget} {y : State} {r : Result} (valid : AddrValid y)
    (found : yieldedPlan L budget y = .ok r) (c : Control) (cIn : AllIn (· < y.heap.size) (controlAddresses c)) :
    ∃ F, ForcesBy (r.state.heap.size - y.heap.size) F ⟨y.heap, c, y.stack⟩ ⟨r.state.heap, c, y.stack⟩ := by
  obtain ⟨_, _, _, F, _, chain⟩ := yieldedPlan_heapForces valid.heap found
  exact ⟨F, chain c y.stack cIn valid.stack⟩


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Back.lean` -/
/-! ## Halting, backward -/

theorem halts_prepend {s : State} {m k : Nat} (live : ∀ j, j < m → active (exec j s).control = true)
    (h : Halts (exec m s) k) : Halts s (m + k) := by
  refine ⟨fun j lt => ?_, ?_⟩
  · by_cases jm : j < m
    · exact live j jm
    · have := h.1 (j - m) (by omega)
      rwa [← exec_add, show m + (j - m) = j by omega] at this
  · rw [exec_add]; exact h.2

/-- Exactly agreeing runs halt together, read backward. -/
theorem agree_halts_back {f : Nat → Nat} {σ τ : State} (rel : AgreeRel f σ τ) {n : Nat} (halts : Halts τ n) :
    Halts σ n := by
  have all : ∀ j, StateAgree f everywhere (fun _ => False) (exec j σ) (exec j τ) :=
    fun j => agree_exec rel.agree j (fun _ _ _ _ h => h)
  exact ⟨fun j lt => by rw [← (all j).active_eq]; exact halts.1 j lt,
    by rw [← (all n).active_eq]; exact halts.2⟩

/-- **Through a pending demand, backward**: if the forced run halts, the lazy run halts. When
the lazy run enters the pending cell it runs the cell's closed demand (`pend_switch`, which
needs no halting premise: the demand is the one the extraction finished), then agrees
exactly with the forced run, which returned the cached value in one transition. -/
theorem pend_halts_back {e : Pending} {f : Nat → Nat} :
    ∀ (n : Nat) (σ τ : State), PendRel e f σ τ → Halts τ n → ∃ m, Halts σ m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ τ rel halts
  have activeT : active τ.control = active σ.control := by rw [rel.control, active_rename]
  cases act : active σ.control with
  | false => exact ⟨0, fun _ h => by omega, by simp only [exec]; exact act⟩
  | true =>
    have npos : 1 ≤ n := by
      apply Classical.byContradiction; intro h
      have := halts.2; rw [show n = 0 by omega] at this; simp only [exec] at this
      rw [activeT, act] at this; cases this
    have tail : Halts (stepRaw τ) (n - 1) := halts_tail (by rw [show n - 1 + 1 = n by omega]; exact halts)
    by_cases reads : readsAt σ = some e.cell
    · cases ctl : σ.control with
      | enter b =>
        have bEq : b = e.cell := by simp [readsAt, ctl] at reads; exact reads
        subst bEq
        obtain ⟨_, liveLazy, _, _, _, _, agreeNew, _, _⟩ := pend_switch rel ctl
        exact ⟨_, halts_prepend (fun j lt => liveLazy j (by omega)) (agree_halts_back agreeNew tail)⟩
      | returned v =>
        obtain ⟨rest, st⟩ : ∃ rest, σ.stack = .update e.cell :: rest := by
          cases st : σ.stack with
          | nil => simp [readsAt, ctl, st] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, ctl, st] at reads
            exact ⟨rest, by rw [reads]⟩
        obtain ⟨_, inactive⟩ := pend_update_read rel ctl st
        exact ⟨1, fun j lt => by rw [show j = 0 by omega]; exact act, by rw [exec_one]; exact inactive⟩
      | _ => simp [readsAt, ctl] at reads
    · obtain ⟨m, hm⟩ := ih (n - 1) (by omega) _ _ (pend_step rel reads) tail
      exact ⟨m + 1, halts_succ act hm⟩

/-- **Along a forcing chain, backward**: a forced run that halts has a lazy run that halts. -/
theorem forces_halts_back {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    ∀ n, Halts τ n → ∃ m, Halts σ m := by
  induction h with
  | pend r _ => exact fun n halts => pend_halts_back n _ _ r halts
  | agree r _ => exact fun n halts => ⟨n, agree_halts_back r halts⟩
  | trans _ _ _ ih1 ih2 =>
    intro n halts
    obtain ⟨k, hk⟩ := ih2 n halts
    exact ih1 k hk

/-- **Backward transfer**: the forced run halting at `n'`, the lazy run halts no earlier, and
the two ends are again in a chain (the forward theorem `forces_transfer` read at the lazy
run's own halting time, which `forces_halts_back` supplies). -/
theorem forces_transfer_back {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ)
    {n' : Nat} (halts : Halts τ n') :
    ∃ n F', n' ≤ n ∧ Halts σ n ∧ Bounded σ τ n n' gap ∧ ForcesBy gap F' (exec n σ) (exec n' τ) ∧
      ∀ a, a < σ.heap.size → F' a = F a := by
  obtain ⟨n, hn⟩ := forces_halts_back h n' halts
  obtain ⟨n'', F', le, haltsT, bounded, rel, ext⟩ := forces_transfer h n hn
  have same := halts_unique haltsT halts
  subst same
  exact ⟨n, F', le, hn, bounded, rel, ext⟩


/-! ## Backward simulations -/

/-- **A backward simulation** `R F s t` (lazy `s`, forced `t`, address map `F`), over a domain
`Dom` of lazy addresses that depends only on the heap: controls and stacks are renamed, held
addresses are in the domain, any domain control and stack re-enter related, and a forced run
that halts has a lazy run that halts, ending related, under a map that extends `F` on the
domain (which only grows). -/
public structure BackSim (R : (Nat → Nat) → State → State → Prop) (Dom : Array Cell → Nat → Prop) : Prop where
  renames : ∀ {F : Nat → Nat} {s t : State}, R F s t →
    t.control = renameControl F s.control ∧ t.stack = s.stack.map (renameFrame F)
  controlIn : ∀ {F : Nat → Nat} {s t : State}, R F s t → AllIn (Dom s.heap) (controlAddresses s.control)
  stackIn : ∀ {F : Nat → Nat} {s t : State}, R F s t → ∀ fr ∈ s.stack, AllIn (Dom s.heap) (frameAddresses fr)
  reenter : ∀ {F : Nat → Nat} {s t : State} (c : Control) (S : List Frame), R F s t →
    AllIn (Dom s.heap) (controlAddresses c) → (∀ fr ∈ S, AllIn (Dom s.heap) (frameAddresses fr)) →
    R F ⟨s.heap, c, S⟩ ⟨t.heap, renameControl F c, S.map (renameFrame F)⟩
  back : ∀ {F : Nat → Nat} {s t : State} {n' : Nat}, R F s t → Halts t n' →
    ∃ n F', Halts s n ∧ R F' (exec n s) (exec n' t) ∧ ∀ a, Dom s.heap a → Dom (exec n s).heap a ∧ F' a = F a

/-- The threshold form of "the lazy side commits too": every resource vector at least
`(L0, T0)` commits, to `out`, with `T - T0` ticks left. -/
public def ForceAbove (L0 : Limits) (n : Nat) (s : State) (v : RuntimeValue) (st : State) : Prop :=
  ∀ (L : Limits) (T : Nat), LimitsLe L0 L → n ≤ T → forceWith (fun _ => true) L T s = (.finished v st, T - n)

/-- **Forcing, backward.** -/
public theorem BackSim.forceWith {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t)
    {L' : Limits} {T' : Nat} {v' : RuntimeValue} {st' : State} {r' : Nat}
    (ran : Obend.Core.Data.forceWith (fun _ => true) L' T' t = (.finished v' st', r')) :
    ∃ (n : Nat) (L0 : Limits) (v : RuntimeValue) (F' : Nat → Nat),
      ForceAbove L0 n s v (exec n s) ∧ renameValue F' v = v' ∧ R F' (exec n s) st' ∧
      AllIn (Dom (exec n s).heap) (valueAddresses v) ∧
      (∀ a, Dom s.heap a → Dom (exec n s).heap a ∧ F' a = F a) := by
  obtain ⟨n', _, haltsT, _, eq, ctl, _⟩ := forceWith_finished L' T' t v' st' r' ran
  obtain ⟨n, F', halts, rel', ext⟩ := sim.back rel haltsT
  rw [eq] at rel'
  obtain ⟨L0, fits⟩ := fitsFrom_exists s n
  have ctlR := (sim.renames rel').1
  have inside := sim.controlIn rel'
  rw [ctl] at ctlR
  cases hc : (exec n s).control with
  | complete v =>
    rw [hc] at ctlR inside
    simp only [renameControl, Control.complete.injEq] at ctlR
    subst ctlR
    exact ⟨n, L0, v, F', fun L T le nle => forceWith_of_halts L T s n v halts nle (fitsFrom_mono le fits) hc,
      rfl, rel', inside, ext⟩
  | _ => rw [hc] at ctlR; simp [renameControl] at ctlR

/-- Materialization backward at one depth: the forced side's success has, above a threshold,
a lazy success to the same Data with the same nodes and bytes left, `k` ticks left for every
`T0 + k` given, ending in a related state that does not depend on the resources given. -/
public def MaterializeBack (R : (Nat → Nat) → State → State → Prop) (Dom : Array Cell → Nat → Prop)
    (L' : Limits) (depth : Nat) : Prop :=
  ∀ (budget' : Budget) (v : RuntimeValue) (s t : State) (F : Nat → Nat) (r' : Result),
    R F s t → AllIn (Dom s.heap) (valueAddresses v) →
    materializeWith (fun _ => true) L' depth budget' (renameValue F v) t = .ok r' →
    ∃ (L0 : Limits) (T0 : Nat) (st : State) (F' : Nat → Nat), R F' st r'.state ∧
      (∀ a, Dom s.heap a → Dom st.heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        materializeWith (fun _ => true) L depth ⟨budget'.nodes, T0 + k, budget'.bytes⟩ v s =
          .ok ⟨r'.value, st, ⟨r'.remaining.nodes, k, r'.remaining.bytes⟩⟩

/-- **The record fold, backward.** -/
public theorem BackSim.fold {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {L' : Limits} {depth : Nat} (ih : MaterializeBack R Dom L' depth) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (s t : State) (b' : Budget)
      (F : Nat → Nat) (out' : List (String × Data) × State × Budget),
      R F s t → AllIn (Dom s.heap) (fields.map Prod.snd) →
      (fields.map fun field => (field.1, F field.2)).foldlM (recordStep (fun _ => true) L' depth)
        (acc, t, b') = .ok out' →
      ∃ (L0 : Limits) (T0 : Nat) (st : State) (F' : Nat → Nat), R F' st out'.2.1 ∧
        (∀ a, Dom s.heap a → Dom st.heap a ∧ F' a = F a) ∧
        ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
          fields.foldlM (recordStep (fun _ => true) L depth) (acc, s, ⟨b'.nodes, T0 + k, b'.bytes⟩) =
            .ok (out'.1, st, ⟨out'.2.2.nodes, k, out'.2.2.bytes⟩) := by
  intro fields
  induction fields with
  | nil =>
    intro acc s t b' F out' rel _ folded
    simp at folded
    subst folded
    exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [List.foldlM]⟩
  | cons field rest ihf =>
    intro acc s t b' F out' rel inside folded
    simp only [List.map_cons, List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid', first', restFolded⟩ := folded
    have fieldIn : Dom s.heap field.2 := inside field.2 (by simp)
    obtain ⟨nodes, ticks', bytes⟩ := b'
    simp [recordStep] at first'
    split at first'
    · simp at first'
    · rename_i cond
      have entered := sim.reenter (.enter field.2) [] rel (by simpa [controlAddresses] using fieldIn)
        (fun _ m => by cases m)
      cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F field.2), []⟩ with
      | mk outcome rest' =>
        rw [forced] at first'
        cases outcome with
        | finished value' retained' =>
          simp at first'
          obtain ⟨a', materialized, rfl⟩ := first'
          obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
          subst vEq
          obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := ih _ v _ _ F1 a' rel1 vIn materialized
          have restIn : AllIn (Dom st2.heap) (rest.map Prod.snd) := fun x m =>
            (ext2 x (ext1 x (inside x (by simp at m ⊢; exact Or.inr m))).1).1
          have restMap : rest.map (fun field => (field.1, F field.2)) =
              rest.map (fun field => (field.1, F2 field.2)) := by
            apply List.map_congr_left
            intro fld m
            have dx : Dom s.heap fld.2 := inside fld.2 (by simp; exact Or.inr ⟨fld.1, m⟩)
            rw [(ext2 _ (ext1 _ dx).1).2, (ext1 _ dx).2]
          rw [restMap] at restFolded
          obtain ⟨L3, T3, st3, F3, rel3, ext3, tail⟩ := ihf _ st2 _ _ F2 out' rel2 restIn restFolded
          refine ⟨limitsMax L1 (limitsMax L2 L3), n + (T2 + T3), st3, F3, rel3, fun x hx => ?_, fun L k le => ?_⟩
          · obtain ⟨d1, f1⟩ := ext1 x hx
            obtain ⟨d2, f2⟩ := ext2 x d1
            obtain ⟨d3, f3⟩ := ext3 x d2
            exact ⟨d3, by rw [f3, f2, f1]⟩
          · have le1 := limitsLe_trans (limitsLe_max_left _ _) le
            have le2 := limitsLe_trans (limitsLe_trans (limitsLe_max_left _ _) (limitsLe_max_right _ _)) le
            have le3 := limitsLe_trans (limitsLe_trans (limitsLe_max_right _ _) (limitsLe_max_right _ _)) le
            have runL := above L (n + (T2 + T3) + k) le1 (by omega)
            rw [show n + (T2 + T3) + k - n = T2 + (T3 + k) by omega] at runL
            have childL := child L (T3 + k) le2
            simp only [List.foldlM_cons, except_bind_ok]
            refine ⟨((field.1, a'.value) :: acc, st2, ⟨a'.remaining.nodes, T3 + k, a'.remaining.bytes⟩), ?_, tail L k le3⟩
            simp [recordStep, cond, runL, childL]
        | _ => simp at first'

/-- **Materialization, backward.** -/
public theorem BackSim.materialize {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) (L' : Limits) : ∀ depth, MaterializeBack R Dom L' depth := by
  intro depth
  induction depth with
  | zero => intro budget' v s t F r' _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget' v s t F r' rel valueIn found
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases v with
    | natural m =>
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          subst found
          exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [materializeWith, c1, c2]⟩
    | boolean b =>
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          subst found
          exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [materializeWith, c1, c2]⟩
    | label l =>
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          subst found
          exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [materializeWith, c1, c2]⟩
    | closure body environment =>
      simp [materializeWith, renameValue] at found; split at found <;> simp at found
    | specification metadata extension =>
      simp [materializeWith, renameValue] at found; split at found <;> simp at found
    | prototype spec target =>
      simp [materializeWith, renameValue] at found; split at found <;> simp at found
    | variant label payload =>
      have payloadIn : Dom s.heap payload := valueIn payload (by simp [valueAddresses])
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          have entered := sim.reenter (.enter payload) [] rel (by simpa [controlAddresses] using payloadIn)
            (fun _ m => by cases m)
          cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F payload), []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value' retained' =>
              simp at found
              obtain ⟨a', materialized, rfl⟩ := found
              obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
              subst vEq
              obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := ih _ v _ _ F1 a' rel1 vIn materialized
              refine ⟨limitsMax L1 L2, n + T2, st2, F2, rel2, fun x hx => ?_, fun L k le => ?_⟩
              · obtain ⟨d1, f1⟩ := ext1 x hx
                obtain ⟨d2, f2⟩ := ext2 x d1
                exact ⟨d2, by rw [f2, f1]⟩
              · have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
                rw [show n + T2 + k - n = T2 + k by omega] at runL
                have childL := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
                simp [materializeWith, c1, c2, runL, childL]
            | _ => simp at found
    | record fields =>
      have fieldsIn : AllIn (Dom s.heap) (fields.map Prod.snd) := valueIn
      simp only [renameValue] at found
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out', folded, rfl⟩ := (except_map_ok _ _ _).mp found
              obtain ⟨L0, T0, st, F', rel', ext', fold⟩ :=
                sim.fold (ih) fields [] s t _ F out' rel fieldsIn folded
              refine ⟨L0, T0, st, F', rel', ext', fun L k le => ?_⟩
              have foldL := fold L k le
              have c3' : (fields.map Prod.fst).eraseDups.length = fields.length := by
                simpa [Function.comp_def] using c3
              simp [materializeWith_record, c1, c2, c3', c4, foldL]
          · simp at found

/-- Renaming a held state by two maps that agree on the domain gives the same state. -/
theorem rename_state_congr {Dom : Array Cell → Nat → Prop} {F G : Nat → Nat} {H : Array Cell} {c : Control}
    {S : List Frame} (cIn : AllIn (Dom H) (controlAddresses c)) (sIn : ∀ fr ∈ S, AllIn (Dom H) (frameAddresses fr))
    (same : ∀ a, Dom H a → G a = F a) :
    renameControl G c = renameControl F c ∧ S.map (renameFrame G) = S.map (renameFrame F) :=
  ⟨renameControl_congr (fun x m => same x (cIn x m)),
    List.map_congr_left (fun fr m => renameFrame_congr (fun x mx => same x (sIn fr m x mx)))⟩

/-- **Plan extraction, backward**: the forced yield's Plan extracts, so the lazy yield's Plan
extracts to the same Data above a threshold (heap and stack room, extraction ticks), with the
same nodes and bytes left, ending in a related state (the checkpoint candidates). -/
public theorem BackSim.yieldedPlan {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {r' : Result} (found : Obend.Core.Data.yieldedPlan L' budget' y' = .ok r') :
    ∃ (L0 : Limits) (E0 : Nat) (st : State) (F' : Nat → Nat), R F' st r'.state ∧
      (∀ a, Dom y.heap a → Dom st.heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        Obend.Core.Data.yieldedPlan L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y =
          .ok ⟨r'.value, st, ⟨r'.remaining.nodes, k, r'.remaining.bytes⟩⟩ := by
  obtain ⟨ctlEq, stEq⟩ := sim.renames rel
  have cIn := sim.controlIn rel
  have sIn := sim.stackIn rel
  unfold Obend.Core.Data.yieldedPlan yieldedPlanWith at found ⊢
  cases hc : y.control with
  | yielded plan =>
    rw [ctlEq, hc] at found
    rw [hc] at cIn
    simp only [renameControl] at found
    have planIn : Dom y.heap plan := cIn plan (by simp [controlAddresses])
    have entered := sim.reenter (.enter plan) [] rel (by simpa [controlAddresses] using planIn) (fun _ m => by cases m)
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨y'.heap, .enter (F plan), []⟩ with
    | mk outcome rest =>
      simp only at found
      rw [forced] at found
      cases outcome with
      | finished value' retained' =>
        simp at found
        obtain ⟨a', materialized, rfl⟩ := found
        obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
        subst vEq
        obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := sim.materialize L' _ _ v _ _ F1 a' rel1 vIn materialized
        have ext : ∀ a, Dom y.heap a → Dom st2.heap a ∧ F2 a = F a := fun x hx => by
          obtain ⟨d1, f1⟩ := ext1 x hx
          obtain ⟨d2, f2⟩ := ext2 x d1
          exact ⟨d2, by rw [f2, f1]⟩
        have cIn' : AllIn (Dom st2.heap) (controlAddresses (.yielded plan)) := fun x m => (ext x (cIn x m)).1
        have sIn' : ∀ fr ∈ y.stack, AllIn (Dom st2.heap) (frameAddresses fr) := fun fr m x mx => (ext x (sIn fr m x mx)).1
        have back := sim.reenter (.yielded plan) y.stack rel2 cIn' sIn'
        obtain ⟨cSame, sSame⟩ := rename_state_congr (Dom := Dom) (H := y.heap) (c := .yielded plan) (S := y.stack)
          cIn sIn (fun a h => (ext a h).2)
        rw [cSame, sSame, ← stEq] at back
        refine ⟨limitsMax L1 L2, n + T2, ⟨st2.heap, .yielded plan, y.stack⟩, F2, back, fun x hx => ⟨(ext x hx).1, (ext x hx).2⟩,
          fun L k le => ?_⟩
        have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
        rw [show n + T2 + k - n = T2 + k by omega] at runL
        have childL := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
        simp [runL, childL]
      | _ => simp at found
  | _ => rw [ctlEq, hc] at found; simp [renameControl] at found

/-- **Completion, backward.** -/
public theorem BackSim.complete {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {r' : Result} (found : Obend.Core.Data.complete L' budget' y' = .ok r') :
    ∃ (L0 : Limits) (E0 : Nat) (st : State) (F' : Nat → Nat), R F' st r'.state ∧
      (∀ a, Dom y.heap a → Dom st.heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        Obend.Core.Data.complete L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y =
          .ok ⟨r'.value, st, ⟨r'.remaining.nodes, k, r'.remaining.bytes⟩⟩ := by
  obtain ⟨ctlEq, stEq⟩ := sim.renames rel
  have cIn := sim.controlIn rel
  unfold Obend.Core.Data.complete completeWith at found ⊢
  obtain ⟨nodes, ticks', bytes⟩ := budget'
  cases hc : y.control with
  | complete v =>
    cases hs : y.stack with
    | nil =>
      rw [ctlEq, stEq, hc, hs] at found
      rw [hc] at cIn
      simp only [renameControl, List.map_nil] at found
      simp at found
      obtain ⟨a', materialized, rest⟩ := found
      obtain ⟨L0, T0, st, F', rel', ext', child⟩ := sim.materialize L' _ _ v _ _ F a' rel cIn materialized
      split at rest
      · rename_i encodedBytes encodedAt
        split at rest
        · simp at rest
        · rename_i small
          simp at rest
          subst rest
          refine ⟨L0, T0, st, F', rel', ext', fun L k le => ?_⟩
          have childL := child L k le
          simp [childL, encodedAt, small]
      · simp at rest
    | cons fr rest => rw [ctlEq, stEq, hc, hs] at found; simp at found
  | _ => rw [ctlEq, hc] at found; simp [renameControl] at found

/-- **Bounded runs, backward**: a forced bounded run that does not suspend has a lazy run that,
under every limits and ticks above a threshold, is its halting raw run, the two ends related. -/
public theorem BackSim.runBounded {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    (notSusp : ∀ r st, Obend.Core.Machine.runBounded L' T' t ≠ .suspended r st) :
    ∃ (n n' : Nat) (L0 : Limits) (F' : Nat → Nat), R F' (exec n s) (exec n' t) ∧
      Obend.Core.Machine.runBounded L' T' t = Obend.Core.Machine.runBounded L' 0 (exec n' t) ∧
      (∀ a, Dom s.heap a → Dom (exec n s).heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (T : Nat), LimitsLe L0 L → n ≤ T →
        Obend.Core.Machine.runBounded L T s = Obend.Core.Machine.runBounded L 0 (exec n s) := by
  obtain ⟨n', _, haltsT, _, eqT⟩ := runBounded_halts L' T' t notSusp
  obtain ⟨n, F', halts, rel', ext⟩ := sim.back rel haltsT
  obtain ⟨L0, fits⟩ := fitsFrom_exists s n
  exact ⟨n, n', L0, F', rel', eqT, ext,
    fun L T le nle => runBounded_of_halts L T s n halts nle (fitsFrom_mono le fits)⟩

/-! ## Terminal states -/

public theorem runBounded_zero_yielded {L : Limits} {s y : State} {p : Nat} :
    Obend.Core.Machine.runBounded L 0 s = .yielded p y ↔ s.control = .yielded p ∧ y = s := by
  cases hc : s.control <;> simp [Obend.Core.Machine.runBounded, hc, eq_comm]

theorem runBounded_zero_finished {L : Limits} {s y : State} {v : RuntimeValue} :
    Obend.Core.Machine.runBounded L 0 s = .finished v y ↔ s.control = .complete v ∧ y = s := by
  cases hc : s.control <;> simp [Obend.Core.Machine.runBounded, hc, eq_comm]

theorem runBounded_zero_divergent {L : Limits} {s y : State} {a : Nat} :
    Obend.Core.Machine.runBounded L 0 s = .divergent a y ↔ s.control = .blackhole a ∧ y = s := by
  cases hc : s.control <;> simp [Obend.Core.Machine.runBounded, hc, eq_comm]

theorem runBounded_zero_refused {L : Limits} {s y : State} {reason : Refusal} :
    Obend.Core.Machine.runBounded L 0 s = .refused reason y ↔ s.control = .refused reason ∧ y = s := by
  cases hc : s.control <;> simp [Obend.Core.Machine.runBounded, hc, eq_comm]

/-! ## Instances -/

/-- **Forcing chains are backward simulations.** -/
public theorem forcesSim (gap : Nat) : BackSim (ForcesBy gap) (fun H a => a < H.size) where
  renames h := h.renames
  controlIn h := h.lazyValid.control
  stackIn h := h.lazyValid.stack
  reenter c S h cIn sIn := h.reenter c S cIn sIn
  back h halts := by
    obtain ⟨n, F', _, hn, _, rel, ext⟩ := forces_transfer_back h halts
    exact ⟨n, F', hn, rel, fun a lt => ⟨Nat.lt_of_lt_of_le lt (exec_size_mono _ n), ext a lt⟩⟩

theorem related_exec {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t) :
    ∀ n, Related f D (exec n s) (exec n t) := by
  intro n
  induction n with
  | zero => exact related
  | succ n ih => rw [exec_succ, exec_succ]; exact related_stepRaw ih

/-- **A renaming relation (the collection's) is a backward simulation**: it is lockstep, so
the original halts exactly when the renamed state does. -/
public theorem relatedSim (f : Nat → Nat) (D : Nat → Prop) :
    BackSim (fun F s t => F = f ∧ Related f D s t) (fun _ a => D a) where
  renames h := by obtain ⟨rfl, r⟩ := h; exact ⟨r.control, r.stack⟩
  controlIn h := h.2.controlIn
  stackIn h := h.2.stackIn
  reenter c S h cIn sIn := by obtain ⟨rfl, r⟩ := h; exact ⟨rfl, ⟨r.heap, cIn, rfl, sIn, rfl⟩⟩
  back h halts := by
    obtain ⟨rfl, r⟩ := h
    have all := related_exec r
    refine ⟨_, _, ⟨fun j lt => ?_, ?_⟩, ⟨rfl, all _⟩, fun a d => ⟨d, rfl⟩⟩
    · have := halts.1 j lt; rwa [(all j).control, active_rename] at this
    · have := halts.2; rwa [(all _).control, active_rename] at this

/-- **`BackSim`'s refuting pole**: relating every pair of states is not a backward simulation
(it would have to rename a running control into a refused one). Its satisfying poles are
`forcesSim`, `relatedSim` and `settleSim`. -/
theorem not_backSim_everything : ¬ BackSim (fun _ _ _ => True) (fun _ _ => True) := by
  intro sim
  have renamed := (sim.renames (F := id) (s := initial (.nat 0))
    (t := ⟨#[], .refused .unbound, []⟩) trivial).1
  simp [renameControl, initial] at renamed


/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/Converse.lean` -/
/-! ## Settling is a backward simulation -/

theorem settle_exec {s t : State} (agree : Agree s t) : ∀ n, Agree (exec n s) (exec n t) := by
  intro n
  induction n with
  | zero => exact agree
  | succ n ih => rw [exec_succ, exec_succ]; exact Obend.Core.Collect.agree_stepRaw ih

theorem renameControl_idMap (c : Control) : renameControl id c = c := renameControl_id (f := id) (fun _ _ => rfl)

theorem renameStack_idMap (S : List Frame) : S.map (renameFrame id) = S :=
  renameStack_id (f := id) (fun _ _ _ _ => rfl)

/-- **Settling (origins erased) is a backward simulation**: exact lockstep, identity map. -/
public theorem settleSim : BackSim (fun F s t => F = id ∧ Agree s t) (fun _ _ => True) where
  renames h := by
    obtain ⟨rfl, a⟩ := h
    exact ⟨by rw [renameControl_idMap]; exact a.control.symm, by rw [renameStack_idMap]; exact a.stack.symm⟩
  controlIn _ := fun _ _ => trivial
  stackIn _ := fun _ _ _ _ => trivial
  reenter c S h _ _ := by
    obtain ⟨rfl, a⟩ := h
    refine ⟨rfl, Agree.mk' a.heap ?_ ?_⟩
    · exact (renameControl_idMap c).symm
    · exact (renameStack_idMap S).symm
  back h halts := by
    obtain ⟨rfl, a⟩ := h
    have all := settle_exec a
    refine ⟨_, id, ⟨fun j lt => ?_, ?_⟩, ⟨rfl, all _⟩, fun _ _ => ⟨trivial, rfl⟩⟩
    · have := halts.1 j lt; rwa [← (all j).control] at this
    · have := halts.2; rwa [← (all _).control] at this


/-- **A backward simulation's segment, as endings**: whatever the forced side ends with, the
lazy side ends with above a threshold, stopping in a related state. -/
public theorem BackSim.ends {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    {budget' : Budget} {e : Ending} {y' : State} (ran : endsWith L' T' budget' t = some (e, y')) :
    ∃ y F', R F' y y' ∧ EndsAbove s budget' e y := by
  unfold endsWith at ran
  have notSusp : ∀ r st, Obend.Core.Machine.runBounded L' T' t ≠ .suspended r st := by
    intro r st h; rw [h] at ran; cases ran
  obtain ⟨n, n', L1, F1, rel1, eqT, _, lazy⟩ := sim.runBounded rel notSusp
  have ctl := (sim.renames rel1).1
  rw [eqT] at ran
  cases hc : (exec n s).control with
  | yielded p =>
    rw [hc] at ctl
    simp only [Obend.Core.Machine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i r' found
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨L2, E0, st, F2, _, _, extract⟩ := sim.yieldedPlan rel1 found
      refine ⟨exec n s, F1, rel1, limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      have ext := extract L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [endsWith, run, Obend.Core.Machine.runBounded, hc, ext]
    · cases ran
  | complete v =>
    rw [hc] at ctl
    simp only [Obend.Core.Machine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i r' found
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨L2, E0, st, F2, _, _, extract⟩ := sim.complete rel1 found
      refine ⟨exec n s, F1, rel1, limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      have ext := extract L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [endsWith, run, Obend.Core.Machine.runBounded, hc, ext]
    · cases ran
  | blackhole a =>
    rw [hc] at ctl
    simp only [Obend.Core.Machine.runBounded, ctl, renameControl, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    refine ⟨exec n s, F1, rel1, L1, n, 0, fun L T k le nle => ?_⟩
    simp [endsWith, lazy L T le nle, Obend.Core.Machine.runBounded, hc]
  | refused r =>
    rw [hc] at ctl
    simp only [Obend.Core.Machine.runBounded, ctl, renameControl, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    refine ⟨exec n s, F1, rel1, L1, n, 0, fun L T k le nle => ?_⟩
    simp [endsWith, lazy L T le nle, Obend.Core.Machine.runBounded, hc]
  | evaluate _ _ | enter _ | returned _ =>
    rw [hc] at ctl
    simp [Obend.Core.Machine.runBounded, ctl, renameControl] at ran

/-! ## Chains of normalizations -/

/-- **A chain** from a lazy state to a normalized one: forcing (`ForcesBy`), settling
(`Agree`) and collection (`Related`) steps, composed. A kernel checkpoint is in a chain
with the yield it was made from (`chain_checkpoint`). -/
public inductive Chain : State → State → Prop where
  | forces {gap : Nat} {F : Nat → Nat} {s t : State} : ForcesBy gap F s t → Chain s t
  | settles {s t : State} : Agree s t → Chain s t
  | collects {f : Nat → Nat} {D : Nat → Prop} {s t : State} : Related f D s t → Chain s t
  | trans {s m t : State} : Chain s m → Chain m t → Chain s t

/-- **The converse, along a chain: the difference is resources only.** Whatever segment the
normalized state ends with (under some resources), the lazy state ends with the SAME ending
under every resource vector above a threshold, with the same output nodes and bytes, and
stops in a state in a chain with the normalized one's. -/
public theorem Chain.back {s t : State} (h : Chain s t) :
    ∀ {L' : Limits} {T' : Nat} {budget' : Budget} {e : Ending} {y' : State},
      endsWith L' T' budget' t = some (e, y') → ∃ y, Chain y y' ∧ EndsAbove s budget' e y := by
  induction h with
  | forces r =>
    intro L' T' budget' e y' ran
    obtain ⟨y, _, rel, above⟩ := (forcesSim _).ends r ran
    exact ⟨y, .forces rel, above⟩
  | settles a =>
    intro L' T' budget' e y' ran
    obtain ⟨y, _, rel, above⟩ := settleSim.ends ⟨rfl, a⟩ ran
    exact ⟨y, .settles rel.2, above⟩
  | @collects f D _ _ r =>
    intro L' T' budget' e y' ran
    obtain ⟨y, _, rel, above⟩ := (relatedSim f D).ends ⟨rfl, r⟩ ran
    exact ⟨y, .collects rel.2, above⟩
  | trans _ _ ih1 ih2 =>
    intro L' T' budget' e y' ran
    obtain ⟨ym, cm, L0, T0, E0, above⟩ := ih2 ran
    obtain ⟨y, cs, above'⟩ := ih1 (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
    exact ⟨y, .trans cs cm, above'⟩

/-- **Every response resumes a chain to a chain** (the response captures no address). -/
public theorem Chain.resume {s t : State} (h : Chain s t) (response : Term) :
    ∀ {s0 : State}, Obend.Core.Machine.resume response s = some s0 →
      ∃ t0, Obend.Core.Machine.resume response t = some t0 ∧ Chain s0 t0 := by
  induction h with
  | @forces gap F s t r =>
    intro s0 resumed
    obtain ⟨plan, yielded⟩ := resume_requires_yield response s (by rw [resumed]; rfl)
    have ctlT : t.control = .yielded (F plan) := by rw [r.renames.1, yielded]; rfl
    simp only [Obend.Core.Machine.resume, yielded, Option.some.injEq] at resumed
    subst resumed
    refine ⟨⟨t.heap, .evaluate response [], t.stack⟩, by simp [Obend.Core.Machine.resume, ctlT], ?_⟩
    have := r.reenter (.evaluate response []) s.stack (fun _ m => by cases m) r.lazyValid.stack
    rw [← r.renames.2] at this
    exact .forces this
  | settles a =>
    intro s0 resumed
    obtain ⟨t0, again, a0⟩ := agree_resume a response resumed
    exact ⟨t0, again, .settles a0⟩
  | collects r =>
    intro s0 resumed
    obtain ⟨t0, again, r0⟩ := related_resume r response resumed
    exact ⟨t0, again, .collects r0⟩
  | trans _ _ ih1 ih2 =>
    intro s0 resumed
    obtain ⟨m0, againM, c1⟩ := ih1 resumed
    obtain ⟨t0, againT, c2⟩ := ih2 againM
    exact ⟨t0, againT, .trans c1 c2⟩

/-- **A checkpoint is in a chain with its yield**: the Plan extraction forces (`yieldedPlan_forces`),
settling erases origins, collection renames. -/
theorem chain_checkpoint {L : Limits} {budget : Budget} {y : State} {r : Result} (valid : AddrValid y)
    (found : Obend.Core.Data.yieldedPlan L budget y = .ok r) : Chain y (checkpoint r.state) := by
  obtain ⟨F, forces⟩ := yieldedPlan_forces valid found y.control valid.control
  obtain ⟨sameControl, sameStack⟩ := yieldedPlanWith_control found
  have eq : (⟨r.state.heap, y.control, y.stack⟩ : State) = r.state := by
    rw [← sameControl, ← sameStack]
  rw [eq] at forces
  exact .trans (.forces forces) (.trans (.settles (agree_settle r.state)) (.collects (related_collect (settle r.state))))


/-- **Silent divergence is never a visible ending**: if the lazy run never halts, the
normalized run ends no segment, under any resources. -/
public theorem Chain.spins {s t : State} (h : Chain s t) (spins : ∀ n, ¬ Halts s n) (L : Limits) (T : Nat)
    (budget : Budget) : endsWith L T budget t = none := by
  cases ran : endsWith L T budget t with
  | none => rfl
  | some ending =>
    obtain ⟨e, y'⟩ := ending
    obtain ⟨y, _, L0, T0, E0, above⟩ := h.back ran
    obtain ⟨n, halts⟩ := halts_of_endsWith (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
    exact absurd halts (spins n)

/-- **The continuation states after equal next Plans.** If the normalized state yields Plan
`d` and the kernel stores the checkpoint of that yield's extraction, the lazy state yields the
same `d` above a threshold, and the lazy state's OWN yield is in a chain with the stored
checkpoint: so every later response resumes them to a chain again (`Chain.resume`). -/
public theorem Chain.next {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {budget' : Budget} {d : Data}
    {y' : State} (ran : endsWith L' T' budget' t = some (.yielded d, y')) (valid : AddrValid y') {r' : Result}
    (found : Obend.Core.Data.yieldedPlan L' budget' y' = .ok r') :
    ∃ y, EndsAbove s budget' (.yielded d) y ∧ Chain y (checkpoint r'.state) := by
  obtain ⟨y, c, above⟩ := h.back ran
  exact ⟨y, above, .trans c (chain_checkpoint valid found)⟩

/-- A chain renames the control. -/
public theorem Chain.control {s t : State} (h : Chain s t) : ∃ G, t.control = renameControl G s.control := by
  induction h with
  | forces r => exact ⟨_, r.renames.1⟩
  | settles a => exact ⟨id, by rw [renameControl_idMap]; exact a.control.symm⟩
  | collects r => exact ⟨_, r.control⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨G1, e1⟩ := ih1
    obtain ⟨G2, e2⟩ := ih2
    exact ⟨G2 ∘ G1, by rw [e2, e1, renameControl_comp]⟩

/-- **A response the normalized state accepts, the lazy state accepts**, to a chain. -/
public theorem Chain.resume_back {s t : State} (h : Chain s t) (response : Term) {t0 : State}
    (resumed : Obend.Core.Machine.resume response t = some t0) :
    ∃ s0, Obend.Core.Machine.resume response s = some s0 ∧ Chain s0 t0 := by
  obtain ⟨plan, yielded⟩ := resume_requires_yield response t (by rw [resumed]; rfl)
  obtain ⟨G, ctl⟩ := h.control
  have sYield : ∃ p, s.control = .yielded p := by
    rw [yielded] at ctl
    cases hc : s.control <;> rw [hc] at ctl <;> simp [renameControl] at ctl
    exact ⟨_, rfl⟩
  obtain ⟨p, sp⟩ := sYield
  have sResumed : Obend.Core.Machine.resume response s = some ⟨s.heap, .evaluate response [], s.stack⟩ := by
    simp [Obend.Core.Machine.resume, sp]
  obtain ⟨t1, again, chain⟩ := h.resume response sResumed
  rw [resumed] at again
  cases again
  exact ⟨_, sResumed, chain⟩


end Obend.Core.Proofs.Forcing

namespace Obend.Core.Interaction
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Collect
open Obend.Core.Data
open Obend.Core.Proofs.Forcing
set_option autoImplicit false

/-! ## The machine against the reference -/

/-- **What a normalized state commits is the reference node** of the lazy state in a chain
with it: under ANY resources, an ending of the normalized state is the lazy state's node. -/
public theorem node_of_chain {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {b : Budget} {e : Ending}
    {y' : State} (ran : endsWith L' T' b t = some (e, y')) :
    node b s = Node.ofEnding e ∧ ∃ y, ending b s = some (e, y) ∧ Chain y y' := by
  obtain ⟨y, c, above⟩ := h.back ran
  exact ⟨node_of_above above, y, ending_of_above above, c⟩

/-- **The machine/reference yield theorem.** A normalized state yields Plan `d` (under any
resources) and the kernel stores the checkpoint of that yield's extraction. Then the
reference node is `Vis(d, k)`, and for EVERY response `r` the kernel accepts, resuming the
stored checkpoint corresponds to `k r` (they are in a chain: every later ending agrees,
resources only, and spinning is preserved). -/
public theorem node_of_chain_vis {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {b : Budget} {d : Data}
    {y' : State} (ran : endsWith L' T' b t = some (.yielded d, y')) (valid : AddrValid y') {r' : Result}
    (found : Obend.Core.Data.yieldedPlan L' b y' = .ok r') :
    node b s = .vis d ∧ ∀ (response : Term) (stored : State),
      resume response (checkpoint r'.state) = some stored →
      ∃ next, continuation b s response = some next ∧ Chain next stored := by
  obtain ⟨y, above, chain⟩ := h.next ran valid found
  refine ⟨node_of_above above, fun response stored resumed => ?_⟩
  obtain ⟨next, again, c⟩ := chain.resume_back response resumed
  refine ⟨next, ?_, c⟩
  unfold continuation
  rw [ending_of_above above]
  exact again

/-- **Spinning is never a visible ending**: if the reference spins, the normalized state ends
no segment under any resources. -/
public theorem chain_spin {s t : State} (h : Chain s t) {b : Budget} (spin : node b s = .spin) (L : Limits) (T : Nat)
    (b' : Budget) : endsWith L T b' t = none :=
  h.spins ((node_spin_iff b s).mp spin) L T b'


end Obend.Core.Interaction

namespace Obend.Core.Proofs.Forcing
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Collect
open Obend.Core.Data
open Obend.Core.Invariant
set_option autoImplicit false

/-! ## Consolidated from `lean/Obend/Core/Proofs/Forcing/BackFail.lean` -/

/-- The failure an extraction throws for a forcing outcome (`none`: it finished). -/
public def failureOf : Outcome → Option Failure
  | .finished _ _ => none
  | .suspended reason _ => some (suspensionFailure reason)
  | .divergent _ _ => some .divergent
  | .refused _ _ => some .refused
  | .yielded _ _ => some .yielded

@[simp] public theorem suspensionFailure_ne_divergent (reason : Suspension) :
    suspensionFailure reason ≠ .divergent := by cases reason <;> simp [suspensionFailure]

@[simp] public theorem suspensionFailure_ne_refused (reason : Suspension) :
    suspensionFailure reason ≠ .refused := by cases reason <;> simp [suspensionFailure]

@[simp] public theorem suspensionFailure_ne_yielded (reason : Suspension) :
    suspensionFailure reason ≠ .yielded := by cases reason <;> simp [suspensionFailure]

/-- A terminal outcome's failure depends only on the control, up to renaming. -/
theorem failureOf_rename {L L' : Limits} {x y : State} {G : Nat → Nat}
    (ctl : y.control = renameControl G x.control) :
    failureOf (Obend.Core.Machine.runBounded L 0 x) = failureOf (Obend.Core.Machine.runBounded L' 0 y) := by
  cases hc : x.control <;> rw [hc] at ctl <;>
    simp [Obend.Core.Machine.runBounded, hc, ctl, renameControl, failureOf]

/-- **A forcing that fails, backward.** A forced forcing whose outcome is a failure other
than `suspended` has a lazy forcing with the same failure above a threshold. -/
theorem BackSim.forceFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    {f : Failure} (fails : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' T' t).1 = some f) (semantic : f ≠ .suspended ∧ f ≠ .tickExhausted) :
    ∃ (L0 : Limits) (n : Nat), ∀ (L : Limits) (T : Nat), LimitsLe L0 L → n ≤ T →
      failureOf (Obend.Core.Data.forceWith (fun _ => true) L T s).1 = some f := by
  rw [Obend.Core.Proofs.DataSoundness.forceWith_unrestricted] at fails
  have notSusp : ∀ r st, Obend.Core.Machine.runBounded L' T' t ≠ .suspended r st := by
    intro r st h
    rw [h] at fails
    cases r with
    | ticks => simp [failureOf, suspensionFailure] at fails; exact semantic.2 fails.symm
    | capacity => simp [failureOf, suspensionFailure] at fails; exact semantic.1 fails.symm
  obtain ⟨n, n', L0, F', rel', eqT, _, lazy⟩ := sim.runBounded rel notSusp
  have ctl := (sim.renames rel').1
  refine ⟨L0, n, fun L T le nle => ?_⟩
  rw [Obend.Core.Proofs.DataSoundness.forceWith_unrestricted, lazy L T le nle, failureOf_rename ctl (L' := L'),
    ← eqT]
  exact fails

theorem except_map_error {ε α β : Type} (g : α → β) (x : Except ε α) (e : ε) :
    (g <$> x) = .error e ↔ x = .error e := by
  cases x <;> simp [Functor.map, Except.map]

theorem except_bind_error {ε α β : Type} (x : Except ε α) (k : α → Except ε β) (e : ε) :
    (x >>= k) = .error e ↔ x = .error e ∨ ∃ a, x = .ok a ∧ k a = .error e := by
  cases x <;> simp [bind, Except.bind]

/-- Materialization failure backward at one depth. -/
public def MaterializeFailBack (R : (Nat → Nat) → State → State → Prop) (Dom : Array Cell → Nat → Prop)
    (L' : Limits) (depth : Nat) : Prop :=
  ∀ (budget' : Budget) (v : RuntimeValue) (s t : State) (F : Nat → Nat) (f : Failure) (st' : State × Budget),
    R F s t → AllIn (Dom s.heap) (valueAddresses v) → (f ≠ .suspended ∧ f ≠ .tickExhausted) →
    materializeWith (fun _ => true) L' depth budget' (renameValue F v) t = .error (f, st') →
    ∃ (L0 : Limits) (T0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
      ∃ st, materializeWith (fun _ => true) L depth ⟨budget'.nodes, T0 + k, budget'.bytes⟩ v s = .error (f, st)

/-- **The record fold's failure, backward.** -/
theorem BackSim.foldFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {L' : Limits} {depth : Nat} (ih : MaterializeFailBack R Dom L' depth) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (s t : State) (b' : Budget)
      (F : Nat → Nat) (f : Failure) (st' : State × Budget),
      R F s t → AllIn (Dom s.heap) (fields.map Prod.snd) → (f ≠ .suspended ∧ f ≠ .tickExhausted) →
      (fields.map fun field => (field.1, F field.2)).foldlM (recordStep (fun _ => true) L' depth)
        (acc, t, b') = .error (f, st') →
      ∃ (L0 : Limits) (T0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        ∃ st, fields.foldlM (recordStep (fun _ => true) L depth) (acc, s, ⟨b'.nodes, T0 + k, b'.bytes⟩) =
          .error (f, st) := by
  intro fields
  induction fields with
  | nil =>
    intro acc s t b' F f st' _ _ _ folded
    simp [List.foldlM, pure, Except.pure] at folded
  | cons field rest ihf =>
    intro acc s t b' F f st' rel inside semantic folded
    simp only [List.map_cons, List.foldlM_cons, except_bind_error] at folded
    have fieldIn : Dom s.heap field.2 := inside field.2 (by simp)
    obtain ⟨nodes, ticks', bytes⟩ := b'
    have entered := sim.reenter (.enter field.2) [] rel (by simpa [controlAddresses] using fieldIn)
      (fun _ m => by cases m)
    rcases folded with first' | ⟨mid', first', restFolded⟩
    · simp [recordStep] at first'
      split at first'
      · rename_i cond
        change Except.error _ = Except.error _ at first'
        simp only [Except.error.injEq, Prod.mk.injEq] at first'
        obtain ⟨rfl, -⟩ := first'
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [List.foldlM_cons, recordStep, cond] <;> rfl⟩⟩
      · rename_i cond
        cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F field.2), []⟩ with
        | mk outcome rest' =>
        rw [forced] at first'
        cases outcome with
        | finished value' retained' =>
          rw [except_map_error] at first'
          obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
          subst vEq
          obtain ⟨L2, T2, child⟩ := ih _ v _ _ F1 f st' rel1 vIn semantic first'
          refine ⟨limitsMax L1 L2, n + T2, fun L k le => ?_⟩
          have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
          rw [show n + T2 + k - n = T2 + k by omega] at runL
          obtain ⟨st, childL⟩ := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
          exact ⟨st, by simp [List.foldlM_cons, except_bind_error, except_map_error, recordStep, cond, runL, childL]⟩
        | suspended reason _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          cases reason with
          | ticks => exact absurd first'.1.symm semantic.2
          | capacity => exact absurd first'.1.symm semantic.1
        | divergent _ _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          obtain ⟨rfl, -⟩ := first'
          have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
              ⟨t.heap, .enter (F field.2), []⟩).1 = some .divergent := by rw [forced]; rfl
          obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
          refine ⟨L1, n, fun L k le => ?_⟩
          have lz := lazy L (n + k) le (by omega)
          cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter field.2, []⟩ with
          | mk o r =>
            rw [lf] at lz
            cases o <;> simp [failureOf] at lz <;>
              exact ⟨_, by simp [List.foldlM_cons, except_bind_error, recordStep, cond, lf] <;> rfl⟩
        | refused _ _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          obtain ⟨rfl, -⟩ := first'
          have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
              ⟨t.heap, .enter (F field.2), []⟩).1 = some .refused := by rw [forced]; rfl
          obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
          refine ⟨L1, n, fun L k le => ?_⟩
          have lz := lazy L (n + k) le (by omega)
          cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter field.2, []⟩ with
          | mk o r =>
            rw [lf] at lz
            cases o <;> simp [failureOf] at lz <;>
              exact ⟨_, by simp [List.foldlM_cons, except_bind_error, recordStep, cond, lf] <;> rfl⟩
        | yielded _ _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          obtain ⟨rfl, -⟩ := first'
          have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
              ⟨t.heap, .enter (F field.2), []⟩).1 = some .yielded := by rw [forced]; rfl
          obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
          refine ⟨L1, n, fun L k le => ?_⟩
          have lz := lazy L (n + k) le (by omega)
          cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter field.2, []⟩ with
          | mk o r =>
            rw [lf] at lz
            cases o <;> simp [failureOf] at lz <;>
              exact ⟨_, by simp [List.foldlM_cons, except_bind_error, recordStep, cond, lf] <;> rfl⟩
    · simp [recordStep] at first'
      split at first'
      · simp at first'
      · rename_i cond
        cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F field.2), []⟩ with
        | mk outcome rest' =>
          rw [forced] at first'
          cases outcome with
          | finished value' retained' =>
            simp at first'
            obtain ⟨a', materialized, rfl⟩ := first'
            obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
            subst vEq
            obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := sim.materialize L' _ _ v _ _ F1 a' rel1 vIn materialized
            have restIn : AllIn (Dom st2.heap) (rest.map Prod.snd) := fun x m =>
              (ext2 x (ext1 x (inside x (by simp at m ⊢; exact Or.inr m))).1).1
            have restMap : rest.map (fun field => (field.1, F field.2)) =
                rest.map (fun field => (field.1, F2 field.2)) := by
              apply List.map_congr_left
              intro fld m
              have dx : Dom s.heap fld.2 := inside fld.2 (by simp; exact Or.inr ⟨fld.1, m⟩)
              rw [(ext2 _ (ext1 _ dx).1).2, (ext1 _ dx).2]
            rw [restMap] at restFolded
            obtain ⟨L3, T3, tail⟩ := ihf _ st2 _ _ F2 f st' rel2 restIn semantic restFolded
            refine ⟨limitsMax L1 (limitsMax L2 L3), n + (T2 + T3), fun L k le => ?_⟩
            have le1 := limitsLe_trans (limitsLe_max_left _ _) le
            have le2 := limitsLe_trans (limitsLe_trans (limitsLe_max_left _ _) (limitsLe_max_right _ _)) le
            have le3 := limitsLe_trans (limitsLe_trans (limitsLe_max_right _ _) (limitsLe_max_right _ _)) le
            have runL := above L (n + (T2 + T3) + k) le1 (by omega)
            rw [show n + (T2 + T3) + k - n = T2 + (T3 + k) by omega] at runL
            have childL := child L (T3 + k) le2
            obtain ⟨st, tailL⟩ := tail L k le3
            refine ⟨st, ?_⟩
            simp only [List.foldlM_cons, except_bind_error]
            refine .inr ⟨((field.1, a'.value) :: acc, st2, ⟨a'.remaining.nodes, T3 + k, a'.remaining.bytes⟩), ?_, tailL⟩
            simp [recordStep, cond, runL, childL]
          | _ => simp at first'

theorem BackSim.materializeFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) (L' : Limits) : ∀ depth, MaterializeFailBack R Dom L' depth := by
  intro depth
  induction depth with
  | zero =>
    intro budget' v s t F f st' _ _ _ found
    simp [materializeWith] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith] <;> rfl⟩⟩
  | succ depth ih =>
    intro budget' v s t F f st' rel valueIn semantic found
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases v with
    | natural m =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          simp at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · cases found
    | boolean b =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          simp at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · cases found
    | label l =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          simp at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · cases found
    | closure body environment =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
    | specification metadata extension =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
    | prototype spec target =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
    | variant label payload =>
      have payloadIn : Dom s.heap payload := valueIn payload (by simp [valueAddresses])
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          change Except.error _ = Except.error _ at found
          simp only [Except.error.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · rename_i c2
          have entered := sim.reenter (.enter payload) [] rel (by simpa [controlAddresses] using payloadIn)
            (fun _ m => by cases m)
          cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F payload), []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value' retained' =>
              simp only [except_map_error] at found
              obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
              subst vEq
              obtain ⟨L2, T2, child⟩ := ih _ v _ _ F1 f st' rel1 vIn semantic found
              refine ⟨limitsMax L1 L2, n + T2, fun L k le => ?_⟩
              have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
              rw [show n + T2 + k - n = T2 + k by omega] at runL
              obtain ⟨st, childL⟩ := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
              exact ⟨st, by simp [materializeWith, c1, c2, runL, except_map_error, childL]⟩
            | suspended reason _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              cases reason with
              | ticks => exact absurd found.1.symm semantic.2
              | capacity => exact absurd found.1.symm semantic.1
            | divergent _ _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
                  ⟨t.heap, .enter (F payload), []⟩).1 = some .divergent := by rw [forced]; rfl
              obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
              refine ⟨L1, n, fun L k le => ?_⟩
              have lz := lazy L (n + k) le (by omega)
              cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter payload, []⟩ with
              | mk o r =>
                rw [lf] at lz
                cases o <;> simp [failureOf] at lz <;>
                  exact ⟨_, by simp [materializeWith, c1, c2, lf] <;> rfl⟩
            | refused _ _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
                  ⟨t.heap, .enter (F payload), []⟩).1 = some .refused := by rw [forced]; rfl
              obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
              refine ⟨L1, n, fun L k le => ?_⟩
              have lz := lazy L (n + k) le (by omega)
              cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter payload, []⟩ with
              | mk o r =>
                rw [lf] at lz
                cases o <;> simp [failureOf] at lz <;>
                  exact ⟨_, by simp [materializeWith, c1, c2, lf] <;> rfl⟩
            | yielded _ _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
                  ⟨t.heap, .enter (F payload), []⟩).1 = some .yielded := by rw [forced]; rfl
              obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
              refine ⟨L1, n, fun L k le => ?_⟩
              have lz := lazy L (n + k) le (by omega)
              cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter payload, []⟩ with
              | mk o r =>
                rw [lf] at lz
                cases o <;> simp [failureOf] at lz <;>
                  exact ⟨_, by simp [materializeWith, c1, c2, lf] <;> rfl⟩
    | record fields =>
      have fieldsIn : AllIn (Dom s.heap) (fields.map Prod.snd) := valueIn
      simp only [renameValue] at found
      simp [materializeWith_record] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          change Except.error _ = Except.error _ at found
          simp only [Except.error.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1, c2] <;> rfl⟩⟩
        · rename_i c2
          split at found
          · rename_i c3
            have c3' : (fields.map Prod.fst).eraseDups.length = fields.length := by
              simpa [Function.comp_def] using c3
            split at found
            · rename_i c4
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1, c2, c3', c4] <;> rfl⟩⟩
            · rename_i c4
              rw [except_map_error] at found
              obtain ⟨L0, T0, fold⟩ := sim.foldFail ih fields [] s t _ F f st' rel fieldsIn semantic found
              refine ⟨L0, T0, fun L k le => ?_⟩
              obtain ⟨st, foldL⟩ := fold L k le
              exact ⟨st, by simp [materializeWith_record, c1, c2, c3', c4, foldL, except_map_error]⟩
          · rename_i c3
            have c3' : ¬ (fields.map Prod.fst).eraseDups.length = fields.length := by
              simpa [Function.comp_def] using c3
            change Except.error _ = Except.error _ at found
            simp only [Except.error.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, -⟩ := found
            exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1, c2, c3'] <;> rfl⟩⟩

/-- **Plan extraction's failure, backward**: a forced yield whose Plan extraction fails with
a failure other than `suspended` or `tickExhausted` has a lazy yield whose extraction fails with the same
failure above a threshold, with the same output nodes and bytes. -/
theorem BackSim.yieldedPlanFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {f : Failure} {st' : State × Budget} (found : Obend.Core.Data.yieldedPlan L' budget' y' = .error (f, st'))
    (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    ∃ (L0 : Limits) (E0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
      ∃ st, Obend.Core.Data.yieldedPlan L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y = .error (f, st) := by
  obtain ⟨ctlEq, _⟩ := sim.renames rel
  have cIn := sim.controlIn rel
  unfold Obend.Core.Data.yieldedPlan yieldedPlanWith at found ⊢
  cases hc : y.control with
  | yielded plan =>
    rw [ctlEq, hc] at found
    rw [hc] at cIn
    simp only [renameControl] at found
    have planIn : Dom y.heap plan := cIn plan (by simp [controlAddresses])
    have entered := sim.reenter (.enter plan) [] rel (by simpa [controlAddresses] using planIn) (fun _ m => by cases m)
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases forced : Obend.Core.Data.forceWith (fun _ => true) L' ticks' ⟨y'.heap, .enter (F plan), []⟩ with
    | mk outcome rest =>
      simp only at found
      rw [forced] at found
      cases outcome with
      | finished value' retained' =>
        simp only [except_bind_error] at found
        rcases found with childFail | ⟨_, _, bad⟩
        · obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
          subst vEq
          obtain ⟨L2, T2, child⟩ := sim.materializeFail L' _ _ v _ _ F1 f st' rel1 vIn semantic childFail
          refine ⟨limitsMax L1 L2, n + T2, fun L k le => ?_⟩
          have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
          rw [show n + T2 + k - n = T2 + k by omega] at runL
          obtain ⟨st, childL⟩ := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
          exact ⟨st, by simp [runL, childL] <;> rfl⟩
        · cases bad
      | suspended reason _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        cases reason with
        | ticks => exact absurd found.1.symm semantic.2
        | capacity => exact absurd found.1.symm semantic.1
      | divergent _ _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
            ⟨y'.heap, .enter (F plan), []⟩).1 = some .divergent := by rw [forced]; rfl
        obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
        refine ⟨L1, n, fun L k le => ?_⟩
        have lz := lazy L (n + k) le (by omega)
        cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨y.heap, .enter plan, []⟩ with
        | mk o r =>
          rw [lf] at lz
          cases o <;> simp [failureOf] at lz <;>
            exact ⟨_, by simp [hc, lf] <;> rfl⟩
      | refused _ _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
            ⟨y'.heap, .enter (F plan), []⟩).1 = some .refused := by rw [forced]; rfl
        obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
        refine ⟨L1, n, fun L k le => ?_⟩
        have lz := lazy L (n + k) le (by omega)
        cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨y.heap, .enter plan, []⟩ with
        | mk o r =>
          rw [lf] at lz
          cases o <;> simp [failureOf] at lz <;>
            exact ⟨_, by simp [hc, lf] <;> rfl⟩
      | yielded _ _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        have fail : failureOf (Obend.Core.Data.forceWith (fun _ => true) L' ticks'
            ⟨y'.heap, .enter (F plan), []⟩).1 = some .yielded := by rw [forced]; rfl
        obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
        refine ⟨L1, n, fun L k le => ?_⟩
        have lz := lazy L (n + k) le (by omega)
        cases lf : Obend.Core.Data.forceWith (fun _ => true) L (n + k) ⟨y.heap, .enter plan, []⟩ with
        | mk o r =>
          rw [lf] at lz
          cases o <;> simp [failureOf] at lz <;>
            exact ⟨_, by simp [hc, lf] <;> rfl⟩
  | _ =>
    rw [ctlEq, hc] at found
    simp only [renameControl] at found
    change Except.error _ = Except.error _ at found
    simp only [Except.error.injEq, Prod.mk.injEq] at found
    exact absurd found.1.symm semantic.1

/-- **Completion's failure, backward.** -/
theorem BackSim.completeFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {f : Failure} {st' : State × Budget} (found : Obend.Core.Data.complete L' budget' y' = .error (f, st'))
    (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    ∃ (L0 : Limits) (E0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
      ∃ st, Obend.Core.Data.complete L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y = .error (f, st) := by
  obtain ⟨ctlEq, stEq⟩ := sim.renames rel
  have cIn := sim.controlIn rel
  unfold Obend.Core.Data.complete completeWith at found ⊢
  obtain ⟨nodes, ticks', bytes⟩ := budget'
  cases hc : y.control with
  | complete v =>
    cases hs : y.stack with
    | nil =>
      rw [ctlEq, stEq, hc, hs] at found
      rw [hc] at cIn
      simp only [renameControl, List.map_nil] at found
      simp at found
      rw [except_bind_error] at found
      rcases found with mFail | ⟨a', materialized, rest⟩
      · obtain ⟨L0, T0, m⟩ := sim.materializeFail L' nodes ⟨nodes, ticks', bytes⟩ v y y' F f st' rel cIn semantic mFail
        refine ⟨L0, T0, fun L k le => ?_⟩
        obtain ⟨st, mL⟩ := m L k le
        exact ⟨st, by simp [hc, hs, mL, bind, Except.bind]⟩
      · obtain ⟨L0, T0, st, F', rel', ext', child⟩ := sim.materialize L' _ _ v _ _ F a' rel cIn materialized
        refine ⟨L0, T0, fun L k le => ?_⟩
        have childL := child L k le
        split at rest
        · rename_i encodedBytes encodedAt
          split at rest
          · rename_i big
            change Except.error _ = Except.error _ at rest
            simp only [Except.error.injEq, Prod.mk.injEq] at rest
            obtain ⟨rfl, -⟩ := rest
            exact ⟨(st, _), by simp [hc, hs, childL, encodedAt, big, bind, Except.bind] <;> rfl⟩
          · cases rest
        · rename_i noEnc
          change Except.error _ = Except.error _ at rest
          simp only [Except.error.injEq, Prod.mk.injEq] at rest
          obtain ⟨rfl, -⟩ := rest
          cases enc : encoded nodes a'.value with
          | some b => exact absurd enc (noEnc b)
          | none => exact ⟨(st, _), by simp [hc, hs, childL, enc, bind, Except.bind] <;> rfl⟩
    | cons fr rest =>
      rw [ctlEq, stEq, hc, hs] at found
      simp at found
      exact absurd found.1.symm semantic.1
  | _ =>
    rw [ctlEq, hc] at found
    simp [renameControl] at found
    exact absurd found.1.symm semantic.1

/-! ## Segments that end in a failed extraction -/

/-- The extraction failure a segment ends with: its bounded run halted in a yield or a
completion, and that extraction failed (`none`: anything else). -/
public def failsWith (L : Limits) (T : Nat) (budget : Budget) (s : State) : Option Failure :=
  match Obend.Core.Machine.runBounded L T s with
  | .yielded _ y => match Obend.Core.Data.yieldedPlan L budget y with
    | .error (f, _) => some f
    | .ok _ => none
  | .finished _ y => match Obend.Core.Data.complete L budget y with
    | .error (f, _) => some f
    | .ok _ => none
  | _ => none

/-- **A failure above a threshold**: under every resource vector at least `(L0, T0, E0)`, with
the same output nodes and bytes, the segment from `s` ends with extraction failure `f`. -/
public def FailsAbove (s : State) (budget : Budget) (f : Failure) : Prop :=
  ∃ (L0 : Limits) (T0 E0 : Nat), ∀ (L : Limits) (T k : Nat), LimitsLe L0 L → T0 ≤ T →
    failsWith L T ⟨budget.nodes, E0 + k, budget.bytes⟩ s = some f

/-- A segment that ends in a failed extraction halted. -/
theorem failsWith_halts {L : Limits} {T : Nat} {budget : Budget} {s : State} {f : Failure}
    (ran : failsWith L T budget s = some f) : ∃ n, Halts s n := by
  have notSusp : ∀ r st, Obend.Core.Machine.runBounded L T s ≠ .suspended r st := by
    intro r st h; unfold failsWith at ran; rw [h] at ran; cases ran
  obtain ⟨n, _, halts, _, _⟩ := runBounded_halts L T s notSusp
  exact ⟨n, halts⟩

/-- A segment that ends in a failed extraction ends no segment. -/
theorem endsWith_of_failsWith {L : Limits} {T : Nat} {budget : Budget} {s : State} {f : Failure}
    (ran : failsWith L T budget s = some f) : endsWith L T budget s = none := by
  unfold failsWith at ran
  unfold endsWith
  cases hr : Obend.Core.Machine.runBounded L T s with
  | yielded p y =>
    rw [hr] at ran
    simp only at ran ⊢
    cases hp : Obend.Core.Data.yieldedPlan L budget y with
    | ok r => rw [hp] at ran; cases ran
    | error e => try simp [hp]
  | finished v y =>
    rw [hr] at ran
    simp only at ran ⊢
    cases hp : Obend.Core.Data.complete L budget y with
    | ok r => rw [hp] at ran; cases ran
    | error e => try simp [hp]
  | _ => simp only [hr] at ran; cases ran

/-- **A segment's extraction failure, backward.** -/
theorem BackSim.failsBack {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    {budget' : Budget} {f : Failure} (ran : failsWith L' T' budget' t = some f) (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    FailsAbove s budget' f := by
  have notSusp : ∀ r st, Obend.Core.Machine.runBounded L' T' t ≠ .suspended r st := by
    intro r st h; unfold failsWith at ran; rw [h] at ran; cases ran
  obtain ⟨n, n', L1, F1, rel1, eqT, _, lazy⟩ := sim.runBounded rel notSusp
  have ctl := (sim.renames rel1).1
  unfold failsWith at ran
  rw [eqT] at ran
  cases hc : (exec n s).control with
  | yielded p =>
    rw [hc] at ctl
    simp only [Obend.Core.Machine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i f' st' found
      cases ran
      obtain ⟨L2, E0, h⟩ := sim.yieldedPlanFail rel1 found semantic
      refine ⟨limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      obtain ⟨st, ext⟩ := h L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [failsWith, run, Obend.Core.Machine.runBounded, hc, ext]
    · cases ran
  | complete v =>
    rw [hc] at ctl
    simp only [Obend.Core.Machine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i f' st' found
      cases ran
      obtain ⟨L2, E0, h⟩ := sim.completeFail rel1 found semantic
      refine ⟨limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      obtain ⟨st, ext⟩ := h L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [failsWith, run, Obend.Core.Machine.runBounded, hc, ext]
    · cases ran
  | _ =>
    rw [hc] at ctl
    simp [Obend.Core.Machine.runBounded, ctl, renameControl] at ran

/-- **Along a chain: a semantic extraction failure is the lazy state's own.** Whatever
extraction failure other than `suspended` or `tickExhausted` the normalized state's segment ends with (under
some resources), the lazy state's segment ends with the SAME failure under every resource
vector above a threshold, with the same output nodes and bytes. -/
theorem Chain.failsBack {s t : State} (h : Chain s t) :
    ∀ {L' : Limits} {T' : Nat} {budget' : Budget} {f : Failure},
      failsWith L' T' budget' t = some f → (f ≠ .suspended ∧ f ≠ .tickExhausted) → FailsAbove s budget' f := by
  induction h with
  | forces r => exact fun ran semantic => (forcesSim _).failsBack r ran semantic
  | settles a => exact fun ran semantic => settleSim.failsBack ⟨rfl, a⟩ ran semantic
  | @collects f D _ _ r => exact fun ran semantic => (relatedSim f D).failsBack ⟨rfl, r⟩ ran semantic
  | trans _ _ ih1 ih2 =>
    intro L' T' budget' f ran semantic
    obtain ⟨L0, T0, E0, above⟩ := ih2 ran semantic
    exact ih1 (budget' := ⟨budget'.nodes, E0 + 0, budget'.bytes⟩) (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
      semantic

open Obend.Core.Interaction (node ending Node) in
/-- **A semantic extraction failure is the reference's `malformed`.** A normalized state
whose segment ends (under some resources) in a yield or a completion whose extraction fails
with anything but `suspended` or `tickExhausted` is in a chain with a lazy state whose reference node is
`malformed`: it halts, and no resources make its Plan or result Data within the output
sizes. -/
theorem node_malformed_of_chain {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {budget : Budget}
    {f : Failure} (ran : failsWith L' T' budget t = some f) (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    node budget s = .malformed := by
  obtain ⟨L0, T0, E0, fails⟩ := h.failsBack ran semantic
  obtain ⟨n, halts⟩ := failsWith_halts (fails L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
  unfold node
  cases hEnd : ending budget s with
  | some p =>
    exfalso
    unfold ending at hEnd
    split at hEnd
    · rename_i hex
      have spec := Classical.choose_spec hex
      rw [Option.some.injEq] at hEnd
      rw [hEnd] at spec
      obtain ⟨L1, T1, E1, above⟩ := spec
      have a := above (limitsMax L0 L1) (T0 + T1) E0 (limitsLe_max_right _ _) (by omega)
      have c := fails (limitsMax L0 L1) (T0 + T1) E1 (limitsLe_max_left _ _) (by omega)
      rw [Nat.add_comm E0 E1] at c
      rw [endsWith_of_failsWith c] at a
      cases a
    · cases hEnd
  | none =>
    simp only
    rw [if_pos ⟨n, halts⟩]

/-! ## `suspended` is a resource failure -/

/-- A yield whose Plan is one suspended cell. -/
@[expose] public def suspendedYield : State := ⟨#[.suspended ⟨.nat 1, []⟩], .yielded 0, []⟩

@[expose] public def suspendedCheck : Bool :=
  (match Obend.Core.Data.yieldedPlan ⟨8, 8⟩ ⟨8, 0, 64⟩ suspendedYield with
    | .error (.tickExhausted, _) => true
    | _ => false) &&
  (match Obend.Core.Data.yieldedPlan ⟨8, 8⟩ ⟨8, 16, 64⟩ suspendedYield with
    | .ok _ => true
    | .error _ => false)

/- `suspendedCheck_true` and `suspended_is_resource` (tick suspension does not transfer: with no
extraction ticks the Plan extraction fails `tickExhausted`, with 16 it succeeds) are in
`Obend.Core.Teeth.BackFail`, a legacy leaf: `suspendedCheck_true` evaluates `yieldedPlan` by `decide`. -/


end Obend.Core.Proofs.Forcing
