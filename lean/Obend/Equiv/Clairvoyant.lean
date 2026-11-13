module
/- Executable Clairvoyant Call-by-Need Oracle (`evalClairvoyantMinCost`), Eager Call-by-Value
Evaluator (`evalCBV`), and Dead-`let` Elimination Cost Theorems for `Core4`.
Core relational definitions (`Ready`, `CValue`, `Settled`, `Mode`, `Run`, `CV`, `CostAtMost`,
hoisting lemmas, `isSkipped`, `pickMinCost`, `DemandHint`) reside in `Obend.Equiv.Behaviour` and
are re-exported here via `public import Obend.Equiv.Behaviour`. -/
public import Obend.Equiv.Behaviour
public import Obend.Tactic.Tooth
public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false
/-! ## Cost Upper Bound, Skipped-Term Check, Minimum-Cost Branch Selector & Demand Hints -/

/-- The clairvoyant cost of `t` is at most `k`: some derivation costs at most `k`. -/
@[expose] def CostAtMost (t : Term) (k : Nat) : Prop := ∃ v k', CV t v k' ∧ k' ≤ k
/-- Executable check for `t = skipped` (`.hole 0 []`). -/
@[expose] def isSkipped : Term → Bool
  | .hole 0 [] => true
  | _ => false
theorem isSkipped_skipped : isSkipped skipped = true := rfl
theorem isSkipped_sound {t : Term} (h : isSkipped t = true) : t = skipped := by
  cases t with
  | hole n args =>
    cases n with
    | zero => cases args with | nil => rfl | cons _ _ => cases h
    | succ _ => cases h
  | _ => cases h
theorem not_skipped_of_isSkipped_false {t : Term} (h : isSkipped t = false) : t ≠ skipped := by
  intro heq; subst heq; cases h
/-- Pick the minimum-cost result when both branches succeed, or whichever succeeds. -/
@[expose] def pickMinCost : Option (Term × Nat) → Option (Term × Nat) → Option (Term × Nat)
  | some (v1, k1), some (v2, k2) => if k1 ≤ k2 then some (v1, k1) else some (v2, k2)
  | some r1, none => some r1
  | none, some r2 => some r2
  | none, none => none
theorem pickMinCost_inhabited :
    pickMinCost (some (.nat 0, 1)) (some (.nat 0, 2)) = some (.nat 0, 1) := rfl
theorem pickMinCost_sound {P : Term → Nat → Prop} {o1 o2 : Option (Term × Nat)} {v : Term} {k : Nat}
    (h1 : ∀ v1 k1, o1 = some (v1, k1) → P v1 k1)
    (h2 : ∀ v2 k2, o2 = some (v2, k2) → P v2 k2)
    (h : pickMinCost o1 o2 = some (v, k)) : P v k := by
  cases o1 with
  | none =>
    cases o2 with
    | none => cases h
    | some r2 => rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact h2 r2.1 r2.2 rfl
  | some r1 =>
    cases o2 with
    | none => rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact h1 r1.1 r1.2 rfl
    | some r2 =>
      simp only [pickMinCost] at h
      split at h <;> { rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; first | exact h1 _ _ rfl | exact h2 _ _ rfl }
theorem pickMinCost_le_right {o1 : Option (Term × Nat)} {v2 : Term} {k2 : Nat} :
    ∃ v k, pickMinCost o1 (some (v2, k2)) = some (v, k) ∧ k ≤ k2 := by
  cases o1 with
  | none => exact ⟨v2, k2, rfl, Nat.le_refl k2⟩
  | some r1 =>
    simp only [pickMinCost]; split
    · rename_i hle; exact ⟨r1.1, r1.2, rfl, hle⟩
    · exact ⟨v2, k2, rfl, Nat.le_refl k2⟩
theorem pickMinCost_le_left {o2 : Option (Term × Nat)} {v1 : Term} {k1 : Nat} :
    ∃ v k, pickMinCost (some (v1, k1)) o2 = some (v, k) ∧ k ≤ k1 := by
  cases o2 with
  | none => exact ⟨v1, k1, rfl, Nat.le_refl k1⟩
  | some r2 =>
    simp only [pickMinCost]; split
    · exact ⟨v1, k1, rfl, Nat.le_refl k1⟩
    · rename_i hgt; exact ⟨r2.1, r2.2, rfl, by omega⟩
/-! ## Private Proof-Only Binding Soundness Helpers -/

private theorem skipBind_sound (t : Term) :
    Run .bind t (if isSettled t then (t, 0) else (skipped, 1)).1
      (if isSettled t then (t, 0) else (skipped, 1)).2 := by
  split
  · rename_i hs; exact .keep (isSettled_sound t hs)
  · exact .skip t
private theorem evalBind_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (t : Term) :
    let b := if isSettled t then (t, 0)
      else match eval t with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
    Run .bind t b.1 b.2 := by
  dsimp only
  split
  · rename_i hs; exact .keep (isSettled_sound t hs)
  · rename_i hns
    have hnot : ¬ Settled t := fun hs => hns hs.isSettled_eq_true
    split
    · rename_i vt kt ht; exact .eval hnot (heval t vt kt ht)
    · exact .skip t
/-! ## Field, Head, Wave & Knot Clairvoyant Evaluators -/

/-- Evaluate record fields under a fuel-bounded clairvoyant evaluator. -/
@[expose] def evalClairvoyantFields (eval : Term → Option (Term × Nat)) :
    List (String × Term) → Option (List (String × Term) × Nat)
  | [] => some ([], 0)
  | (name, field) :: rest =>
    match evalClairvoyantFields eval rest with
    | none => none
    | some (rest', k2) =>
      if isSettled field then
        some ((name, field) :: rest', 0 + k2 + 1)
      else
        match eval field with
        | some (vf, kf) => some ((name, vf) :: rest', (kf + 1) + k2 + 1)
        | none => some ((name, skipped) :: rest', 1 + k2 + 1)
theorem evalClairvoyantFields_inhabited :
    evalClairvoyantFields (fun _ => none) [] = some ([], 0) := rfl
theorem evalClairvoyantFields_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (fs fs' : List (String × Term)) (k : Nat),
      evalClairvoyantFields eval fs = some (fs', k) →
      Run .fields (.record fs) (.record fs') k
  | [], _, _, h => by
    rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact .nil
  | (_, field) :: rest, _, _, h => by
    simp only [evalClairvoyantFields] at h
    split at h
    · cases h
    · rename_i rest' k2 hrest
      have ih := evalClairvoyantFields_sound heval rest rest' k2 hrest
      split at h
      · rename_i hs
        rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
        exact .cons (.keep (isSettled_sound field hs)) ih
      · rename_i hns
        have hnot : ¬ Settled field := fun hs => hns hs.isSettled_eq_true
        split at h
        · rename_i vf kf hf
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          exact .cons (.eval hnot (heval field vf kf hf)) ih
        · rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          exact .cons (.skip field) ih
/-- Selective record-field binding for demand hints (`some target` or `none`). -/
@[expose] def evalClairvoyantFieldsFor (eval : Term → Option (Term × Nat)) :
    Option String → List (String × Term) → List (String × Term) × Nat
  | _, [] => ([], 0)
  | some target, (name, field) :: rest =>
    if name == target then
      let (field', k1) := if isSettled field then (field, 0)
        else match eval field with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
      let (rest', k2) := evalClairvoyantFieldsFor eval none rest
      ((name, field') :: rest', k1 + k2 + 1)
    else
      let (field', k1) := if isSettled field then (field, 0) else (skipped, 1)
      let (rest', k2) := evalClairvoyantFieldsFor eval (some target) rest
      ((name, field') :: rest', k1 + k2 + 1)
  | none, (name, field) :: rest =>
    let (field', k1) := if isSettled field then (field, 0) else (skipped, 1)
    let (rest', k2) := evalClairvoyantFieldsFor eval none rest
    ((name, field') :: rest', k1 + k2 + 1)
theorem evalClairvoyantFieldsFor_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (optTarget : Option String) (fs : List (String × Term)),
      Run .fields (.record fs)
        (.record (evalClairvoyantFieldsFor eval optTarget fs).1)
        (evalClairvoyantFieldsFor eval optTarget fs).2
  | _, [] => .nil
  | some target, (_, field) :: rest => by
    unfold evalClairvoyantFieldsFor
    split
    · exact .cons (evalBind_sound heval field) (evalClairvoyantFieldsFor_sound heval none rest)
    · exact .cons (skipBind_sound field) (evalClairvoyantFieldsFor_sound heval (some target) rest)
  | none, (_, field) :: rest => by
    unfold evalClairvoyantFieldsFor
    exact .cons (skipBind_sound field) (evalClairvoyantFieldsFor_sound heval none rest)
/-- Settle the template of a `fix` body (`Run .head`). -/
@[expose] def evalClairvoyantHead (eval : Term → Option (Term × Nat)) (fuel : Nat) (t : Term) :
    Option (Term × Nat) :=
  match t with
  | .record fs => if isCValue (.record fs) then some (.record fs, 0) else some (.record fs, 1)
  | .extend i fs =>
    match fuel with
    | 0 => eval (.extend i fs)
    | n + 1 =>
      match evalClairvoyantHead eval n i with
      | some (.record inh, k) => some (.record (extendFields inh fs), k + 1)
      | _ => eval (.extend i fs)
  | .app f a =>
    match fuel with
    | 0 => eval (.app f a)
    | n + 1 =>
      match eval f with
      | some (.lam b, k1) =>
        let bx := if isSettled a then (a, 0)
          else match eval a with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
        match evalClairvoyantHead eval n (instantiate b bx.1) with
        | some (v, k3) => some (v, k1 + bx.2 + k3 + 1)
        | none => eval (.app f a)
      | _ => eval (.app f a)
  | _ => eval t
termination_by fuel
theorem evalClairvoyantHead_inhabited :
    evalClairvoyantHead (fun _ => none) 0 (.record []) = some (.record [], 0) := by
  unfold evalClairvoyantHead; rfl
theorem evalClairvoyantHead_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (fuel : Nat) (t T : Term) (k : Nat),
      evalClairvoyantHead eval fuel t = some (T, k) → Run .head t T k
  | fuel, t, T, k, h => by
    unfold evalClairvoyantHead at h
    split at h
    · rename_i fs
      split at h
      · rename_i hcv
        rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
        exact .headEval (.value (isCValue_sound (.record fs) hcv))
      · rename_i hncv
        rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
        exact .headRecord (not_cvalue_of_isCValue_false (by simpa using hncv))
    · rename_i i fs
      split at h
      · exact .headEval (heval _ T k h)
      · rename_i n
        split at h
        · rename_i inh k1 hi
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          exact .headExtend (evalClairvoyantHead_sound heval n i (.record inh) k1 hi)
        · exact .headEval (heval _ T k h)
    · rename_i f a
      split at h
      · exact .headEval (heval _ T k h)
      · rename_i n
        split at h
        · rename_i b k1 hf
          dsimp only at h
          split at h
          · rename_i v k3 hbody
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .apply (heval f (.lam b) k1 hf) (evalBind_sound heval a)
              (evalClairvoyantHead_sound heval n _ v k3 hbody)
          · exact .headEval (heval _ T k h)
        · exact .headEval (heval _ T k h)
    · exact .headEval (heval t T k h)
termination_by fuel => fuel
/-- Evaluate one wave across all record fields (`Run .wave`). -/
@[expose] def evalClairvoyantWave (eval : Term → Option (Term × Nat)) (optTarget : Option String)
    (S : Term) : List (String × Term) → List (String × Term) → Option (List (String × Term) × Nat)
  | [], [] => some ([], 0)
  | (n, t) :: fs, (n', p) :: ps =>
    if n == n' then
      let shouldEval := match optTarget with | some target => n == target | none => true
      let tSub := t.substitute (single S)
      let cellOpt :=
        if isSettled tSub then some (tSub, 0)
        else if isSkipped p then
          if shouldEval then
            match eval tSub with | some (v, k) => some (v, k + 1) | none => some (skipped, 0)
          else some (skipped, 0)
        else if isSettled p then some (p, 0)
        else none
      match cellOpt, evalClairvoyantWave eval optTarget S fs ps with
      | some (p', k1), some (ps', k2) => some ((n, p') :: ps', k1 + k2)
      | _, _ => none
    else none
  | _, _ => none
theorem evalClairvoyantWave_inhabited :
    evalClairvoyantWave (fun _ => none) none skipped [] [] = some ([], 0) := rfl
theorem evalClairvoyantWave_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) (S : Term) :
    ∀ (fs ps ps' : List (String × Term)) (k : Nat),
      evalClairvoyantWave eval optTarget S fs ps = some (ps', k) →
      Run .wave (.app (.app (.record fs) S) (.record ps)) (.record ps') k
  | [], [], _, _, h => by
    rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact .waveNil
  | (n, t) :: fs, (n', p) :: ps, _, _, h => by
    unfold evalClairvoyantWave at h
    split at h
    · rename_i hname
      have hn : n' = n := (beq_iff_eq.1 hname).symm; subst hn
      dsimp only at h
      split at h
      · rename_i p' k1 ps_rest k2 hcell hwave
        rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
        have hrun_cell : Run .cell (.app (.app t S) p) p' k1 := by
          split at hcell
          · rename_i hset
            rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩
            exact .cellValue (isSettled_sound _ hset)
          · rename_i hnset
            have hnot_sub : ¬ Settled (t.substitute (single S)) :=
              not_settled_of_isSettled_false (by simpa using hnset)
            split at hcell
            · rename_i hskip
              have hp_eq : p = skipped := isSkipped_sound hskip; subst hp_eq
              cases optTarget with
              | none =>
                simp only [↓reduceIte] at hcell; split at hcell
                · rename_i v kv hev; rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩
                  exact .cellEval hnot_sub (heval _ v kv hev)
                · rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩; exact .cellWait hnot_sub
              | some target =>
                dsimp only at hcell; split at hcell
                · split at hcell
                  · rename_i v kv hev; rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩
                    exact .cellEval hnot_sub (heval _ v kv hev)
                  · rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩; exact .cellWait hnot_sub
                · rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩; exact .cellWait hnot_sub
            · rename_i hnskip
              have hp_ne : p ≠ skipped := not_skipped_of_isSkipped_false (by simpa using hnskip)
              split at hcell
              · rename_i hsetp
                rcases Prod.mk.inj (Option.some.inj hcell) with ⟨rfl, rfl⟩
                exact .cellKeep hnot_sub (isSettled_sound p hsetp) hp_ne
              · cases hcell
        exact .waveCons hrun_cell (evalClairvoyantWave_sound heval optTarget S fs ps ps_rest k2 hwave)
      · cases h
    · cases h
  | [], _ :: _, _, _, h => by simp [evalClairvoyantWave] at h
  | _ :: _, [], _, _, h => by simp [evalClairvoyantWave] at h
/-- Try target-selective wave evaluation first (`optTarget`), falling back to full wave (`none`). -/
def evalClairvoyantStepWave (eval : Term → Option (Term × Nat))
    (optTarget : Option String) (S : Term) (fs ps : List (String × Term)) :
    Option (List (String × Term) × Nat) :=
  match optTarget with
  | some target =>
    match evalClairvoyantWave eval (some target) S fs ps with
    | some (ps', k) =>
      let resOk := match ps'.find? (fun f => f.1 == target) with
        | some (_, p) => !isSkipped p
        | none => true
      if resOk then some (ps', k) else evalClairvoyantWave eval none S fs ps
    | none => evalClairvoyantWave eval none S fs ps
  | none => evalClairvoyantWave eval none S fs ps

theorem evalClairvoyantStepWave_inhabited :
    evalClairvoyantStepWave (fun _ => none) none skipped [] [] = some ([], 0) := by
  unfold evalClairvoyantStepWave evalClairvoyantWave; rfl

theorem evalClairvoyantStepWave_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) (S : Term) (fs ps ps' : List (String × Term)) (k : Nat)
    (h : evalClairvoyantStepWave eval optTarget S fs ps = some (ps', k)) :
    Run .wave (.app (.app (.record fs) S) (.record ps)) (.record ps') k := by
  unfold evalClairvoyantStepWave at h
  cases optTarget with
  | none => exact evalClairvoyantWave_sound heval none S fs ps ps' k h
  | some target =>
    dsimp only at h
    split at h
    · rename_i ps1 k1 hw1
      by_cases hok : (match ps1.find? (fun f => f.1 == target) with | some (_, p) => !isSkipped p | none => true) = true
      · simp only [hok, ↓reduceIte] at h; rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
        exact evalClairvoyantWave_sound heval (some target) S fs ps ps1 k1 hw1
      · simp only [Bool.not_eq_true] at hok; simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
        exact evalClairvoyantWave_sound heval none S fs ps ps' k h
    · exact evalClairvoyantWave_sound heval none S fs ps ps' k h

def waveTargetDone (optTarget : Option String) (ps : List (String × Term)) : Bool :=
  match optTarget with
  | some target => match ps.find? (fun f => f.1 == target) with
    | some (_, p) => !isSkipped p
    | none => true
  | none => ps.all (fun f => !isSkipped f.2)

def hintTarget (hint : DemandHint) : Option String :=
  match hint with
  | .fieldOnly name => some name
  | _ => none

/-- Run subsequent knot waves (`Run.knotWave` / `Run.knotDone`). -/
@[expose] def evalClairvoyantKnotWaves (eval : Term → Option (Term × Nat)) (optTarget : Option String) :
    Nat → List (String × Term) → List (String × Term) → Option (Term × Nat)
  | 0, _, ps => if isCValue (.record ps) then some (.record ps, 0) else none
  | w + 1, fs, ps =>
    if waveTargetDone optTarget ps && isCValue (.record ps) then
      some (.record ps, 0)
    else
      match evalClairvoyantStepWave eval optTarget (.record ps) fs ps with
      | some (ps', k1) =>
        match evalClairvoyantKnotWaves eval optTarget w fs ps' with
        | some (V, k2) => some (V, k1 + k2)
        | none => if isCValue (.record ps) then some (.record ps, 0) else none
      | none => if isCValue (.record ps) then some (.record ps, 0) else none

theorem evalClairvoyantKnotWaves_inhabited :
    evalClairvoyantKnotWaves (fun _ => none) none 0 [] [] = some (.record [], 0) := by
  unfold evalClairvoyantKnotWaves; rfl

theorem evalClairvoyantKnotWaves_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) :
    ∀ (waves : Nat) (fs ps : List (String × Term)) (V : Term) (k : Nat),
      evalClairvoyantKnotWaves eval optTarget waves fs ps = some (V, k) →
      Run .knot (.app (.record fs) (.record ps)) V k
  | 0, _, ps, _, _, h => by
    unfold evalClairvoyantKnotWaves at h; split at h
    · rename_i hcv; rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      exact .knotDone (isCValue_sound (.record ps) hcv)
    · cases h
  | w + 1, fs, ps, _, _, h => by
    unfold evalClairvoyantKnotWaves at h
    by_cases hdone : (waveTargetDone optTarget ps && isCValue (.record ps)) = true
    · rw [ite_eq_left_iff.2 (fun hn => absurd hdone hn)] at h
      rw [Bool.and_eq_true] at hdone
      rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      exact .knotDone (isCValue_sound (.record ps) hdone.2)
    · rw [ite_eq_right_iff.2 (fun hy => absurd hy hdone)] at h
      cases hwave : evalClairvoyantStepWave eval optTarget (.record ps) fs ps with
      | some pk =>
        rw [hwave] at h; obtain ⟨ps', k1⟩ := pk; dsimp only at h
        have hrun_wave := evalClairvoyantStepWave_sound heval optTarget (.record ps) fs ps ps' k1 hwave
        cases hrest : evalClairvoyantKnotWaves eval optTarget w fs ps' with
        | some vk =>
          rw [hrest] at h; obtain ⟨V', k2⟩ := vk; dsimp only at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          exact .knotWave hrun_wave (evalClairvoyantKnotWaves_sound heval optTarget w fs ps' V' k2 hrest)
        | none =>
          rw [hrest] at h; dsimp only at h
          by_cases hcv : isCValue (.record ps) = true
          · rw [ite_eq_left_iff.2 (fun hn => absurd hcv hn)] at h
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .knotDone (isCValue_sound (.record ps) hcv)
          · rw [ite_eq_right_iff.2 (fun hy => absurd hy hcv)] at h; cases h
      | none =>
        rw [hwave] at h
        by_cases hcv : isCValue (.record ps) = true
        · rw [ite_eq_left_iff.2 (fun hn => absurd hcv hn)] at h
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          exact .knotDone (isCValue_sound (.record ps) hcv)
        · rw [ite_eq_right_iff.2 (fun hy => absurd hy hcv)] at h; cases h
/-! ## Demand-Hinted Clairvoyant Minimum-Cost Evaluator -/

/-- Demand-hinted fuel-bounded clairvoyant oracle evaluator (`evalClairvoyantWithHint`). -/
@[expose] def evalClairvoyantWithHint (hint : DemandHint) (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  if isCValue t then some (t, 0)
  else
    match fuel with
    | 0 => none
    | n + 1 =>
      match t with
      | .app f a =>
        match evalClairvoyantWithHint .full n f with
        | some (.lam b, k1) =>
          let letBranch :=
            if isSettled a then
              match evalClairvoyantWithHint hint n (instantiate b a) with
              | some (v, k3) => some (v, k1 + 0 + k3 + 1)
              | none => none
            else
              match evalClairvoyantWithHint .full n a with
              | some (va, ka) =>
                match evalClairvoyantWithHint hint n (instantiate b va) with
                | some (v, k3) => some (v, k1 + (ka + 1) + k3 + 1)
                | none => none
              | none => none
          let skipBranch :=
            match evalClairvoyantWithHint hint n (instantiate b skipped) with
            | some (v, k3) => some (v, k1 + 1 + k3 + 1)
            | none => none
          pickMinCost letBranch skipBranch
        | some (.specification _ e, k1) =>
          let fullSpecBranch :=
            match evalClairvoyantWithHint hint n (.app e a) with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          let skipMetaBranch :=
            match evalClairvoyantWithHint .specApply n f with
            | some (.specification _ e', k1') =>
              match evalClairvoyantWithHint hint n (.app e' a) with
              | some (v, k2) => some (v, k1' + k2 + 1)
              | none => none
            | _ => none
          pickMinCost fullSpecBranch skipMetaBranch
        | _ => none
      | .mix l u => some (mixBody l u, 1)
      | .fix s i =>
        match evalClairvoyantHead (evalClairvoyantWithHint .full n) n (selfBody s i) with
        | some (T, k1) =>
          let optTarget := hintTarget hint
          let knotOpt :=
            if isCValue T then
              let P := T.substitute (single skipped)
              if isCValue P then some (P, 0) else none
            else
              match T with
              | .record fs =>
                let pend := fs.map fun f => (f.1, skipped)
                match evalClairvoyantStepWave (evalClairvoyantWithHint .full n) optTarget skipped fs pend with
                | some (ps1, kw1) =>
                  match evalClairvoyantKnotWaves (evalClairvoyantWithHint .full n) optTarget n fs ps1 with
                  | some (V, kw2) => some (V, kw1 + kw2)
                  | none => none
                | none => none
              | _ => none
          match knotOpt with
          | some (V, k2) => some (V, k1 + k2 + 1)
          | none => none
        | none => none
      | .specification m e =>
        let (m', k1) := match hint with
          | .specApply => if isSettled m then (m, 0) else (skipped, 1)
          | _ => if isSettled m then (m, 0)
            else match evalClairvoyantWithHint .full n m with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
        let (e', k2) := match hint with
          | .specMetadata => if isSettled e then (e, 0) else (skipped, 1)
          | _ => if isSettled e then (e, 0)
            else match evalClairvoyantWithHint .full n e with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
        some (.specification m' e', k1 + k2 + 1)
      | .prototype s g =>
        let (s', k1) := match hint with
          | .protoProject => if isSettled s then (s, 0) else (skipped, 1)
          | _ => if isSettled s then (s, 0)
            else match evalClairvoyantWithHint .full n s with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
        let (g', k2) := match hint with
          | .protoReflect => if isSettled g then (g, 0) else (skipped, 1)
          | _ => if isSettled g then (g, 0)
            else match evalClairvoyantWithHint .full n g with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
        some (.prototype s' g', k1 + k2 + 1)
      | .project p =>
        let projBranch :=
          match evalClairvoyantWithHint .protoProject n p with
          | some (.prototype _ g, k1) =>
            match evalClairvoyantWithHint hint n g with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n p with
          | some (.prototype _ g, k1) =>
            match evalClairvoyantWithHint hint n g with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | _ => none
        pickMinCost projBranch fullBranch
      | .reflect p =>
        let reflBranch :=
          match evalClairvoyantWithHint .protoReflect n p with
          | some (.prototype s _, k1) =>
            match evalClairvoyantWithHint hint n s with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n p with
          | some (.prototype s _, k1) =>
            match evalClairvoyantWithHint hint n s with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | _ => none
        pickMinCost reflBranch fullBranch
      | .metadata p =>
        let metaBranch :=
          match evalClairvoyantWithHint .specMetadata n p with
          | some (.specification me _, k1) =>
            match evalClairvoyantWithHint hint n me with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n p with
          | some (.specification me _, k1) =>
            match evalClairvoyantWithHint hint n me with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | _ => none
        pickMinCost metaBranch fullBranch
      | .record fs =>
        let recOpt := match hint with
          | .fieldOnly target => some (evalClairvoyantFieldsFor (evalClairvoyantWithHint .full n) (some target) fs)
          | .skipAllFields => some (evalClairvoyantFieldsFor (evalClairvoyantWithHint .full n) none fs)
          | _ => evalClairvoyantFields (evalClairvoyantWithHint .full n) fs
        match recOpt with | some (fs', k) => some (.record fs', k + 1) | none => none
      | .get g name =>
        let focusedBranch :=
          match evalClairvoyantWithHint (.fieldOnly name) n g with
          | some (.record fs, k1) =>
            match fs.find? (fun f => f.1 == name) with
            | some (_, x) =>
              match evalClairvoyantWithHint hint n x with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
            | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n g with
          | some (.record fs, k1) =>
            match fs.find? (fun f => f.1 == name) with
            | some (_, x) =>
              match evalClairvoyantWithHint hint n x with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
            | none => none
          | _ => none
        pickMinCost focusedBranch fullBranch
      | .extend i fs =>
        match hint with
        | .fieldOnly target =>
          if fs.any (fun f => f.1 == target) then
            let bfs := evalClairvoyantFieldsFor (evalClairvoyantWithHint .full n) (some target) fs
            match evalClairvoyantWithHint .skipAllFields n i with
            | some (.record inh, k1) => some (.record (extendFields inh bfs.1), k1 + bfs.2 + 1)
            | _ => none
          else
            let bfs := evalClairvoyantFieldsFor (evalClairvoyantWithHint .full n) none fs
            match evalClairvoyantWithHint (.fieldOnly target) n i with
            | some (.record inh, k1) => some (.record (extendFields inh bfs.1), k1 + bfs.2 + 1)
            | _ => none
        | .skipAllFields =>
          let bfs := evalClairvoyantFieldsFor (evalClairvoyantWithHint .full n) none fs
          match evalClairvoyantWithHint .skipAllFields n i with
          | some (.record inh, k1) => some (.record (extendFields inh bfs.1), k1 + bfs.2 + 1)
          | _ => none
        | _ =>
          match evalClairvoyantWithHint .full n i, evalClairvoyantFields (evalClairvoyantWithHint .full n) fs with
          | some (.record inh, k1), some (fs', k2) => some (.record (extendFields inh fs'), k1 + k2 + 1)
          | _, _ => none
      | .binary op l r =>
        match evalClairvoyantWithHint .full n l, evalClairvoyantWithHint .full n r with
        | some (lv, k1), some (rv, k2) =>
          match primitiveResult op lv rv with | some res => some (res, k1 + k2 + 1) | none => none
        | _, _ => none
      | .ifZero c z s =>
        match evalClairvoyantWithHint .full n c with
        | some (.nat 0, k1) =>
          match evalClairvoyantWithHint hint n z with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | some (.nat (m + 1), k1) =>
          match evalClairvoyantWithHint hint n (instantiate s (.nat m)) with
          | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .inject l p =>
        let (p', kp) := match hint with
          | .skipInjectPayload => if isSettled p then (p, 0) else (skipped, 1)
          | _ => if isSettled p then (p, 0)
            else match evalClairvoyantWithHint .full n p with | some (vt, kt) => (vt, kt + 1) | none => (skipped, 1)
        some (.inject l p', kp + 1)
      | .case sc arms =>
        let stdBranch :=
          match evalClairvoyantWithHint .full n sc with
          | some (.inject l p, k1) =>
            match arms.find? (fun a => a.1 == l) with
            | some (_, body) =>
              match evalClairvoyantWithHint hint n (instantiate body p) with
              | some (v, k2) => some (v, k1 + k2 + 1) | none => none
            | none => none
          | _ => none
        let skipScBranch :=
          match evalClairvoyantWithHint .skipInjectPayload n sc with
          | some (.inject l p, k1) =>
            match arms.find? (fun a => a.1 == l) with
            | some (_, body) =>
              match evalClairvoyantWithHint hint n (instantiate body p) with
              | some (v, k2) => some (v, k1 + k2 + 1) | none => none
            | none => none
          | _ => none
        pickMinCost stdBranch skipScBranch
      | .ifBool c x y =>
        match evalClairvoyantWithHint .full n c with
        | some (.boolean true, k1) =>
          match evalClairvoyantWithHint hint n x with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | some (.boolean false, k1) =>
          match evalClairvoyantWithHint hint n y with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .done x =>
        match evalClairvoyantWithHint hint n x with | some (v, k) => some (v, k + 1) | none => none
      | _ => none
termination_by structural fuel
/-- Executable fuel-bounded clairvoyant oracle evaluator (`evalClairvoyantMinCost`). -/
@[expose] def evalClairvoyantMinCost (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  evalClairvoyantWithHint .full fuel t
theorem evalClairvoyantWithHint_inhabited :
    evalClairvoyantWithHint .full 0 (.nat 0) = some (.nat 0, 0) := by
  unfold evalClairvoyantWithHint; rfl
theorem evalClairvoyantWithHint_sound : ∀ (fuel : Nat) (hint : DemandHint) (t v : Term) (k : Nat),
    evalClairvoyantWithHint hint fuel t = some (v, k) → CV t v k
  | fuel, hint, t, v, k, h => by
    unfold evalClairvoyantWithHint at h
    split at h
    · rename_i hcv
      rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      exact .value (isCValue_sound t hcv)
    · rename_i hncv
      have hnotcv : ¬ CValue t := fun hc => hncv hc.isCValue_eq_true
      cases fuel with
      | zero => simp at h
      | succ n =>
        simp only at h
        have ih := evalClairvoyantWithHint_sound n
        split at h
        · rename_i f a
          split at h
          · rename_i b k1 hf
            have hrunf : CV f (.lam b) k1 := ih .full f (.lam b) k1 hf
            refine pickMinCost_sound ?_ ?_ h
            · intro v1 k_let hlet
              split at hlet
              · rename_i hsa
                split at hlet
                · rename_i v3 k3 hbody
                  rcases Prod.mk.inj (Option.some.inj hlet) with ⟨rfl, rfl⟩
                  exact .apply hrunf (.keep (isSettled_sound a hsa)) (ih hint _ v3 k3 hbody)
                · cases hlet
              · rename_i hnsa
                have hnot_sa : ¬ Settled a := fun hs => hnsa hs.isSettled_eq_true
                split at hlet
                · rename_i va ka ha
                  split at hlet
                  · rename_i v3 k3 hbody
                    rcases Prod.mk.inj (Option.some.inj hlet) with ⟨rfl, rfl⟩
                    exact .apply hrunf (.eval hnot_sa (ih .full a va ka ha)) (ih hint _ v3 k3 hbody)
                  · cases hlet
                · cases hlet
            · intro v2 k_skip hskip
              split at hskip
              · rename_i v3 k3 hbody
                rcases Prod.mk.inj (Option.some.inj hskip) with ⟨rfl, rfl⟩
                exact .apply hrunf (.skip a) (ih hint _ v3 k3 hbody)
              · cases hskip
          · rename_i me e k1 hf
            have hrunf : CV f (.specification me e) k1 := ih .full f (.specification me e) k1 hf
            refine pickMinCost_sound ?_ ?_ h
            · intro v1 k_full hfull
              split at hfull
              · rename_i v2 k2 hbody
                rcases Prod.mk.inj (Option.some.inj hfull) with ⟨rfl, rfl⟩
                exact .applySpec hrunf (ih hint (.app e a) v2 k2 hbody)
              · cases hfull
            · intro v2 k_skip hskip
              split at hskip
              · rename_i me' e' k1' hf'
                split at hskip
                · rename_i v3 k2 hbody
                  rcases Prod.mk.inj (Option.some.inj hskip) with ⟨rfl, rfl⟩
                  exact .applySpec (ih .specApply f (.specification me' e') k1' hf')
                    (ih hint (.app e' a) v3 k2 hbody)
                · cases hskip
              · cases hskip
          · cases h
        · rename_i l u
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact .mix l u
        · rename_i s i
          split at h
          · rename_i T k1 hhead
            split at h
            · rename_i V k2 hknot
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              have hrun_knot : Run .knot (.app T skipped) V k2 := by
                split at hknot
                · rename_i hcvT
                  split at hknot
                  · rename_i hcvP
                    rcases Prod.mk.inj (Option.some.inj hknot) with ⟨rfl, rfl⟩
                    exact .knotUnroll (isCValue_sound T hcvT) (.knotDone (isCValue_sound _ hcvP))
                  · cases hknot
                · cases T with
                  | record fs =>
                    dsimp only at hknot
                    let pend := fs.map fun f => (f.1, skipped)
                    cases hs1 : evalClairvoyantStepWave (evalClairvoyantWithHint .full n) (hintTarget hint) skipped fs pend with
                    | none => rw [hs1] at hknot; cases hknot
                    | some p1 =>
                      rw [hs1] at hknot; obtain ⟨ps1, kw1⟩ := p1; dsimp only at hknot
                      cases hwaves : evalClairvoyantKnotWaves (evalClairvoyantWithHint .full n) (hintTarget hint) n fs ps1 with
                      | none => rw [hwaves] at hknot; cases hknot
                      | some vk =>
                        rw [hwaves] at hknot; obtain ⟨V', kw2⟩ := vk; dsimp only at hknot
                        rcases Prod.mk.inj (Option.some.inj hknot) with ⟨rfl, rfl⟩
                        have hw1 : Run .wave (.app (.app (.record fs) skipped) (pending fs)) (.record ps1) kw1 :=
                          evalClairvoyantStepWave_sound (ih .full) (hintTarget hint) skipped fs pend ps1 kw1 hs1
                        exact .knotFirst hw1 (evalClairvoyantKnotWaves_sound (ih .full) (hintTarget hint) n fs ps1 V' kw2 hwaves)
                  | bound _ | hole _ _ | label _ | lam _ | app _ _ | mix _ _ | fix _ _
                  | specification _ _ | prototype _ _ | project _ | reflect _ | metadata _
                  | get _ _ | extend _ _ | nat _ | binary _ _ _ | ifZero _ _ _ | inject _ _
                  | case _ _ | boolean _ | ifBool _ _ _ | done _ | perform _ | split _ _ _ => cases hknot
              exact .fix (evalClairvoyantHead_sound (ih .full) n (selfBody s i) T k1 hhead) hrun_knot
            · cases h
          · cases h
        · rename_i m e
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          refine .specification hnotcv ?_ ?_
          · cases hint <;> first | exact skipBind_sound m | exact evalBind_sound (ih .full) m
          · cases hint <;> first | exact skipBind_sound e | exact evalBind_sound (ih .full) e
        · rename_i s g
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          refine .prototype hnotcv ?_ ?_
          · cases hint <;> first | exact skipBind_sound s | exact evalBind_sound (ih .full) s
          · cases hint <;> first | exact skipBind_sound g | exact evalBind_sound (ih .full) g
        · rename_i p
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_proj hproj
            split at hproj
            · rename_i s g k1 hp
              split at hproj
              · rename_i v2 k2 hg
                rcases Prod.mk.inj (Option.some.inj hproj) with ⟨rfl, rfl⟩
                exact .project (ih .protoProject p (.prototype s g) k1 hp) (ih hint g v2 k2 hg)
              · cases hproj
            · cases hproj
          · intro v2 k_full hfull
            split at hfull
            · rename_i s g k1 hp
              split at hfull
              · rename_i v3 k2 hg
                rcases Prod.mk.inj (Option.some.inj hfull) with ⟨rfl, rfl⟩
                exact .project (ih .full p (.prototype s g) k1 hp) (ih hint g v3 k2 hg)
              · cases hfull
            · cases hfull
        · rename_i p
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_refl hrefl
            split at hrefl
            · rename_i s g k1 hp
              split at hrefl
              · rename_i v2 k2 hs
                rcases Prod.mk.inj (Option.some.inj hrefl) with ⟨rfl, rfl⟩
                exact .reflect (ih .protoReflect p (.prototype s g) k1 hp) (ih hint s v2 k2 hs)
              · cases hrefl
            · cases hrefl
          · intro v2 k_full hfull
            split at hfull
            · rename_i s g k1 hp
              split at hfull
              · rename_i v3 k2 hs
                rcases Prod.mk.inj (Option.some.inj hfull) with ⟨rfl, rfl⟩
                exact .reflect (ih .full p (.prototype s g) k1 hp) (ih hint s v3 k2 hs)
              · cases hfull
            · cases hfull
        · rename_i p
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_meta hmeta
            split at hmeta
            · rename_i me e k1 hp
              split at hmeta
              · rename_i v2 k2 hm
                rcases Prod.mk.inj (Option.some.inj hmeta) with ⟨rfl, rfl⟩
                exact .metadata (ih .specMetadata p (.specification me e) k1 hp) (ih hint me v2 k2 hm)
              · cases hmeta
            · cases hmeta
          · intro v2 k_full hfull
            split at hfull
            · rename_i me e k1 hp
              split at hfull
              · rename_i v3 k2 hm
                rcases Prod.mk.inj (Option.some.inj hfull) with ⟨rfl, rfl⟩
                exact .metadata (ih .full p (.specification me e) k1 hp) (ih hint me v3 k2 hm)
              · cases hfull
            · cases hfull
        · rename_i fs
          split at h
          · rename_i fs' kf hfs
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            have hrf : Run .fields (.record fs) (.record fs') kf := by
              cases hint with
              | fieldOnly target =>
                rcases Prod.mk.inj (Option.some.inj hfs) with ⟨rfl, rfl⟩
                exact evalClairvoyantFieldsFor_sound (ih .full) (some target) fs
              | skipAllFields =>
                rcases Prod.mk.inj (Option.some.inj hfs) with ⟨rfl, rfl⟩
                exact evalClairvoyantFieldsFor_sound (ih .full) none fs
              | full | skipInjectPayload | protoReflect | protoProject | specMetadata | specApply =>
                exact evalClairvoyantFields_sound (ih .full) fs fs' kf hfs
            exact .record hnotcv hrf
          · cases h
        · rename_i g name
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_foc hfoc
            split at hfoc
            · rename_i fs k1 hg
              split at hfoc
              · rename_i f_name x hfind
                have hname : f_name = name := by simpa using List.find?_some hfind
                subst hname
                split at hfoc
                · rename_i v2 k2 hx
                  rcases Prod.mk.inj (Option.some.inj hfoc) with ⟨rfl, rfl⟩
                  exact .get (ih (.fieldOnly f_name) g (.record fs) k1 hg) hfind (ih hint x v2 k2 hx)
                · cases hfoc
              · cases hfoc
            · cases hfoc
          · intro v2 k_full hfull
            split at hfull
            · rename_i fs k1 hg
              split at hfull
              · rename_i f_name x hfind
                have hname : f_name = name := by simpa using List.find?_some hfind
                subst hname
                split at hfull
                · rename_i v3 k2 hx
                  rcases Prod.mk.inj (Option.some.inj hfull) with ⟨rfl, rfl⟩
                  exact .get (ih .full g (.record fs) k1 hg) hfind (ih hint x v3 k2 hx)
                · cases hfull
              · cases hfull
            · cases hfull
        · rename_i i fs
          cases hint with
          | fieldOnly target =>
            dsimp only at h
            split at h
            · split at h
              · rename_i inh k1 hi
                rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
                exact .extend (ih .skipAllFields i (.record inh) k1 hi)
                  (evalClairvoyantFieldsFor_sound (ih .full) (some target) fs)
              · cases h
            · split at h
              · rename_i inh k1 hi
                rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
                exact .extend (ih (.fieldOnly target) i (.record inh) k1 hi)
                  (evalClairvoyantFieldsFor_sound (ih .full) none fs)
              · cases h
          | skipAllFields =>
            dsimp only at h
            split at h
            · rename_i inh k1 hi
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .extend (ih .skipAllFields i (.record inh) k1 hi)
                (evalClairvoyantFieldsFor_sound (ih .full) none fs)
            · cases h
          | full | skipInjectPayload | protoReflect | protoProject | specMetadata | specApply =>
            dsimp only at h
            split at h
            · rename_i inh k1 fs' k2 hi hfs
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .extend (ih .full i (.record inh) k1 hi)
                (evalClairvoyantFields_sound (ih .full) fs fs' k2 hfs)
            · cases h
        · rename_i op l r
          split at h
          · rename_i lv k1 rv k2 hl hr
            split at h
            · rename_i res hprim
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .binary (ih .full l lv k1 hl) (ih .full r rv k2 hr) hprim
            · cases h
          · cases h
        · rename_i c z s
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hz
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .zero (ih .full c (.nat 0) k1 hc) (ih hint z v2 k2 hz)
            · cases h
          · rename_i m k1 hc
            split at h
            · rename_i v2 k2 hs
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .succ (ih .full c (.nat (m + 1)) k1 hc) (ih hint (instantiate s (.nat m)) v2 k2 hs)
            · cases h
          · cases h
        · rename_i l p
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
          refine .inject hnotcv ?_
          cases hint <;> first | exact skipBind_sound p | exact evalBind_sound (ih .full) p
        · rename_i sc arms
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_std hstd
            split at hstd
            · rename_i l p k1 hsc
              split at hstd
              · rename_i arm_l body hfind
                have hl : arm_l = l := by simpa using List.find?_some hfind
                subst hl
                split at hstd
                · rename_i v2 k2 hbody
                  rcases Prod.mk.inj (Option.some.inj hstd) with ⟨rfl, rfl⟩
                  exact .case (ih .full sc (.inject arm_l p) k1 hsc) hfind
                    (ih hint (instantiate body p) v2 k2 hbody)
                · cases hstd
              · cases hstd
            · cases hstd
          · intro v2 k_skip hskip
            split at hskip
            · rename_i l p k1 hsc
              split at hskip
              · rename_i arm_l body hfind
                have hl : arm_l = l := by simpa using List.find?_some hfind
                subst hl
                split at hskip
                · rename_i v3 k2 hbody
                  rcases Prod.mk.inj (Option.some.inj hskip) with ⟨rfl, rfl⟩
                  exact .case (ih .skipInjectPayload sc (.inject arm_l p) k1 hsc) hfind
                    (ih hint (instantiate body p) v3 k2 hbody)
                · cases hskip
              · cases hskip
            · cases hskip
        · rename_i c x y
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hx
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .ifTrue (ih .full c (.boolean true) k1 hc) (ih hint x v2 k2 hx)
            · cases h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hy
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .ifFalse (ih .full c (.boolean false) k1 hc) (ih hint y v2 k2 hy)
            · cases h
          · cases h
        · rename_i x
          split at h
          · rename_i v2 k2 hx
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .done (ih hint x v2 k2 hx)
          · cases h
        · cases h
/-- Soundness of `evalClairvoyantMinCost`: every result `some (v, k)` is backed by `CV t v k`. -/
theorem evalClairvoyantMinCost_sound (fuel : Nat) (t v : Term) (k : Nat)
    (h : evalClairvoyantMinCost fuel t = some (v, k)) : CV t v k :=
  evalClairvoyantWithHint_sound fuel .full t v k h
/-- Soundness of `evalClairvoyantMinCost` on closed values (`CValue v`): returns `some (v, 0)`. -/
theorem evalClairvoyantMinCost_value_sound {v : Term} (hv : CValue v) (fuel : Nat) :
    evalClairvoyantMinCost fuel v = some (v, 0) ∧ CV v v 0 := by
  refine ⟨?_, .value hv⟩
  unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp [hv.isCValue_eq_true]
/-- Soundness of `evalClairvoyantMinCost` on β-redexes where the `Skip` branch succeeds. -/
theorem evalClairvoyantMinCost_skip_app_sound (b a v : Term) (k3 fuel : Nat)
    (hskip : evalClairvoyantMinCost fuel (instantiate b skipped) = some (v, k3)) :
    ∃ v' k', evalClairvoyantMinCost (fuel + 1) (.app (.lam b) a) = some (v', k') ∧
      k' ≤ k3 + 2 ∧ CV (.app (.lam b) a) v' k' := by
  have hncv : isCValue (.app (.lam b) a) = false := isCValue_app (.lam b) a
  have hlam : evalClairvoyantWithHint .full fuel (.lam b) = some (.lam b, 0) :=
    (evalClairvoyantMinCost_value_sound (.lam b) fuel).1
  have hskip' : evalClairvoyantWithHint .full fuel (instantiate b skipped) = some (v, k3) := hskip
  obtain ⟨v', k', hpick, hle⟩ :=
    pickMinCost_le_right (o1 :=
      if isSettled a then
        match evalClairvoyantWithHint .full fuel (instantiate b a) with
        | some (v, k3) => some (v, 0 + 0 + k3 + 1)
        | none => none
      else
        match evalClairvoyantWithHint .full fuel a with
        | some (va, ka) =>
          match evalClairvoyantWithHint .full fuel (instantiate b va) with
          | some (v, k3) => some (v, 0 + (ka + 1) + k3 + 1)
          | none => none
        | none => none)
      (v2 := v) (k2 := 0 + 1 + k3 + 1)
  have heval : evalClairvoyantMinCost (fuel + 1) (.app (.lam b) a) = some (v', k') := by
    unfold evalClairvoyantMinCost evalClairvoyantWithHint
    simp only [hncv, Bool.false_eq_true, ite_false, hlam, hskip']
    exact hpick
  exact ⟨v', k', heval, by omega, evalClairvoyantMinCost_sound (fuel + 1) _ v' k' heval⟩
/-- Constant function `λ x => .nat n` applied to `a` achieves cost `2` via `Skip`. -/
theorem cv_skip_const_app (n : Nat) (a : Term) :
    CV (.app (.lam (.nat n)) a) (.nat n) 2 := by
  have hbody : instantiate (.nat n) skipped = .nat n := by simp [instantiate, Term.substitute]
  have := Run.apply (Run.value (.lam (.nat n))) (Run.skip a) (by rw [hbody]; exact Run.value (.nat n))
  simpa using this
/-- **`evalClairvoyant_skip_unused_arg_saves_cost`**: `λ x => .nat 42` skips unsettled `a` at cost `2`. -/
theorem evalClairvoyant_skip_unused_arg_saves_cost (a : Term) (ha : ¬ Settled a) (fuel : Nat) :
    evalClairvoyantMinCost (fuel + 1) (.app (.lam (.nat 42)) a) = some (.nat 42, 2) ∧
      CV (.app (.lam (.nat 42)) a) (.nat 42) 2 := by
  refine ⟨?_, cv_skip_const_app 42 a⟩
  have hnsa : isSettled a = false := by
    cases h : isSettled a with | false => rfl | true => exact absurd (isSettled_sound a h) ha
  have hncv : isCValue (.app (.lam (.nat 42)) a) = false := isCValue_app (.lam (.nat 42)) a
  have hlam : evalClairvoyantWithHint .full fuel (.lam (.nat 42)) = some (.lam (.nat 42), 0) :=
    (evalClairvoyantMinCost_value_sound (.lam (.nat 42)) fuel).1
  have hinst : ∀ x, instantiate (.nat 42) x = .nat 42 := fun _ => by simp [instantiate, Term.substitute]
  have hnat : evalClairvoyantWithHint .full fuel (.nat 42) = some (.nat 42, 0) :=
    (evalClairvoyantMinCost_value_sound (.nat 42) fuel).1
  conv => lhs; unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp only [hncv, Bool.false_eq_true, ite_false, hlam, hnsa, hinst, hnat]
  cases evalClairvoyantWithHint .full fuel a with
  | none => rfl
  | some r =>
    obtain ⟨va, ka⟩ := r; simp only [pickMinCost]
    split
    · rename_i hle; have hka : ka = 0 := by omega
      subst hka; rfl
    · rfl
/-! ## Eager Call-By-Value Evaluator (`evalCBV`) -/

private theorem cbvBind_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (t t' : Term) (k : Nat)
    (h : (if isSettled t then some (t, 0)
      else match eval t with | some (vt, kt) => some (vt, kt + 1) | none => none) = some (t', k)) :
    Run .bind t t' k := by
  split at h
  · rename_i hs; rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
    exact .keep (isSettled_sound t hs)
  · rename_i hns
    have hnot : ¬ Settled t := fun hs => hns hs.isSettled_eq_true
    split at h
    · rename_i vt kt ht; rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      exact .eval hnot (heval t vt kt ht)
    · cases h
/-- Eager Call-By-Value record field evaluation (`Run .fields` without `Skip`). -/
@[expose] def evalCBVFields (eval : Term → Option (Term × Nat)) :
    List (String × Term) → Option (List (String × Term) × Nat)
  | [] => some ([], 0)
  | (name, field) :: rest =>
    let bOpt := if isSettled field then some (field, 0)
      else match eval field with | some (vt, kt) => some (vt, kt + 1) | none => none
    match bOpt, evalCBVFields eval rest with
    | some (field', k1), some (rest', k2) => some ((name, field') :: rest', k1 + k2 + 1)
    | _, _ => none
theorem evalCBVFields_inhabited :
    evalCBVFields (fun _ => none) [] = some ([], 0) := rfl
theorem evalCBVFields_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (fs fs' : List (String × Term)) (k : Nat),
      evalCBVFields eval fs = some (fs', k) →
      Run .fields (.record fs) (.record fs') k
  | [], _, _, h => by
    rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact .nil
  | (_, field) :: rest, _, _, h => by
    unfold evalCBVFields at h; dsimp only at h
    split at h
    · rename_i field' k1 rest' k2 hf hr
      rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      exact .cons (cbvBind_sound heval field field' k1 hf)
        (evalCBVFields_sound heval rest rest' k2 hr)
    · cases h
/-- Executable fuel-bounded Call-By-Value evaluator (`evalCBV`). -/
@[expose] def evalCBV (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  if isCValue t then
    some (t, 0)
  else
    match fuel with
    | 0 => none
    | n + 1 =>
      match t with
      | .app f a =>
        match evalCBV n f with
        | some (.lam b, k1) =>
          if isSettled a then
            match evalCBV n (instantiate b a) with
            | some (v, k3) => some (v, k1 + 0 + k3 + 1)
            | none => none
          else
            match evalCBV n a with
            | some (va, ka) =>
              match evalCBV n (instantiate b va) with
              | some (v, k3) => some (v, k1 + (ka + 1) + k3 + 1)
              | none => none
            | none => none
        | some (.specification _ e, k1) =>
          match evalCBV n (.app e a) with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .mix l u => some (mixBody l u, 1)
      | .specification m e =>
        let bm := if isSettled m then some (m, 0)
          else match evalCBV n m with | some (vt, kt) => some (vt, kt + 1) | none => none
        let be := if isSettled e then some (e, 0)
          else match evalCBV n e with | some (vt, kt) => some (vt, kt + 1) | none => none
        match bm, be with
        | some (m', k1), some (e', k2) => some (.specification m' e', k1 + k2 + 1)
        | _, _ => none
      | .prototype s g =>
        let bs := if isSettled s then some (s, 0)
          else match evalCBV n s with | some (vt, kt) => some (vt, kt + 1) | none => none
        let bg := if isSettled g then some (g, 0)
          else match evalCBV n g with | some (vt, kt) => some (vt, kt + 1) | none => none
        match bs, bg with
        | some (s', k1), some (g', k2) => some (.prototype s' g', k1 + k2 + 1)
        | _, _ => none
      | .project p =>
        match evalCBV n p with
        | some (.prototype _ g, k1) =>
          match evalCBV n g with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .reflect p =>
        match evalCBV n p with
        | some (.prototype s _, k1) =>
          match evalCBV n s with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .metadata p =>
        match evalCBV n p with
        | some (.specification me _, k1) =>
          match evalCBV n me with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .record fs =>
        match evalCBVFields (evalCBV n) fs with
        | some (fs', k) => some (.record fs', k + 1)
        | none => none
      | .get g name =>
        match evalCBV n g with
        | some (.record fs, k1) =>
          match fs.find? (fun f => f.1 == name) with
          | some (_, x) =>
            match evalCBV n x with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | none => none
        | _ => none
      | .extend i fs =>
        match evalCBV n i, evalCBVFields (evalCBV n) fs with
        | some (.record inh, k1), some (fs', k2) => some (.record (extendFields inh fs'), k1 + k2 + 1)
        | _, _ => none
      | .binary op l r =>
        match evalCBV n l, evalCBV n r with
        | some (lv, k1), some (rv, k2) =>
          match primitiveResult op lv rv with | some res => some (res, k1 + k2 + 1) | none => none
        | _, _ => none
      | .ifZero c z s =>
        match evalCBV n c with
        | some (.nat 0, k1) =>
          match evalCBV n z with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | some (.nat (m + 1), k1) =>
          match evalCBV n (instantiate s (.nat m)) with
          | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .inject l p =>
        if isSettled p then some (.inject l p, 0 + 1)
        else
          match evalCBV n p with
          | some (vp, kp) => some (.inject l vp, (kp + 1) + 1)
          | none => none
      | .case sc arms =>
        match evalCBV n sc with
        | some (.inject l p, k1) =>
          match arms.find? (fun a => a.1 == l) with
          | some (_, body) =>
            match evalCBV n (instantiate body p) with
            | some (v, k2) => some (v, k1 + k2 + 1) | none => none
          | none => none
        | _ => none
      | .ifBool c x y =>
        match evalCBV n c with
        | some (.boolean true, k1) =>
          match evalCBV n x with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | some (.boolean false, k1) =>
          match evalCBV n y with | some (v, k2) => some (v, k1 + k2 + 1) | none => none
        | _ => none
      | .done x =>
        match evalCBV n x with | some (v, k) => some (v, k + 1) | none => none
      | _ => none
theorem evalCBV_inhabited : evalCBV 0 (.nat 0) = some (.nat 0, 0) := by
  unfold evalCBV; rfl
theorem evalCBV_sound : ∀ (fuel : Nat) (t v : Term) (k : Nat),
    evalCBV fuel t = some (v, k) → CV t v k
  | fuel, t, v, k, h => by
    unfold evalCBV at h
    split at h
    · rename_i hcv
      rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
      exact .value (isCValue_sound t hcv)
    · rename_i hncv
      have hnotcv : ¬ CValue t := fun hc => hncv hc.isCValue_eq_true
      cases fuel with
      | zero => simp at h
      | succ n =>
        simp only at h
        have ih := evalCBV_sound n
        split at h
        · rename_i f a
          split at h
          · rename_i b k1 hf
            have hrunf : CV f (.lam b) k1 := ih f (.lam b) k1 hf
            split at h
            · rename_i hsa
              split at h
              · rename_i v3 k3 hbody
                rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
                exact .apply hrunf (.keep (isSettled_sound a hsa)) (ih _ v3 k3 hbody)
              · cases h
            · rename_i hnsa
              have hnot_sa : ¬ Settled a := fun hs => hnsa hs.isSettled_eq_true
              split at h
              · rename_i va ka ha
                split at h
                · rename_i v3 k3 hbody
                  rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
                  exact .apply hrunf (.eval hnot_sa (ih a va ka ha)) (ih _ v3 k3 hbody)
                · cases h
              · cases h
          · rename_i me e k1 hf
            split at h
            · rename_i v2 k2 hbody
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .applySpec (ih f (.specification me e) k1 hf) (ih (.app e a) v2 k2 hbody)
            · cases h
          · cases h
        · rename_i l u
          rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩; exact .mix l u
        · rename_i m e
          split at h
          · rename_i m' k1 e' k2 hm he
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .specification hnotcv (cbvBind_sound ih m m' k1 hm) (cbvBind_sound ih e e' k2 he)
          · cases h
        · rename_i s g
          split at h
          · rename_i s' k1 g' k2 hs hg
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .prototype hnotcv (cbvBind_sound ih s s' k1 hs) (cbvBind_sound ih g g' k2 hg)
          · cases h
        · rename_i p
          split at h
          · rename_i s g k1 hp
            split at h
            · rename_i v2 k2 hg
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .project (ih p (.prototype s g) k1 hp) (ih g v2 k2 hg)
            · cases h
          · cases h
        · rename_i p
          split at h
          · rename_i s g k1 hp
            split at h
            · rename_i v2 k2 hs
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .reflect (ih p (.prototype s g) k1 hp) (ih s v2 k2 hs)
            · cases h
          · cases h
        · rename_i p
          split at h
          · rename_i me e k1 hp
            split at h
            · rename_i v2 k2 hm
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .metadata (ih p (.specification me e) k1 hp) (ih me v2 k2 hm)
            · cases h
          · cases h
        · rename_i fs
          split at h
          · rename_i fs' kf hfs
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .record hnotcv (evalCBVFields_sound ih fs fs' kf hfs)
          · cases h
        · rename_i g name
          split at h
          · rename_i fs k1 hg
            split at h
            · rename_i f_name x hfind
              have hname : f_name = name := by simpa using List.find?_some hfind
              subst hname
              split at h
              · rename_i v2 k2 hx
                rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
                exact .get (ih g (.record fs) k1 hg) hfind (ih x v2 k2 hx)
              · cases h
            · cases h
          · cases h
        · rename_i i fs
          split at h
          · rename_i inh k1 fs' k2 hi hfs
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .extend (ih i (.record inh) k1 hi) (evalCBVFields_sound ih fs fs' k2 hfs)
          · cases h
        · rename_i op l r
          split at h
          · rename_i lv k1 rv k2 hl hr
            split at h
            · rename_i res hprim
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .binary (ih l lv k1 hl) (ih r rv k2 hr) hprim
            · cases h
          · cases h
        · rename_i c z s
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hz
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .zero (ih c (.nat 0) k1 hc) (ih z v2 k2 hz)
            · cases h
          · rename_i m k1 hc
            split at h
            · rename_i v2 k2 hs
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .succ (ih c (.nat (m + 1)) k1 hc) (ih (instantiate s (.nat m)) v2 k2 hs)
            · cases h
          · cases h
        · rename_i l p
          split at h
          · rename_i hsp
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .inject hnotcv (.keep (isSettled_sound p hsp))
          · rename_i hnsp
            have hnot_sp : ¬ Settled p := fun hs => hnsp hs.isSettled_eq_true
            split at h
            · rename_i vp kp hp
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .inject hnotcv (.eval hnot_sp (ih p vp kp hp))
            · cases h
        · rename_i sc arms
          split at h
          · rename_i l p k1 hsc
            split at h
            · rename_i arm_l body hfind
              have hl : arm_l = l := by simpa using List.find?_some hfind
              subst hl
              split at h
              · rename_i v2 k2 hbody
                rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
                exact .case (ih sc (.inject arm_l p) k1 hsc) hfind (ih (instantiate body p) v2 k2 hbody)
              · cases h
            · cases h
          · cases h
        · rename_i c x y
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hx
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .ifTrue (ih c (.boolean true) k1 hc) (ih x v2 k2 hx)
            · cases h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hy
              rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
              exact .ifFalse (ih c (.boolean false) k1 hc) (ih y v2 k2 hy)
            · cases h
          · cases h
        · rename_i x
          split at h
          · rename_i v2 k2 hx
            rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
            exact .done (ih x v2 k2 hx)
          · cases h
        · cases h
/-! ## Dead-`let` Elimination in Prototype Methods (`clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper`) -/

def deadLetBind (deadExpr body : Term) : Term := .app (.lam (body.rename Nat.succ)) deadExpr
theorem instantiate_deadLet_body (body arg : Term) :
    instantiate (body.rename Nat.succ) arg = body := by rw [instantiate_eq, shift_one_cancel]
theorem steps_deadLetBind (deadExpr body : Term) : Steps (deadLetBind deadExpr body) body := by
  unfold deadLetBind
  have hstep := Step.beta (body.rename Nat.succ) deadExpr
  rw [instantiate_deadLet_body] at hstep; exact steps_one hstep
theorem ahead_deadLetBind (deadExpr body : Term) :
    Ahead (deadLetBind deadExpr body) body ∧ Ahead (.lam (deadLetBind deadExpr body)) (.lam body) :=
  ⟨Ahead.ofStepsRefl (steps_deadLetBind deadExpr body), .lam (Ahead.ofStepsRefl (steps_deadLetBind deadExpr body))⟩
theorem bEquiv_deadLetBind (deadExpr body : Term) :
    (deadLetBind deadExpr body ≈b body) ∧ (.lam (deadLetBind deadExpr body) ≈b .lam body) :=
  ⟨bequiv_of_ahead (ahead_deadLetBind deadExpr body).1, bequiv_of_ahead (ahead_deadLetBind deadExpr body).2⟩
theorem cv_deadLetBind_of_cv (deadExpr : Term) {body v : Term} {k : Nat} (h : CV body v k) :
    CV (deadLetBind deadExpr body) v (k + 2) := by
  unfold deadLetBind
  have hbody : CV (instantiate (body.rename Nat.succ) skipped) v k := by rwa [instantiate_deadLet_body]
  have happ := Run.apply (Run.value (.lam (body.rename Nat.succ))) (Run.skip deadExpr) hbody
  have heq : 0 + 1 + k + 1 = k + 2 := by omega
  rwa [heq] at happ
theorem cv_of_cv_deadLetBind {deadExpr body v : Term} {k_unpruned : Nat}
    (h : CV (deadLetBind deadExpr body) v k_unpruned) :
    ∃ k_pruned, CV body v k_pruned ∧ k_pruned < k_unpruned ∧ (¬ Settled deadExpr → k_pruned + 2 ≤ k_unpruned) := by
  unfold deadLetBind at h
  cases h with
  | value hv => exact absurd hv app_not_ready
  | applySpec hf _ => obtain ⟨heq, _⟩ := cv_lam hf; cases heq
  | @apply _ _ _ b x _ k1 k2 k3 hf hb hbody =>
    obtain ⟨hb_eq, rfl⟩ := cv_lam hf
    simp only [Term.lam.injEq] at hb_eq; subst hb_eq; rw [instantiate_deadLet_body] at hbody
    refine ⟨k3, hbody, by omega, fun hns => ?_⟩
    rcases bind_of_unsettled hns hb with ⟨_, rfl⟩ | ⟨j, _, rfl⟩ <;> omega
theorem clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper (deadExpr body : Term) :
    (deadLetBind deadExpr body ≈b body) ∧ (.lam (deadLetBind deadExpr body) ≈b .lam body) ∧
    (∀ o : Observation, Halts (deadLetBind deadExpr body) o ↔ Halts body o) ∧
    (∀ v k, CV body v k → CV (deadLetBind deadExpr body) v (k + 2) ∧ k < k + 2) ∧
    (∀ v k_unpruned, CV (deadLetBind deadExpr body) v k_unpruned →
      ∃ k_pruned, CV body v k_pruned ∧ k_pruned < k_unpruned ∧ (¬ Settled deadExpr → k_pruned + 2 ≤ k_unpruned)) ∧
    evalClairvoyantMinCost 2 (deadLetBind (.binary .add (.nat 10) (.nat 20)) (.nat 42)) = some (.nat 42, 2) ∧
    evalClairvoyantMinCost 2 (.nat 42) = some (.nat 42, 0) := by
  have hbeq := bEquiv_deadLetBind deadExpr body
  have hns : ¬ Settled (.binary .add (.nat 10) (.nat 20)) := fun h => by cases h with | value hv => cases hv
  have hev1 : evalClairvoyantMinCost 2 (deadLetBind (.binary .add (.nat 10) (.nat 20)) (.nat 42)) = some (.nat 42, 2) := by
    simpa [deadLetBind, Term.rename] using (evalClairvoyant_skip_unused_arg_saves_cost (.binary .add (.nat 10) (.nat 20)) hns 1).1
  exact ⟨hbeq.1, hbeq.2, fun o => hbeq.1.sameRuns.halts o,
    fun v k hcv => ⟨cv_deadLetBind_of_cv deadExpr hcv, by omega⟩,
    fun v k_unpruned hcv => cv_of_cv_deadLetBind hcv,
    hev1, (evalClairvoyantMinCost_value_sound (.nat 42) 2).1⟩

@[simp] theorem deadLetBind_nat (deadExpr : Term) (n : Nat) :
    deadLetBind deadExpr (.nat n) = .app (.lam (.nat n)) deadExpr := by simp [deadLetBind, Term.rename]
@[simp] theorem evalClairvoyantMinCost_nat (fuel n : Nat) :
    evalClairvoyantMinCost fuel (.nat n) = some (.nat n, 0) := (evalClairvoyantMinCost_value_sound (.nat n) fuel).1
@[simp] theorem evalClairvoyantMinCost_id_nat (fuel n : Nat) :
    evalClairvoyantMinCost (fuel + 1) (.app (.lam (.bound 0)) (.nat n)) = some (.nat n, 1) := by
  have hinst : ∀ x, instantiate (.bound 0) x = x := fun _ => by simp [instantiate, Term.substitute]
  have hskip : evalClairvoyantWithHint .full fuel skipped = none := by cases fuel <;> rfl
  have hlam : evalClairvoyantWithHint .full fuel (.lam (.bound 0)) = some (.lam (.bound 0), 0) :=
    (evalClairvoyantMinCost_value_sound (.lam (.bound 0)) fuel).1
  have hnat : evalClairvoyantWithHint .full fuel (.nat n) = some (.nat n, 0) :=
    (evalClairvoyantMinCost_value_sound (.nat n) fuel).1
  conv => lhs; unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp [isCValue, isSettled, hlam, hinst, hnat, hskip, pickMinCost]
@[simp] theorem evalClairvoyantMinCost_nested_id_nat (fuel n : Nat) :
    evalClairvoyantMinCost (fuel + 2) (.app (.lam (.bound 0)) (.app (.lam (.bound 0)) (.nat n))) = some (.nat n, 3) := by
  have hinst : ∀ x, instantiate (.bound 0) x = x := fun _ => by simp [instantiate, Term.substitute]
  have hskip : evalClairvoyantWithHint .full (fuel + 1) skipped = none := rfl
  have hlam : evalClairvoyantWithHint .full (fuel + 1) (.lam (.bound 0)) = some (.lam (.bound 0), 0) :=
    (evalClairvoyantMinCost_value_sound (.lam (.bound 0)) (fuel + 1)).1
  have hnat : evalClairvoyantWithHint .full (fuel + 1) (.nat n) = some (.nat n, 0) :=
    (evalClairvoyantMinCost_value_sound (.nat n) (fuel + 1)).1
  have hinner : evalClairvoyantWithHint .full (fuel + 1) (.app (.lam (.bound 0)) (.nat n)) =
      some (.nat n, 1) := evalClairvoyantMinCost_id_nat fuel n
  conv => lhs; unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp [isCValue, isSettled, hlam, hinst, hnat, hskip, hinner, pickMinCost]
@[simp] theorem evalClairvoyantMinCost_nested_id_nat_four (n : Nat) :
    evalClairvoyantMinCost 4 (.app (.lam (.bound 0)) (.app (.lam (.bound 0)) (.nat n))) = some (.nat n, 3) :=
  evalClairvoyantMinCost_nested_id_nat 2 n
@[simp] theorem evalClairvoyantMinCost_skip_const_add (fuel c a b : Nat) :
    evalClairvoyantMinCost (fuel + 1) (.app (.lam (.nat c)) (.binary .add (.nat a) (.nat b))) = some (.nat c, 2) := by
  have hinst : ∀ x, instantiate (.nat c) x = .nat c := fun _ => by simp [instantiate, Term.substitute]
  have hlam : evalClairvoyantWithHint .full fuel (.lam (.nat c)) = some (.lam (.nat c), 0) :=
    (evalClairvoyantMinCost_value_sound (.lam (.nat c)) fuel).1
  have hnat : evalClairvoyantWithHint .full fuel (.nat c) = some (.nat c, 0) :=
    (evalClairvoyantMinCost_value_sound (.nat c) fuel).1
  conv => lhs; unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp only [isCValue, isSettled, Bool.false_eq_true, ↓reduceIte, hlam, hinst, hnat]
  cases evalClairvoyantWithHint .full fuel (.binary .add (.nat a) (.nat b)) with
  | none => rfl
  | some r =>
    obtain ⟨va, ka⟩ := r; simp only [pickMinCost]; split
    · rename_i hle; have hka : ka = 0 := by omega
      subst hka; rfl
    · rfl
@[simp] theorem evalClairvoyantMinCost_skip_const_add_four (c a b : Nat) :
    evalClairvoyantMinCost 4 (.app (.lam (.nat c)) (.binary .add (.nat a) (.nat b))) = some (.nat c, 2) :=
  evalClairvoyantMinCost_skip_const_add 3 c a b
end Obend.Equiv
end
