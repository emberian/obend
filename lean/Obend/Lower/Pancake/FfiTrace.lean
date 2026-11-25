module
public import Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.PanSem

public section
namespace Obend.Lower.Pancake

set_option autoImplicit false

/-- Actual PanSem FFI events, including calls which return an error status. -/
def events {θ : Type} (s : PanState θ) : List String := s.ffi.io_events.map IOEvent.name

def CommandTrace (c : PStmt) (names : List String) : Prop :=
  ∀ {θ : Type} (s : PanState θ),
    ((evaluate c s).1 = .normal → events (evaluate c s).2 = events s ++ names) ∧
    (evaluate c s).1 ≠ .continue_ ∧
    (evaluate c s).1 ≠ .break_ ∧
    ∀ w : Word, (evaluate c s).1 = .ret (.word w) → w = 0

theorem seq_trace {a b : PStmt} {left right : List String}
    (ha : CommandTrace a left) (hb : CommandTrace b right) :
    CommandTrace (.seq a b) (left ++ right) := by
  intro θ s
  rw [evaluate_seq]
  dsimp only
  split
  · rename_i normal
    have eq : (evaluate a s).1 = .normal := eq_of_beq normal
    obtain ⟨rest, hnc, hnb, early⟩ := hb (evaluate a s).2
    exact ⟨fun h => by rw [rest h, (ha s).1 eq, List.append_assoc], hnc, hnb, early⟩
  · exact ⟨fun h => by simp_all, (ha s).2.1, (ha s).2.2.1, (ha s).2.2.2⟩

theorem skip_trace : CommandTrace .skip [] := by
  intro θ s
  simp [evaluate_skip]

theorem store_trace (a b : PExp) : CommandTrace (.store a b) [] := by
  intro θ s
  rw [evaluate_store]
  repeat' split <;> simp [events]

theorem storeByte_trace (a b : PExp) : CommandTrace (.storeByte a b) [] := by
  intro θ s
  rw [evaluate_storeByte]
  repeat' split <;> simp [events]

theorem status_trace (cond : PExp) : CommandTrace (.ite cond (.ret (.const 0)) .skip) [] := by
  intro θ s
  rw [evaluate_ite]
  repeat' split <;> simp [evaluate_ret, evaluate_skip, events]

private theorem ffi_events {θ : Type} {ffi final : FFIState θ} {name : String} {conf input output : List Byte}
    (named : name ≠ "") (success : call_FFI ffi name conf input = .FFI_return final output) :
    final.io_events.map IOEvent.name = ffi.io_events.map IOEvent.name ++ [name] := by
  simp [call_FFI, named] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  simp

/-- A returning named foreign call appends exactly one observation and cannot
return directly from its enclosing Pancake function. -/
theorem extCall_trace (name : String) (named : name ≠ "") (a b c d : PExp) :
    CommandTrace (.extCall name a b c d) [name] := by
  intro θ s
  rw [evaluate_eq_step]
  simp only [evaluateStep]
  split
  · split
    · split
      · rename_i final output good
        exact ⟨fun _ => ffi_events named good, by simp, by simp, by simp⟩
      · simp
    · simp
  · simp

theorem positive_return_trace {θ : Type} (s f : PanState θ) (c : PStmt) (g : PExp) (names : List String)
    (w : Word) (positive : w ≠ 0) (contract : CommandTrace c names)
    (run : evaluate (.seq c (.ret g)) s = (.ret (.word w), f)) : events f = events s ++ names := by
  rw [evaluate_seq] at run
  dsimp only at run
  split at run
  next norm =>
    have recorded := (contract s).1 (eq_of_beq norm)
    rw [evaluate_ret] at run
    repeat' split at run <;> try contradiction
    all_goals cases run <;> exact recorded
  next => exact False.elim (positive ((contract s).2.2.2 w (congrArg Prod.fst run)))

/-- General FFI-trace invariant for whole Pancake procedures:
every non-returning exit (`normal`/`continue`/`break`) leaves `events` unchanged,
and every positive return (`w ≠ 0`) satisfies `P (events s) (events f)`. -/
def PositiveTrace (c : PStmt) (P : List String → List String → Prop) : Prop :=
  ∀ {θ : Type} (s : PanState θ),
    ((evaluate c s).1 = .normal ∨ (evaluate c s).1 = .continue_ ∨ (evaluate c s).1 = .break_ →
      events (evaluate c s).2 = events s) ∧
    ∀ w : Word, w ≠ 0 → (evaluate c s).1 = .ret (.word w) → P (events s) (events (evaluate c s).2)

theorem positiveTrace_skip (P : List String → List String → Prop) : PositiveTrace .skip P := by
  intro θ s
  simp [evaluate_skip]

theorem positiveTrace_break (P : List String → List String → Prop) : PositiveTrace .break_ P := by
  intro θ s
  rw [evaluate_eq_step]
  simp [evaluateStep]

theorem positiveTrace_assign (P : List String → List String → Prop) (vk : VarKind) (v : String) (e : PExp) :
    PositiveTrace (.assign vk v e) P := by
  intro θ s
  rw [evaluate_assign]
  cases eval s e with
  | none => simp
  | some val =>
    dsimp only
    split
    · cases vk <;> simp [events, set_kvar, set_var, set_global]
    · simp

theorem positiveTrace_store (P : List String → List String → Prop) (a b : PExp) :
    PositiveTrace (.store a b) P := by
  intro θ s
  rw [evaluate_store]
  repeat' split <;> simp [events]

theorem positiveTrace_storeByte (P : List String → List String → Prop) (a b : PExp) :
    PositiveTrace (.storeByte a b) P := by
  intro θ s
  rw [evaluate_storeByte]
  repeat' split <;> simp [events]

theorem positiveTrace_failZero (P : List String → List String → Prop) (cond : PExp) :
    PositiveTrace (.ite cond (.ret (.const 0)) .skip) P := by
  intro θ s
  rw [evaluate_ite]
  cases eval s cond with
  | none => simp
  | some val =>
    cases val with
    | rstruct _ => simp
    | word w =>
      dsimp only
      split
      · refine ⟨fun h => by simp [evaluate_ret] at h, fun w' hw' hret => ?_⟩
        simp [evaluate_ret] at hret
        exact False.elim (hw' hret.symm)
      · simp [evaluate_skip]

theorem positiveTrace_seq_ret {c : PStmt} {g : PExp} {names : List String}
    {P : List String → List String → Prop}
    (hc : CommandTrace c names) (hP : ∀ evs, P evs (evs ++ names)) :
    PositiveTrace (.seq c (.ret g)) P := by
  intro θ s
  constructor
  · intro h
    rw [evaluate_seq] at h
    dsimp only at h
    split at h
    · rw [evaluate_ret] at h
      cases he : eval (evaluate c s).2 g with
      | none => simp [he] at h
      | some val =>
        simp only [he] at h
        split at h <;> simp at h
    · rename_i hne
      have hnot : (evaluate c s).1 ≠ .normal := fun hn => by simp [hn] at hne
      rcases h with h | h | h
      · exact False.elim (hnot h)
      · exact False.elim ((hc s).2.1 h)
      · exact False.elim ((hc s).2.2.1 h)
  · intro w hw hr
    have hev := positive_return_trace s (evaluate (.seq c (.ret g)) s).2 c g names w hw hc
      (by cases h : evaluate (.seq c (.ret g)) s with | mk r f => rw [h] at hr; simp at hr; rw [hr])
    rw [hev]
    exact hP (events s)

theorem positiveTrace_dec {v : String} {sh : Shape} {e : PExp} {body : PStmt}
    {P : List String → List String → Prop} (hb : PositiveTrace body P) :
    PositiveTrace (.dec v sh e body) P := by
  intro θ s
  rw [evaluate_dec]
  cases eval s e with
  | none => simp
  | some val =>
    dsimp only
    split
    · obtain ⟨hnorm, hret⟩ := hb { s with locals := FUPDATE s.locals (v, val) }
      exact ⟨fun h => hnorm h, fun w hw hr => hret w hw hr⟩
    · simp

theorem positiveTrace_ite {cond : PExp} {a b : PStmt} {P : List String → List String → Prop}
    (ha : PositiveTrace a P) (hb : PositiveTrace b P) :
    PositiveTrace (.ite cond a b) P := by
  intro θ s
  rw [evaluate_ite]
  cases eval s cond with
  | none => simp
  | some val =>
    cases val with
    | rstruct _ => simp
    | word w =>
      dsimp only
      split
      · exact ha s
      · exact hb s

theorem positiveTrace_seq {a b : PStmt} {P : List String → List String → Prop}
    (ha : PositiveTrace a P) (hb : PositiveTrace b P) :
    PositiveTrace (.seq a b) P := by
  intro θ s
  rw [evaluate_seq]
  dsimp only
  split
  · rename_i hnorm
    have hn : (evaluate a s).1 = .normal := eq_of_beq hnorm
    have hev : events (evaluate a s).2 = events s := (ha s).1 (.inl hn)
    obtain ⟨hbn, hbr⟩ := hb (evaluate a s).2
    exact ⟨fun h => (hbn h).trans hev, fun w hw hr => hev ▸ hbr w hw hr⟩
  · exact ⟨fun h => (ha s).1 h, (ha s).2⟩

theorem positiveTrace_while {cond : PExp} {body : PStmt} {P : List String → List String → Prop}
    (hb : PositiveTrace body P) : PositiveTrace (.while_ cond body) P := by
  suffices ∀ (fuel : Nat) {θ : Type} (s : PanState θ), s.clock ≤ fuel →
      ((evaluate (.while_ cond body) s).1 = .normal ∨
       (evaluate (.while_ cond body) s).1 = .continue_ ∨
       (evaluate (.while_ cond body) s).1 = .break_ →
        events (evaluate (.while_ cond body) s).2 = events s) ∧
      ∀ w : Word, w ≠ 0 → (evaluate (.while_ cond body) s).1 = .ret (.word w) →
        P (events s) (events (evaluate (.while_ cond body) s).2) by
    intro θ s
    exact this s.clock s (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro θ s hclk
    have h0 : s.clock = 0 := by omega
    rw [evaluate_while]
    cases eval s cond with
    | none => simp
    | some val =>
      cases val with
      | rstruct _ => simp
      | word w =>
        dsimp only
        split
        · simp [h0]
        · simp
  | succ k ih =>
    intro θ s hclk
    rw [evaluate_while]
    cases eval s cond with
    | none => simp
    | some val =>
      cases val with
      | rstruct _ => simp
      | word w =>
        dsimp only
        split
        · split
          · simp
          · rename_i hnz
            have hpos : 0 < s.clock := by
              cases hc : s.clock with
              | zero => simp [hc] at hnz
              | succ _ => omega
            have hdec : (dec_clock s).clock ≤ k := by simp [dec_clock]; omega
            have hle := evaluate_clock_le body (dec_clock s)
            have hbd := hb (dec_clock s)
            have hevDec : events (dec_clock s) = events s := rfl
            cases hr : (evaluate body (dec_clock s)).1 with
            | normal =>
              have hev1 : events (evaluate body (dec_clock s)).2 = events s :=
                (hbd.1 (.inl hr)).trans hevDec
              obtain ⟨hn, hret⟩ := ih (evaluate body (dec_clock s)).2 (Nat.le_trans hle hdec)
              exact ⟨fun h => (hn h).trans hev1, fun w' hw' hr' => hev1 ▸ hret w' hw' hr'⟩
            | continue_ =>
              have hev1 : events (evaluate body (dec_clock s)).2 = events s :=
                (hbd.1 (.inr (.inl hr))).trans hevDec
              obtain ⟨hn, hret⟩ := ih (evaluate body (dec_clock s)).2 (Nat.le_trans hle hdec)
              exact ⟨fun h => (hn h).trans hev1, fun w' hw' hr' => hev1 ▸ hret w' hw' hr'⟩
            | break_ =>
              have hev1 : events (evaluate body (dec_clock s)).2 = events s :=
                (hbd.1 (.inr (.inr hr))).trans hevDec
              exact ⟨fun _ => hev1, fun _ _ h => by cases h⟩
            | ret rv =>
              refine ⟨fun h => (by rcases h with h | h | h <;> cases h), fun w' hw' hr' => ?_⟩
              cases hr'
              exact hevDec ▸ hbd.2 w' hw' hr
            | TimeOut | Error | finalFFI _ =>
              exact ⟨fun h => (by rcases h with h | h | h <;> cases h), fun _ _ h => (by cases h)⟩
        · simp

/-- Unfolding equation for `decCall` matching `PanSem.evaluate_call`. -/
theorem evaluate_decCall {θ : Type} (v : String) (sh : Shape) (fname : String)
    (args : List PExp) (cont : PStmt) (s : PanState θ) :
    evaluate (.decCall v sh fname args cont) s =
      match evalList s args, s.code fname with
      | some argVals, some (params, calleeBody) =>
        if shapesMatch params argVals then
          if s.clock == 0 then
            (.TimeOut, empty_locals s)
          else
            let calleeSt := { dec_clock s with locals := mkCalleeLocals params argVals }
            let r1 := evaluate calleeBody calleeSt
            match r1.1 with
            | .ret retVal =>
              if sh == shape_of retVal then
                let contSt := { r1.2 with locals := FUPDATE s.locals (v, retVal) }
                let r2 := evaluate cont contSt
                (r2.1, { r2.2 with locals := res_var r2.2.locals (v, s.locals v) })
              else
                (.Error, r1.2)
            | .TimeOut       => (.TimeOut, empty_locals r1.2)
            | .finalFFI ev   => (.finalFFI ev, empty_locals r1.2)
            | .Error         => (.Error, r1.2)
            | .normal        => (.Error, r1.2)
            | .break_        => (.Error, r1.2)
            | .continue_     => (.Error, r1.2)
        else
          (.Error, s)
      | _, _ => (.Error, s) := by
  conv => lhs; rw [evaluate_eq_step]
  simp only [evaluateStep]
  cases ha : evalList s args with
  | none => rfl
  | some argVals =>
    cases hc : s.code fname with
    | none => rfl
    | some entry =>
      obtain ⟨params, calleeBody⟩ := entry
      dsimp only
      split
      · split
        · rfl
        · rw [fix_clock_evaluate_of_clock_le (dec_clock s)
            { dec_clock s with locals := mkCalleeLocals params argVals } calleeBody (Nat.le_refl _)]
          cases h1 : evaluate calleeBody { dec_clock s with locals := mkCalleeLocals params argVals } with
          | mk res1 st1 =>
            cases res1 with
            | ret retVal => rfl
            | TimeOut | finalFFI _ | Error | normal | break_ | continue_ => rfl
      · rfl

/-- Syntactic predicate witnessing that a Pancake statement contains zero FFI or function calls. -/
def NoFfiStmt : PStmt → Bool
  | .skip | .assign .. | .store .. | .storeByte .. | .break_ | .continue_ | .ret _ | .tick | .annot .. => true
  | .dec _ _ _ b => NoFfiStmt b
  | .seq a b => NoFfiStmt a && NoFfiStmt b
  | .ite _ a b => NoFfiStmt a && NoFfiStmt b
  | .while_ _ b => NoFfiStmt b
  | .call .. | .decCall .. | .extCall .. => false
termination_by structural s => s

private theorem evaluateStep_noFfi_preserves_ffi {θ : Type}
    (stepLower : PStmt → PanState θ → PanResult × PanState θ)
    (hLower : ∀ p (st : PanState θ), NoFfiStmt p = true → (stepLower p st).2.ffi = st.ffi) :
    ∀ (stmt : PStmt) (s : PanState θ), NoFfiStmt stmt = true →
      (evaluateStep stepLower stmt s).2.ffi = s.ffi := by
  intro stmt
  induction stmt with
  | skip | break_ | continue_ => intro s _; rfl
  | annot _ _ => intro s _; rfl
  | tick => intro s _; simp only [evaluateStep]; split <;> rfl
  | assign vk _ _ =>
    intro s _; simp only [evaluateStep]
    cases eval s _ with
    | none => rfl
    | some _ => dsimp only; split; cases vk <;> rfl; rfl
  | store _ _ =>
    intro s _; simp only [evaluateStep]
    cases eval s _ with
    | none => rfl
    | some dv =>
      cases dv with
      | rstruct _ => rfl
      | word addr =>
        cases eval s _ with
        | none => rfl
        | some sv => dsimp only; cases mem_stores addr (flatten sv) s.memaddrs s.memory <;> rfl
  | storeByte _ _ =>
    intro s _; simp only [evaluateStep]
    cases eval s _ with
    | none => rfl
    | some dv =>
      cases dv with
      | rstruct _ => rfl
      | word addr =>
        cases eval s _ with
        | none => rfl
        | some sv =>
          cases sv with
          | rstruct _ => rfl
          | word w => dsimp only; cases mem_store_byte s.memory s.memaddrs s.be addr (BitVec.setWidth 8 w) <;> rfl
  | ret _ =>
    intro s _; simp only [evaluateStep]
    cases eval s _ with
    | none => rfl
    | some _ => dsimp only; split <;> rfl
  | dec _ _ _ body ih =>
    intro s hnf; simp only [evaluateStep]
    cases eval s _ with
    | none => rfl
    | some val => dsimp only; split; exact ih _ hnf; rfl
  | seq a b iha ihb =>
    intro s hnf
    simp only [NoFfiStmt, Bool.and_eq_true] at hnf
    simp only [evaluateStep]
    have ha : (fix_clock s (evaluateStep stepLower a s)).2.ffi = s.ffi := iha s hnf.1
    split
    · exact (ihb _ hnf.2).trans ha
    · exact ha
  | ite _ a b iha ihb =>
    intro s hnf
    simp only [NoFfiStmt, Bool.and_eq_true] at hnf
    simp only [evaluateStep]
    cases eval s _ with
    | none => rfl
    | some val =>
      cases val with
      | rstruct _ => rfl
      | word _ => dsimp only; split; exact iha s hnf.1; exact ihb s hnf.2
  | while_ cond body _ =>
    intro s hnf
    simp only [NoFfiStmt] at hnf
    simp only [evaluateStep]
    cases eval s cond with
    | none => rfl
    | some val =>
      cases val with
      | rstruct _ => rfl
      | word _ =>
        dsimp only; split
        · split
          · rfl
          · have hb : (fix_clock (dec_clock s) (stepLower body (dec_clock s))).2.ffi = s.ffi :=
              hLower body (dec_clock s) hnf
            cases hr : (fix_clock (dec_clock s) (stepLower body (dec_clock s))).1 with
            | normal | continue_ => exact (hLower (.while_ cond body) _ hnf).trans hb
            | break_ | ret _ | TimeOut | Error | finalFFI _ => exact hb
        · rfl
  | call _ _ _ => intro _ hnf; cases hnf
  | decCall _ _ _ _ _ => intro _ hnf; cases hnf
  | extCall _ _ _ _ _ => intro _ hnf; cases hnf

private theorem evaluateFuel_noFfi_preserves_ffi {θ : Type} (fuel : Nat) :
    ∀ (stmt : PStmt) (s : PanState θ), NoFfiStmt stmt = true →
      (evaluateFuel fuel stmt s).2.ffi = s.ffi := by
  induction fuel with
  | zero => exact evaluateStep_noFfi_preserves_ffi _ (fun _ _ _ => rfl)
  | succ f ih => exact evaluateStep_noFfi_preserves_ffi _ ih

theorem noFfi_preserves_events {stmt : PStmt} (hnf : NoFfiStmt stmt = true)
    {θ : Type} (s : PanState θ) : events (evaluate stmt s).2 = events s := by
  unfold events evaluate
  rw [evaluateFuel_noFfi_preserves_ffi s.clock stmt s hnf]

end Obend.Lower.Pancake
