module
/-
# Obend.Run.Core4 — an emitted Core4 activity as the runner's protocol

A Core4 activity runs to a yield, its Plan (`Data`) is extracted, the kernel answers with a response
(`Data`, resumed as a closed term), and it runs to the next yield: the turns `Spec.Preview.runTurns`
executes and `Core.Interaction` gives as the reference tree (`node_of_chain_vis`: a machine yield is
the reference `Vis` of every state in a chain with it). Here the same turns become an open protocol:
one operation per Plan, one response per `Data`, `turn` the machine's own run, `unfold n` the
protocol of the activity to depth `n`. What a Plan requires, spends and establishes is a `Spec` over
Plans the DEPLOYMENT supplies (`Core4` Plans carry no authority of their own); the runner enforces it
at dispatch exactly as for any protocol.

Theorems: `Obend.Run.Proofs.Core4`. The gaps this leaves (depth, ticks, response typing, choice points)
are closed by the adapter over it, `Obend.Run.Adapter`.
-/
public import Obend.Run.Runner
public import Obend.Core.Data
public import Obend.Core.MachineFast
public import Obend.Core.Proofs.Force
public import Obend.Leaf.BytecodeRegisterJit
public section

namespace Obend.Run.Core4

open Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data

mutual
/-- Decided equality of Plans (`Data` derives only `Repr`). -/
def decData : (a b : Data) → Decidable (a = b)
  | .natural x, .natural y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .natural _, .boolean _ => isFalse (by intro h; cases h)
  | .natural _, .label _ => isFalse (by intro h; cases h)
  | .natural _, .record _ => isFalse (by intro h; cases h)
  | .natural _, .variant _ _ => isFalse (by intro h; cases h)
  | .boolean _, .natural _ => isFalse (by intro h; cases h)
  | .boolean x, .boolean y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .boolean _, .label _ => isFalse (by intro h; cases h)
  | .boolean _, .record _ => isFalse (by intro h; cases h)
  | .boolean _, .variant _ _ => isFalse (by intro h; cases h)
  | .label _, .natural _ => isFalse (by intro h; cases h)
  | .label _, .boolean _ => isFalse (by intro h; cases h)
  | .label x, .label y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .label _, .record _ => isFalse (by intro h; cases h)
  | .label _, .variant _ _ => isFalse (by intro h; cases h)
  | .record _, .natural _ => isFalse (by intro h; cases h)
  | .record _, .boolean _ => isFalse (by intro h; cases h)
  | .record _, .label _ => isFalse (by intro h; cases h)
  | .record fs, .record gs => match decFields fs gs with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .record _, .variant _ _ => isFalse (by intro h; cases h)
  | .variant _ _, .natural _ => isFalse (by intro h; cases h)
  | .variant _ _, .boolean _ => isFalse (by intro h; cases h)
  | .variant _ _, .label _ => isFalse (by intro h; cases h)
  | .variant _ _, .record _ => isFalse (by intro h; cases h)
  | .variant l p, .variant m q =>
    if hl : l = m then
      match decData p q with
      | isTrue h => isTrue (by rw [hl, h])
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hl rfl)
def decFields : (fs gs : List (String × Data)) → Decidable (fs = gs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | (n, a) :: fs, (m, b) :: gs =>
    if hn : n = m then
      match decData a b, decFields fs gs with
      | isTrue h, isTrue h' => isTrue (by rw [hn, h, h'])
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hn rfl)
end

instance : DecidableEq Data := decData

/-- One operation per Plan; the response is `Data`; the protocol has one index. -/
@[expose] def planSig : Sig Unit where
  Op := fun _ => Data
  Resp := fun _ => Data
  next := fun _ _ => ()

instance : DecidableEq (Σ i, planSig.Op i) := inferInstanceAs (DecidableEq (Σ _ : Unit, Data))

/-- A Core4 activity's protocol has no holes: its plan is the program. -/
@[expose] def NoHole : Unit → Type := fun _ => Empty

instance : ∀ i, DecidableEq (NoHole i) := fun _ => inferInstanceAs (DecidableEq Empty)

/-- How the activity's protocol ends. -/
inductive Stop where
  /-- the machine finished, suspended, diverged or refused within the turn -/
  | ended (o : Outcome)
  /-- it yielded a Plan that is not Data within the budget -/
  | unextractable (f : Failure)
  /-- the yielded state did not take the response (never: `turn_vis_resumes`) -/
  | unresumable
  /-- the unfolding's depth -/
  | depth
  /-- a yielded Plan that is a choice among these alternatives, none chosen at its position yet
  (the adapter's frontier, `Obend.Run.Adapter`) -/
  | choice (alts : List Data)

/-- One turn of the machine: a yield with its extracted Plan and the state to resume, or a stop. -/
inductive Turn where
  | vis (plan : Data) (yielded : State)
  | stop (s : Stop)

/-- One turn under the machine's limits, a tick bound per turn, and the extraction budget. -/
def turn (L : Limits) (ticks : Nat) (budget : Budget) (s : State) : Turn :=
  match runBounded L ticks s with
  | .yielded _ y =>
    match yieldedPlan L budget y with
    | .ok r => .vis r.value r.state
    | .error (f, _) => .stop (.unextractable f)
  | o => .stop (.ended o)

abbrev P := Prot planSig NoHole (fun _ => Stop) ()

/-- The activity at `s` as a protocol, to depth `n`: each yield is a call of its Plan whose
continuation, for every response, is the activity resumed with it. -/
def unfold (L : Limits) (ticks : Nat) (budget : Budget) : Nat → State → P
  | 0, _ => .ret .depth
  | n + 1, s =>
    match turn L ticks budget s with
    | .vis p y => .call (S := planSig) p fun r =>
      match resume r.term y with
      | some s' => unfold L ticks budget n s'
      | none => .ret .unresumable
    | .stop x => .ret x

/-- The open object of an activity: the protocol, nothing to choose, hypotheses `Γ`, tokens `Δ`,
obligation bound `Φ`. -/
def activity {Tok Fact Ob : Type} (L : Limits) (ticks : Nat) (budget : Budget) (n : Nat) (s : State)
    (Γ : List Fact) (Δ : List Tok) (Φ : List Ob) : Open planSig NoHole (fun _ => Stop) Tok Fact Ob () where
  template := unfold L ticks budget n s
  Ω := fun _ h => nomatch h
  σ := fun _ _ => none
  Γ := Γ
  Δ := Δ
  Q := fun _ _ => True
  Φ := Φ
  hist := ⟨[], none⟩

/-- The machine's own run of turns: from `s`, yield Plan `p`, be resumed with `r`, go on; the
transcript is the list of (Plan, response) pairs and the state it ends in. Stated of the machine,
not of the runner. -/
inductive Transcript (L : Limits) (ticks : Nat) (budget : Budget) :
    State → Trace planSig → State → Prop
  | nil (s : State) : Transcript L ticks budget s [] s
  | turn {s y s' s'' : State} {p r : Data} {t : Trace planSig} :
      turn L ticks budget s = .vis p y → resume r.term y = some s' →
      Transcript L ticks budget s' t s'' →
      Transcript L ticks budget s (⟨(), p, r⟩ :: t) s''

/-- The runner's events for a transcript: each Plan dispatched, then its response. -/
def eventsOf {V : Type} : Trace planSig → List (Event planSig NoHole (fun _ => Stop) Fact V)
  | [] => []
  | e :: t => .dispatch ⟨e.1, e.2.1⟩ :: .respond e :: eventsOf t

/-! ## Fast `MachineFast` & `BytecodeRegisterJit` Welds (`turnFast`, `execRunCore4Fast`, `execCore4LoopFast`) -/

/-- Fast single-turn `Core4` execution over `MachineFast.runBoundedFast` (stack-depth counter + pre-state capacity). -/
def turnFast (L : Limits) (ticks : Nat) (budget : Budget) (s : State) : Turn :=
  match Obend.Core.MachineFast.runBoundedFast L ticks s with
  | .yielded _ y =>
    match yieldedPlan L budget y with
    | .ok r => .vis r.value r.state
    | .error (f, _) => .stop (.unextractable f)
  | o => .stop (.ended o)

theorem turnFast_eq_turn (L : Limits) (ticks : Nat) (budget : Budget) (s : State) :
    turnFast L ticks budget s = turn L ticks budget s := by
  simp [turnFast, turn, ← Obend.Core.MachineFast.runBounded_eq_fast]

@[csimp] theorem turn_eq_turnFast : @turn = @turnFast :=
  funext fun L => funext fun ticks => funext fun budget => funext fun s =>
    (turnFast_eq_turn L ticks budget s).symm

private theorem turn_vis_resumes_core {L : Limits} {ticks : Nat} {budget : Budget}
    {s y : State} {p : Data} (h : turn L ticks budget s = .vis p y)
    (t : Obend.Core.Term.Term) : ∃ s', resume t y = some s' := by
  unfold turn at h
  split at h
  · rename_i y₀ _
    cases hf : yieldedPlan L budget y₀ with
    | error e => rw [hf] at h; obtain ⟨_, _⟩ := e; cases h
    | ok r =>
      rw [hf] at h; cases h
      have hy : ∃ a, y₀.control = .yielded a := by
        unfold yieldedPlan yieldedPlanWith at hf
        split at hf
        · exact ⟨_, ‹_›⟩
        · simp at hf
      obtain ⟨a, ha⟩ := hy
      have hc := (Obend.Core.Collect.yieldedPlanWith_control hf).1
      refine ⟨{ r.state with control := .evaluate t [] }, ?_⟩
      unfold resume; rw [hc, ha]
  · cases h

/-- Closure-free multi-turn `Core4` fast runner accumulating answered `(Plan, Data)` entries in an
    unboxed/contiguous `Array` via `Array.push` instead of heap-allocated `Prot` continuations. -/
private def execRunCore4FastLoop (L : Limits) (ticks : Nat) (budget : Budget)
    (respondFn : Data → Data) :
    Nat → State → Array (Entry planSig) → Array (Entry planSig) × State × Stop
  | 0, s, acc => (acc, s, .depth)
  | n + 1, s, acc =>
    match turnFast L ticks budget s with
    | .stop x => (acc, s, x)
    | .vis p y =>
      let r := respondFn p
      match resume r.term y with
      | some s' => execRunCore4FastLoop L ticks budget respondFn n s' (acc.push ⟨(), p, r⟩)
      | none => (acc, y, .unresumable)

/-- Execute up to `depth` `Core4` protocol turns directly via `turnFast` and `Array.push`. -/
def execRunCore4Fast (L : Limits) (ticks : Nat) (budget : Budget)
    (respondFn : Data → Data) (depth : Nat) (s : State) :
    Array (Entry planSig) × State × Stop :=
  execRunCore4FastLoop L ticks budget respondFn depth s #[]

private theorem execRunCore4FastLoop_spec (L : Limits) (ticks : Nat) (budget : Budget)
    (respondFn : Data → Data) :
    ∀ (n : Nat) (s : State) (acc : Array (Entry planSig)),
      ∃ suf : Trace planSig,
        (execRunCore4FastLoop L ticks budget respondFn n s acc).1.toList = acc.toList ++ suf ∧
        suf.length ≤ n ∧
        Transcript L ticks budget s suf
          (execRunCore4FastLoop L ticks budget respondFn n s acc).2.1 ∧
        unfold L ticks budget (n - suf.length)
          (execRunCore4FastLoop L ticks budget respondFn n s acc).2.1 =
          .ret (execRunCore4FastLoop L ticks budget respondFn n s acc).2.2
  | 0, s, acc => ⟨[], by simp [execRunCore4FastLoop], Nat.le_refl 0, .nil s, rfl⟩
  | n + 1, s, acc => by
    simp only [execRunCore4FastLoop]
    cases htFast : turnFast L ticks budget s with
    | stop x =>
      have ht : turn L ticks budget s = .stop x := by rwa [← turnFast_eq_turn]
      exact ⟨[], by simp, Nat.zero_le _, .nil s, by simp [unfold, ht]⟩
    | vis p y =>
      have ht : turn L ticks budget s = .vis p y := by rwa [← turnFast_eq_turn]
      dsimp only
      obtain ⟨s₁, hres⟩ := turn_vis_resumes_core ht (respondFn p).term
      simp only [hres]
      obtain ⟨suf, hList, hLen, hTr, hUnf⟩ :=
        execRunCore4FastLoop_spec L ticks budget respondFn n s₁ (acc.push ⟨(), p, respondFn p⟩)
      refine ⟨⟨(), p, respondFn p⟩ :: suf, ?_, by simp; omega, .turn ht hres hTr, ?_⟩
      · rw [hList, Array.toList_push, List.append_assoc]; rfl
      · simpa [List.length_cons, Nat.succ_sub_succ_eq_sub] using hUnf

/-- **Refinement Theorem (`runCore4Fast_eq_spec`)**:
    `execRunCore4Fast` realizes an exact `Core4.Transcript` of length `≤ depth` and terminates in the
    exact residual `Stop` state prescribed by `unfold`. -/
theorem runCore4Fast_eq_spec (L : Limits) (ticks : Nat) (budget : Budget)
    (respondFn : Data → Data) (depth : Nat) (s : State) :
    let res := execRunCore4Fast L ticks budget respondFn depth s
    res.1.size ≤ depth ∧
    Transcript L ticks budget s res.1.toList res.2.1 ∧
    unfold L ticks budget (depth - res.1.size) res.2.1 = .ret res.2.2 := by
  intro res
  obtain ⟨suf, hList, hLen, hTr, hUnf⟩ :=
    execRunCore4FastLoop_spec L ticks budget respondFn depth s #[]
  simp only [List.nil_append] at hList
  have hSz : res.1.size = suf.length := by
    rw [← Array.length_toList]; exact congrArg List.length hList
  refine ⟨hSz ▸ hLen, ?_, hSz ▸ hUnf⟩
  change Transcript L ticks budget s (execRunCore4FastLoop L ticks budget respondFn depth s #[]).1.toList _
  rwa [hList]

/-- Specialize dictionary-passing `Core4` loop step `stepTerm` and execute `n` iterations directly
    on the unboxed `Array UInt64` `BytecodeRegisterJit` VM, returning `Data.natural`. -/
def execCore4LoopFast (passes maxN maxAcc : Nat) (stepTerm : Obend.Core.Term.Term)
    (n acc0 : Nat) : Option Data :=
  match Obend.Leaf.BytecodeRegisterJit.specializeAndCompileLoop passes maxN maxAcc stepTerm with
  | some (code, maxRegs, iterFuel) =>
    let regs := #[UInt64.ofNat acc0, UInt64.ofNat n] ++ Array.replicate maxRegs 0
    match Obend.Leaf.BytecodeRegisterJit.execBytecode code regs (n * iterFuel + 2) with
    | some out => some (.natural out.toNat)
    | none => none
  | none => none

/-- **Soundness of `execCore4LoopFast` (`execCore4LoopFast_sound`)**:
    Agrees identically with `Core4` small-step `EvaluatesCountdownLoop` on all bounded inputs. -/
theorem execCore4LoopFast_sound
    (passes maxN maxAcc : Nat) (stepTerm : Obend.Core.Term.Term)
    (code : Array Obend.Leaf.BytecodeRegisterJit.ByteInstr) (maxRegs iterFuel : Nat)
    (hLoop : Obend.Leaf.BytecodeRegisterJit.specializeAndCompileLoop passes maxN maxAcc stepTerm =
      some (code, maxRegs, iterFuel))
    {n acc0 finalAcc : Nat} (hn : n ≤ maxN) (hAcclt : finalAcc < 2 ^ 64)
    (hRun : Obend.Leaf.BytecodeRegisterJit.CountdownBounded maxAcc stepTerm n acc0 finalAcc) :
    Obend.Leaf.BytecodeRegisterJit.EvaluatesCountdownLoop stepTerm n acc0 finalAcc ∧
    execCore4LoopFast passes maxN maxAcc stepTerm n acc0 = some (.natural finalAcc) := by
  obtain ⟨hEv, hToNat, hExec⟩ :=
    Obend.Leaf.BytecodeRegisterJit.specializeAndCompileLoop_sound
      passes maxN maxAcc stepTerm code maxRegs iterFuel hLoop hn hAcclt hRun
  refine ⟨hEv, ?_⟩
  simp only [execCore4LoopFast, hLoop]
  have hEx0 := hExec (#[UInt64.ofNat acc0, UInt64.ofNat n] ++ Array.replicate maxRegs 0) 0
    (by simp [Array.size_append])
    (by simp [Array.getElem?_append])
    (by simp [Array.getElem?_append])
  simp only [Nat.add_zero] at hEx0
  simp [hEx0, hToNat]

end Obend.Run.Core4

end
