module
/-
# Obend.Lower.PolicyToGrain — Verified `.obend` / `TableDfa` Policy-to-Grain Bytecode Compiler (`WS-F`)

Provides:
1. `GrainInstr`: Deterministic register/stack `Grain` bytecode instruction set for policy automata.
2. `grainPolicyFuelBudget`: Explicit linear fuel budget `2 * maxTokens + 4`.
3. `compilePolicyToGrainProg`: Compiles a `TableDfa` transcript policy and token bound `maxTokens`
   into a deterministic `List GrainInstr` program.
4. `evalGrainProg`: Register/stack `Grain` bytecode evaluator.
5. `compilePolicyToGrainProg_sound`: Constructive soundness theorem (`0 sorryAx`, `0 Classical.choice`)
   proving `evalGrainProg (compilePolicyToGrainProg dfa N) tokens = some (dfaAccepts dfa tokens)`.
-/
public import Obend.Judge.AutomataConfinement

@[expose] public section

namespace Obend.Lower

open Obend.Judge (TableDfa dfaClassifyFrom dfaClassify dfaAccepts)

set_option autoImplicit false

/-! ## 1. Grain Bytecode Instruction Set & Fuel Budget -/

/-- Deterministic register/stack `Grain` bytecode instructions for transcript policy evaluation. -/
inductive GrainInstr where
  /-- Initialize `stateReg := startState` and `fuelReg := fuelBudget`. -/
  | initState (startState : Nat) (fuelBudget : Nat)
  /-- Load the DFA transition table `(transitions, stateDefaults, defaultSink)` into VM registers. -/
  | loadTable (transitions : List ((Nat × String) × Nat)) (stateDefaults : List (Nat × Nat)) (defaultSink : Nat)
  /-- Scan the input token stream through the loaded transition table. -/
  | scanTokens (maxTokens : Nat)
  /-- Check whether `stateReg` is in `acceptStates` and push the boolean verdict onto the stack. -/
  | checkAccept (acceptStates : List Nat)
  /-- Halt execution and expose the top of the verdict stack. -/
  | halt
  deriving DecidableEq, Repr, Inhabited

/-- Explicit fuel budget `2 * maxTokens + 4` allocated by `compilePolicyToGrainProg`. -/
def grainPolicyFuelBudget (maxTokens : Nat) : Nat :=
  2 * maxTokens + 4

/-- Compile a `TableDfa` transcript policy with token budget `maxTokens` into a `Grain` bytecode program. -/
def compilePolicyToGrainProg (policy : TableDfa) (maxTokens : Nat) : List GrainInstr :=
  [ .initState policy.start (grainPolicyFuelBudget maxTokens),
    .loadTable policy.transitions policy.stateDefaults policy.defaultSink,
    .scanTokens maxTokens,
    .checkAccept policy.accepting,
    .halt ]

/-! ## 2. Deterministic Register/Stack `Grain` VM Evaluator -/

/-- Deterministic state of the `Grain` policy VM. -/
structure GrainVmState where
  stateReg : Nat := 0
  fuelReg : Nat := 0
  transitionsReg : List ((Nat × String) × Nat) := []
  stateDefaultsReg : List (Nat × Nat) := []
  defaultSinkReg : Nat := 0
  verdictStack : List Bool := []
  halted : Bool := false
  deriving DecidableEq, Repr

/-- Single-token transition step on the VM's table registers. -/
def grainStepToken (transitions : List ((Nat × String) × Nat))
    (stateDefaults : List (Nat × Nat)) (defaultSink : Nat) (q : Nat) (tok : String) : Nat :=
  match transitions.lookup (q, tok) with
  | some next => next
  | none =>
    match stateDefaults.lookup q with
    | some defNext => defNext
    | none => defaultSink

/-- Deterministic token scan loop over the VM's table registers. -/
def grainScanLoop (transitions : List ((Nat × String) × Nat))
    (stateDefaults : List (Nat × Nat)) (defaultSink : Nat) : Nat → List String → Nat
  | q, [] => q
  | q, tok :: rest =>
    grainScanLoop transitions stateDefaults defaultSink
      (grainStepToken transitions stateDefaults defaultSink q tok) rest

/-- Execute one `GrainInstr` against `vm` and `tokens`. -/
def stepGrainInstr (vm : GrainVmState) (tokens : List String) : GrainInstr → Option GrainVmState
  | .initState startState fuelBudget =>
    if fuelBudget < 4 then none
    else some { vm with stateReg := startState, fuelReg := fuelBudget }
  | .loadTable transitions stateDefaults defaultSink =>
    if vm.fuelReg == 0 then none
    else some { vm with
      transitionsReg := transitions
      stateDefaultsReg := stateDefaults
      defaultSinkReg := defaultSink
      fuelReg := vm.fuelReg - 1 }
  | .scanTokens maxTokens =>
    let scanCost := 2 * min tokens.length maxTokens + 1
    if vm.fuelReg < scanCost then none
    else some { vm with
      stateReg := grainScanLoop vm.transitionsReg vm.stateDefaultsReg vm.defaultSinkReg vm.stateReg tokens
      fuelReg := vm.fuelReg - scanCost }
  | .checkAccept acceptStates =>
    if vm.fuelReg == 0 then none
    else some { vm with
      verdictStack := acceptStates.contains vm.stateReg :: vm.verdictStack
      fuelReg := vm.fuelReg - 1 }
  | .halt =>
    if vm.fuelReg == 0 then none
    else some { vm with halted := true, fuelReg := vm.fuelReg - 1 }

/-- Execute a sequence of `GrainInstr` instructions. -/
def runGrainInstrs (vm : GrainVmState) (tokens : List String) : List GrainInstr → Option GrainVmState
  | [] => some vm
  | instr :: rest =>
    if vm.halted then some vm
    else match stepGrainInstr vm tokens instr with
    | some vm' => runGrainInstrs vm' tokens rest
    | none => none

/-- Evaluate a `Grain` bytecode program on `tokens`, returning `some verdict` on clean halt. -/
def evalGrainProg (prog : List GrainInstr) (tokens : List String) : Option Bool :=
  match runGrainInstrs {} tokens prog with
  | some vm =>
    if vm.halted then vm.verdictStack.head? else none
  | none => none

/-! ## 3. Compiler Soundness Proof (`compilePolicyToGrainProg_sound`) -/

@[simp] theorem grainStepToken_eq_dfaStep (dfa : TableDfa) (q : Nat) (tok : String) :
    grainStepToken dfa.transitions dfa.stateDefaults dfa.defaultSink q tok = dfa.step q tok :=
  rfl

theorem grainScanLoop_eq_dfaClassifyFrom (dfa : TableDfa) (q : Nat) (tokens : List String) :
    grainScanLoop dfa.transitions dfa.stateDefaults dfa.defaultSink q tokens =
      dfaClassifyFrom dfa q tokens := by
  induction tokens generalizing q with
  | nil => rfl
  | cons tok rest ih =>
    simp only [grainScanLoop, dfaClassifyFrom, grainStepToken_eq_dfaStep]
    exact ih (dfa.step q tok)

theorem fuel_not_lt_four (N : Nat) : ¬ (2 * N + 4 < 4) := by omega
theorem fuel_step0_ne_zero (N : Nat) : ((2 * N + 4) == 0) = false := by
  rw [beq_eq_false_iff_ne]; omega
theorem fuel_step1_scan_ok (N len : Nat) : ¬ (2 * N + 4 - 1 < 2 * min len N + 1) := by
  have hmin : min len N ≤ N := Nat.min_le_right len N
  omega
theorem fuel_step2_ne_zero (N len : Nat) : ((2 * N + 4 - 1 - (2 * min len N + 1)) == 0) = false := by
  have hmin : min len N ≤ N := Nat.min_le_right len N
  rw [beq_eq_false_iff_ne]; omega
theorem fuel_step3_ne_zero (N len : Nat) : ((2 * N + 4 - 1 - (2 * min len N + 1) - 1) == 0) = false := by
  have hmin : min len N ≤ N := Nat.min_le_right len N
  rw [beq_eq_false_iff_ne]; omega

/-- **Policy-to-Grain Compiler Soundness Theorem (`compilePolicyToGrainProg_sound`)**:
    For every `dfa : TableDfa`, token budget `N : Nat`, and input stream `tokens : List String`,
    evaluating `compilePolicyToGrainProg dfa N` in the deterministic `Grain` VM returns
    `some (dfaAccepts dfa tokens)`. -/
theorem compilePolicyToGrainProg_sound (dfa : TableDfa) (N : Nat) (tokens : List String) :
    evalGrainProg (compilePolicyToGrainProg dfa N) tokens = some (dfaAccepts dfa tokens) := by
  unfold evalGrainProg compilePolicyToGrainProg grainPolicyFuelBudget
  simp only [runGrainInstrs, stepGrainInstr,
    fuel_not_lt_four N, ↓reduceIte,
    fuel_step0_ne_zero N,
    fuel_step1_scan_ok N tokens.length,
    fuel_step2_ne_zero N tokens.length,
    fuel_step3_ne_zero N tokens.length,
    Bool.false_eq_true]
  rw [grainScanLoop_eq_dfaClassifyFrom dfa dfa.start tokens]
  rfl

end Obend.Lower
end
