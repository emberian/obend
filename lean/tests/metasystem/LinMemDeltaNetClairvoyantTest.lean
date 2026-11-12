module
/-
# LinMemDeltaNetClairvoyantTest — linear memory, commuting interactions and Δ-nets, the memo oracle

Teeth and instances for `Obend.SymbolicZk.LinMem`, `Obend.Hardware.HvmConfluence` and
`Obend.Equiv.ClairvoyantBook`.

Each `#tooth` replays the stored proof of a universal theorem with one check of the implementation
replaced, and reports the declaration at which the kernel refuses it. The examples are instances:
traces the linear-memory checker accepts and refuses, the Δ-net run of `(λid. id id 42) (λx. x)`
beside `Hvm.Lower`'s refusal of the same term, and a memo table for `let x = Ω(0) in 42` beside a
forged row `Ω(0) = 42`.
-/
public import Obend.Tactic.Tooth
public import Obend.SymbolicZk.LinMem
public import Obend.Hardware.HvmConfluence
public import Obend.Equiv.ClairvoyantBook
import all Obend.SymbolicZk.LinMem
import all Obend.Hardware.HvmConfluence
import all Obend.Equiv.ClairvoyantBook

public section

namespace Obend.Tests.Metasystem.LinMemDeltaNetClairvoyantTest

open Obend.Core.Term
open Obend.SymbolicZk
open Obend.Hardware.Hvm
open Obend.Hardware.Delta
open Obend.Equiv

set_option autoImplicit false

/-! ## 1. Teeth -/

-- A supply whose ids are not checked may hold one id twice: the matching loses injectivity.
#tooth linmem_sound by
  mutation checkStrictlyIncreasingAllocId := fun _ => true

-- Ids compared with `≤` let two cells share an id.
#tooth linmem_sound by
  mutation allocLt := fun a b => decide (a.allocId ≤ b.allocId)

-- Events not checked against births may read a cell before it is written.
#tooth linmem_sound by
  mutation checkCausalExec := fun _ => true

-- Replicators compared by level alone annihilate when their deltas differ.
#tooth rep_interacts_iff_equal by
  mutation replicatorsAnnihilate := fun l1 _ l2 _ => l1 == l2

-- Deltas compared against their negation: the two copies of `λx. x`'s replicator no longer meet
-- as equals, and `(λid. id id n) (λx. x)` does not reach `n`.
#tooth normalize_idId by
  mutation replicatorsAnnihilate := fun l1 d1 l2 d2 => l1 == l2 && d1 == d2.map fun d => -d

-- A row allowed to rank with its callee justifies itself.
#tooth clairvoyantMemo_sound by
  mutation checkBeforeRank := fun calleeRank callerRank => decide (calleeRank ≤ callerRank)

-- A skipped binding that reads as 0 is demand the oracle said was not there.
#tooth clairvoyantMemo_sound by
  mutation skippedRead := some 0

#tooth scExpr_toCore4_clairvoyant_sound by
  mutation skippedRead := some 0

/-! ## 2. Linear memory -/

def cellA : LinCell := ⟨1, 0, 7⟩
def cellB : LinCell := ⟨2, 1, 9⟩
def cellC : LinCell := ⟨3, 2, 4⟩

/-- `A` is there at the start, `B` and `C` are produced, `A` and `B` are consumed, `C` is left. -/
def goodTrace : LinMemTrace :=
  { init := #[cellA], produced := #[cellC, cellB], consumed := #[⟨cellB, 3⟩, ⟨cellA, 1⟩],
    finalCells := #[cellC] }

/-- `A` consumed twice, paid for by dropping `B` from the final cells. -/
def doubleSpend : LinMemTrace :=
  { init := #[cellA], produced := #[cellB], consumed := #[⟨cellA, 1⟩, ⟨cellA, 2⟩],
    finalCells := #[] }

/-- `B`, born at step 1, consumed at step 1. -/
def timeTravel : LinMemTrace :=
  { init := #[cellA], produced := #[cellB], consumed := #[⟨cellB, 1⟩], finalCells := #[cellA] }

/-- Two cells under one allocation id, both accounted for. -/
def sharedId : LinMemTrace :=
  { init := #[cellA], produced := #[⟨1, 1, 8⟩], consumed := #[⟨cellA, 2⟩],
    finalCells := #[⟨1, 1, 8⟩] }

theorem goodTrace_accepted : verifyLinMemExec goodTrace = true :=
  (verifyLinMemExec_iff_spec goodTrace).2 (by decide)

theorem doubleSpend_refused : verifyLinMemExec doubleSpend = false :=
  Bool.eq_false_iff.2 fun h => absurd ((verifyLinMemExec_iff_spec doubleSpend).1 h) (by decide)

theorem timeTravel_refused : verifyLinMemExec timeTravel = false :=
  Bool.eq_false_iff.2 fun h => absurd ((verifyLinMemExec_iff_spec timeTravel).1 h) (by decide)

theorem sharedId_refused : verifyLinMemExec sharedId = false :=
  Bool.eq_false_iff.2 fun h => absurd ((verifyLinMemExec_iff_spec sharedId).1 h) (by decide)

/-- The accepted trace has its matching. -/
theorem goodTrace_matching : Nonempty (CausalMatching goodTrace) :=
  linmem_sound goodTrace goodTrace_accepted

/-- The merge sort, run. -/
theorem mergeSortCells_runs :
    mergeSortCells #[cellC, cellA, cellB] = #[cellA, cellB, cellC] := by decide +kernel

/-! ## 3. Δ-nets and the single duplicator -/

/-- `(λid. id id 42) (λx. x)` reduces to `42`. -/
theorem idId42_reduces : DSteps (compileToDeltaNet (idIdLit 42)) ⟨.lit 42, []⟩ :=
  deltaNet_idId_reduces 42

/-- Its translation: the binder of `id` is a replicator at level 1 with deltas `-1` (the function
position, level 0) and `0` (the argument position, level 1). -/
theorem idId42_binder :
    (compileToDeltaNet (idIdLit 42)).bag.getLast? =
      some (.fan (.rep 1 [-1, 0] [.var 0, .var 1]) (.var 3),
        .fan (.fan (.rep 2 [-1] [.var 4]) (.var 4)) (.var 5)) := by
  rfl

/-- The same term in Core4 is refused by `Hvm.Lower`. -/
theorem idId42_refused_by_hvmLower : ∃ e,
    toS "main" [] 0 (.app (.lam (.app (.app (.bound 0) (.bound 0)) (.nat 42))) (.lam (.bound 0)))
      (.val (.sc .nat)) 0 = .error e :=
  hvmLower_refuses_lambda_argument _ _ _ _ _ _ _

/-- The wires of that run are a valid linear memory. -/
theorem idId42_wires_linear : verifyLinMemExec (wireTrace 64 (compileToDeltaNet (idIdLit 42))) = true :=
  deltaStep_preserves_linmem 64 _ (by decide) (by decide +kernel)

/-- The run ends with no wire left: every wire of the net was consumed. -/
theorem idId42_no_wire_left (x : Nat) :
    x ∉ (wireLedger 64 (compileToDeltaNet (idIdLit 42))).live.map (·.1) := by
  rw [wireLedger_final, normalize_idId]
  simp [DCfg.vars, DTree.vars, dBagVars]

/-- Replicators of one level and different deltas have no rule. -/
theorem rep_same_level_unequal_stuck :
    deltaInteract (.rep 1 [0, 1] [.era, .era]) (.rep 1 [0, 2] [.era, .era]) = none := by
  rfl

/-- A lower replicator copies a higher one at its level plus the port's delta. -/
theorem rep_commute_shifts_level :
    deltaCommute 10 (.rep 1 [-1, 0] [.era, .lit 5]) (.rep 2 [-1] [.era]) =
      some [(.rep 1 [-1] [.var 10], .era), (.rep 2 [-1] [.var 11], .lit 5),
        (.rep 1 [-1, 0] [.var 10, .var 11], .era)] := by
  rfl

/-- Two erasures at two positions of an HVM2 bag commute. -/
theorem two_erasures_commute (root : HTree) (a b c d : HTree) :
    Steps [] ⟨root, [(.era, .con a b), (.era, .con c d)]⟩
        ⟨root, [(.era, a), (.era, b), (.era, .con c d)]⟩ ∧
      Steps [] ⟨root, [(.era, .con a b), (.era, .con c d)]⟩
        ⟨root, [(.era, .con a b), (.era, c), (.era, d)]⟩ ∧
      Steps [] ⟨root, [(.era, a), (.era, b), (.era, .con c d)]⟩
        ⟨root, [(.era, a), (.era, b), (.era, c), (.era, d)]⟩ ∧
      Steps [] ⟨root, [(.era, .con a b), (.era, c), (.era, d)]⟩
        ⟨root, [(.era, a), (.era, b), (.era, c), (.era, d)]⟩ :=
  diamond_of_disjoint (book := []) root [] [] [] (Fire.rule (a := .era) (b := .con a b) rfl)
    (Fire.rule (a := .era) (b := .con c d) rfl) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil)

/-! ## 4. The memo oracle -/

/-- `main(0) = 42` claimed with the `let` demanded and `Ω(0) = 42` as its witness. -/
def forgedDemandTable : MemoTable := { rows := #[⟨1, 0, 42, 5, []⟩, ⟨2, 0, 42, 9, [true]⟩] }

theorem forgedDemandTable_refused : verifyMemoTableExec omegaBook forgedDemandTable = false := by
  decide +kernel

/-- The forged row passes every check but `Before`: the row it looks up is itself. -/
theorem forgedTable_lookup : lookupMemoFast forgedTable 1 0 = some (42, 5) := by decide +kernel

/-- `let y = Ω(0) in 42` has the value 42 in the reference semantics, from the accepted table. -/
theorem lazyTable_row_is_fact : ∃ fuel, evalCallSpec omegaBook fuel 2 0 = some 42 :=
  clairvoyantMemo_sound omegaBook lazyTable omegaBook_wf lazyTable_accepted ⟨2, 0, 42, 1, [false]⟩
    (by decide)

/-- An unused diverging binding in Core4: `(λ_. 42) Ω` at cost 2, while `Ω` has no derivation. -/
theorem unused_omega_42 : Run .eval (.app (.lam (.nat 42)) omegaCore4) (.nat 42) 2 ∧
    ∀ k v, ¬ Run .eval omegaCore4 v k :=
  ⟨clairvoyant_let_unused_omega 42, omega_diverges⟩

/-- A replay with the bit `false` is a derivation that skips: `let y = 1 + 2 in 42`. -/
theorem lowered_skip : ∃ k,
    Run .eval ((scToCore4 (.letLazy (.add (.lit 1) (.lit 2)) (.lit 42))).substitute (envSubst []))
      (.nat 42) k :=
  scExpr_toCore4_clairvoyant_sound 0 _ [false] [] 42 [] (by decide +kernel)

/-- A replay with the bit `true` is a derivation that evaluates first: `let y = 1 + 2 in y + y`. -/
theorem lowered_demand : ∃ k,
    Run .eval ((scToCore4 (.letLazy (.add (.lit 1) (.lit 2)) (.add (.var 0) (.var 0)))).substitute
      (envSubst [])) (.nat 6) k :=
  scExpr_toCore4_clairvoyant_sound 0 _ [true] [] 6 [] (by decide +kernel)

end Obend.Tests.Metasystem.LinMemDeltaNetClairvoyantTest
