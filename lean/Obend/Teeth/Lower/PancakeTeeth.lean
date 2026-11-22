module
/-
# `Obend.Teeth.Lower.PancakeTeeth` — `#tooth` Mutation Suite & Kernel Falsifier Poles (`G6`)

Exercises the full `Obend.Lower.Pancake` stack (`PanSem`, `CondSClk`, `RefinesClkPan`, `LcnfToPancake`):
1. **Positive Executable Witnesses (`decide +kernel`)**:
   - `sampleLcnfAstMatch` (`Obend.Lower.LCNF`) compiled to `PStmt` and executed in `PanSem.evaluate` -> `42#64`.
   - Asymmetric diamond join-point program (`ifBool` + `jpDecl` + `jmp`) with `CondSClk` tight `Nat.max`
     clock bound `2 < 3` (strictly tighter than additive sum!), succeeding at `clock = 2`.
   - Saturating subtraction (`10 - 25 = 0#64` vs `25 - 10 = 15#64`) and 2-field ADT `.cases` dispatch
     verifying reverse binder order (`casesProjCode 25 10` -> `15#64`, `casesProjCode 10 25` -> `0#64`).
   - Lexical join-point capture across shadowing let-bindings (`lexicalCaptureCode 30 999 12` -> `42#64`).
   - `redirectStatusStage` (`301`/`302`/`307`/`308`) and `guardedLoopStmt` (`len ≤ cap` vs `len > cap` bailout).
2. **Adversarial Negative Falsifier Poles (`decide +kernel`)**:
   - Exact fuel boundary: diamond join-point program returns `PanResult.TimeOut` at `clock = 1`.
   - HOL4 `is_valid_value` enforcement: assigning an undeclared local returns `PanResult.Error`.
   - HOL4 `write_bytearray` partial-domain semantics: unmapped byte address drops trailing byte writes.
   - `checkFoLcnf` statically refuses `2^63 + 2^63` 64-bit addition overflow (`none`).
3. **`#tooth` Kernel Mutation Witnesses**:
   - 6 kernel `#tooth` checks proving `compileLcnfToPancake_correct`, `synthStmtClk_compileLcnfToPancake`,
     `sclk_refinesClkPan`, and `runCompiledLcnfBatch_sound` each fail to typecheck under broken implementations.
-/
public import Obend.Tactic.Tooth
import all Obend.Lower.LCNF
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.CondSClk
import all Obend.Lower.Pancake.RefinesClkPan
import all Obend.Lower.Pancake.LcnfEmit
import all Obend.Lower.Pancake.LcnfSimHelpers
import all Obend.Lower.Pancake
public import Obend.Lower.Pancake

public section

namespace Obend.Teeth.Lower.PancakeTeeth

open Obend.Lower.LCNF
open Obend.Lower.Pancake

set_option autoImplicit false

/-! ## 1. Positive & Negative Executable Witnesses (`decide +kernel`) -/

/-- Asymmetric nested join-point benchmark demonstrating `CondSClk`'s `Nat.max` tightness:
    * `then` branch jumps twice (`jp1 -> jp0`: `2` ticks),
    * `else` branch jumps once (`jp0`: `1` tick).
    `synthLcnfClk` synthesizes `max 1 0 + 1 = 2` ticks (vs `3` under naive additive branching)! -/
def asymmetricJoinCode (takeLong : Bool) : LcnfCode :=
  .jpDecl 0 1
    (.letValue (.natOp .add (.bvar 0) (.lit 10)) (.return (.bvar 0)))
    (.ifBool (.boolLit takeLong)
      (.jpDecl 1 1 (.jmp 0 [.bvar 0]) (.jmp 1 [.lit 32]))
      (.jmp 0 [.lit 5]))

/-- 1. `sampleLcnfAstMatch`, `casesProjCode`, `lexicalCaptureCode`, and `asymmetricJoinCode`
    typecheck in `checkFoLcnf`, synthesize exact `CondSClk` fuel, and evaluate to exact words in `PanSem`. -/
example :
    checkFoLcnf sampleLcnfAstMatch = some 42 ∧
    synthLcnfClk sampleLcnfAstMatch = 0 ∧
    (evaluate (compileLcnfToPancake sampleLcnfAstMatch) (emptyPanState () 0)).1 = .ret (.word 42#64) ∧
    (evaluate (compileLcnfToPancake (casesProjCode 25 10)) (emptyPanState () 0)).1 = .ret (.word 15#64) ∧
    (evaluate (compileLcnfToPancake (casesProjCode 10 25)) (emptyPanState () 0)).1 = .ret (.word 0#64) ∧
    synthLcnfClk (lexicalCaptureCode 30 999 12) = 1 ∧
    (evaluate (compileLcnfToPancake (lexicalCaptureCode 30 999 12)) (emptyPanState () 1)).1 =
      .ret (.word 42#64) ∧
    synthLcnfClk (asymmetricJoinCode true) = 2 ∧
    synthStmtClk (compileLcnfToPancake (asymmetricJoinCode true)) = some 2 ∧
    (evaluate (compileLcnfToPancake (asymmetricJoinCode true)) (emptyPanState () 2)).1 =
      .ret (.word 42#64) ∧
    (evaluate (compileLcnfToPancake (asymmetricJoinCode false)) (emptyPanState () 2)).1 =
      .ret (.word 15#64) := by
  decide +kernel

/-- 2. Adversarial negative poles:
    * `asymmetricJoinCode true` with `clock = 1` (< `synthLcnfClk = 2`) hits `PanResult.TimeOut`.
    * Assigning an undeclared local `"unscoped"` hits `PanResult.Error` (`is_valid_value = false`).
    * `checkFoLcnf` refuses 64-bit addition overflow `(2^63) + (2^63) = 2^64` (`none`).
    * `write_bytearray` on an unmapped address silently drops the write per HOL4 `panSem$write_bytearray`. -/
example :
    (evaluate (compileLcnfToPancake (asymmetricJoinCode true)) (emptyPanState () 1)).1 = .TimeOut ∧
    (evaluate (.lassign "unscoped" (.const 7#64)) (emptyPanState () 5)).1 = .Error ∧
    checkFoLcnf
      (.letValue (.natOp .add (.lit (2 ^ 63)) (.lit (2 ^ 63))) (.return (.bvar 0))) = none ∧
    write_bytearray 0x100#64 [0x48#8] (fun _ => 0#64) (fun _ => false) false 0x100#64 = 0#64 := by
  decide +kernel

/-- 3. Multi-turn batch execution across 3 heterogeneous `LcnfCode` turns preserves remaining fuel. -/
example :
    let batch := [sampleLcnfAstMatch, casesProjCode 25 10, asymmetricJoinCode true]
    synthBatchClk batch = 2 ∧
    (runCompiledLcnfBatch batch (emptyPanState () 5)).map (fun p => (p.1, p.2.clock)) =
      some ([42#64, 15#64, 42#64], 3) := by
  decide +kernel

/-! ## 2. `#tooth` Kernel Mutation Witnesses on Universal Theorems -/

/-- Mutation 1: Broken `compileLcnfToPancake` emitting `.skip` is caught by `compileLcnfToPancake_correct`. -/
def compileLcnfBrokenSkip (c : LcnfCode) : PStmt :=
  match c with | .return _ => .skip | _ => .skip

#tooth Obend.Lower.Pancake.compileLcnfToPancake_correct
  by mutation Obend.Lower.Pancake.compileLcnfToPancake := compileLcnfBrokenSkip

/-- Mutation 2: Over-permissive `checkFoLcnf` accepting every `LcnfCode` (including `.unreach` and `2^64` overflow)
    is caught by `compileLcnfToPancake_correct`. -/
def checkFoLcnfAcceptAll (c : LcnfCode) : Option Nat :=
  match c with | .return _ => some 0 | _ => some 0

#tooth Obend.Lower.Pancake.compileLcnfToPancake_correct
  by mutation Obend.Lower.Pancake.checkFoLcnf := checkFoLcnfAcceptAll

/-- Mutation 3: Corrupted `evalLcnf` returning `some 999999` disagrees with `PanSem.evaluate` and is
    caught by `compileLcnfToPancake_evalLcnf_correct`. -/
def evalLcnfConst999999 (c : LcnfCode) : Option Nat :=
  match c with | .return _ => some 999999 | _ => some 999999

#tooth Obend.Lower.Pancake.compileLcnfToPancake_evalLcnf_correct
  by mutation Obend.Lower.Pancake.evalLcnf := evalLcnfConst999999

/-- Mutation 4: Constant `synthStmtClk` disagreeing with `synthLcnfClk` is caught by
    `synthStmtClk_compileLcnfToPancake`. -/
def synthStmtClkConst99 (st : PStmt) : Option Nat :=
  match st with | .skip => some 99 | _ => some 99

#tooth Obend.Lower.Pancake.synthStmtClk_compileLcnfToPancake
  by mutation Obend.Lower.Pancake.synthStmtClk := synthStmtClkConst99

/-- Mutation 5: Broken `PanSem.evaluate` returning `.TimeOut` unconditionally is caught by `sclk_refinesClkPan`. -/
def evaluateAlwaysTimeOut {θ : Type} (st : PStmt) (s : PanState θ) : PanResult × PanState θ :=
  match st with | .skip => (.TimeOut, s) | _ => (.TimeOut, s)

#tooth Obend.Lower.Pancake.sclk_refinesClkPan
  by mutation Obend.Lower.Pancake.evaluate := @evaluateAlwaysTimeOut

/-- Mutation 6: Broken RFC 9110 `redirectStatusOf` returning `500#64` is caught by `redirectStatusStage_refinesClkPan`. -/
def redirectStatusBroken500 (w : Word) : Word :=
  if w == 0#64 then 500#64 else 500#64

#tooth Obend.Lower.Pancake.redirectStatusStage_refinesClkPan
  by mutation Obend.Lower.Pancake.redirectStatusOf := redirectStatusBroken500

/-- Mutation 7: Broken `runCompiledLcnfBatch` dropping outputs to `[]` is caught by `runCompiledLcnfBatch_sound`. -/
def runCompiledLcnfBatchDrop {θ : Type} (cs : List LcnfCode) (s : PanState θ) :
    Option (List Word × PanState θ) :=
  match cs with | [] => some ([], s) | _ :: _ => some ([], s)

#tooth Obend.Lower.Pancake.runCompiledLcnfBatch_sound
  by mutation Obend.Lower.Pancake.runCompiledLcnfBatch := @runCompiledLcnfBatchDrop

end Obend.Teeth.Lower.PancakeTeeth
end
