module
/-
# Obend.Lower.Proofs.Hardware — Auditing and Bridging `Lean-lite` → `Core4` → `Leaf.Book` → `Hardware.Compiler`

Formalizes the complete 4-stage chain from `Obend.Lower` (`LExpr`) through `Core4` (`Term`) and
`Obend.Leaf.Book` (`emit (leanComposition name (lowerT e))`) to `Obend.Hardware.Compiler` (`RtlModule`):

1. **The Wrapping-Subtraction Divergence (`subZeroOne_wrapping_rtl_diverges`, `wrapping_refuses_erased`)**:
   - For `subZeroOne := .natBin .sub (.lit 0) (.lit 1)` (`0 - 1 : Nat`), both the source semantics
     `SSteps` and `Core4` `Evaluates` produce `0` (`subZeroOne_source_and_core_zero`), whereas
     wrapping `Obend.Hardware.Compiler.compileTerm` produces `0xFFFFFFFFFFFFFFFF#64 = 2^64 - 1 ≠ 0#64`
     and refuses `lowerT .erased` (`box = .record []`).

2. **The Saturating-Mode Resolution (`subZeroOne_saturating_rtl_agrees`, `saturating_accepts_erased`)**:
   - Under `Obend.Hardware.Compiler.compileTermSat`, `lowerT subZeroOne` compiles to a saturating
     subtractor `(0 < 1) ? 0 : (0 - 1)` that evaluates to `0#64`, and `lowerT .erased` compiles to
     `some (.const 0#64)`.

3. **Verified 4-Stage Pipeline (`lean_double_to_book_to_rtl`)**:
   - Proves end-to-end for `doubleLExpr` (`fun n : Nat => n + n`) at `n = 21`:
     * Source reduction: `SSteps (.app doubleLExpr (.lit 21)) (.lit 42)`,
     * Core4 evaluation: `Evaluates (lowerT (.app doubleLExpr (.lit 21))) (.nat 42)`,
     * Leaf book halting (`lean_to_book`): `Halts (.app (.get (emit C).link "double") (.nat 21)) (.natural 42)`,
     * Hardware RTL synthesis & simulation: `compileBookToRtl` produces a DAG/CDC-verified `RtlModule`
       whose combinational output at `arg = 21#64` is `[("out_double", 42#64)]`.
-/
public import Obend.Lower.Proofs.Book
public import Obend.Hardware.Compiler
public import Obend.Hardware.HDL
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Hardware.HDL Obend.Hardware.Compiler
set_option autoImplicit false

/-! ## 1. The `0 - 1` Wrapping Divergence vs. Saturating Agreement -/

/-- `0 - 1 : Nat` in the `LExpr` fragment. -/
def subZeroOne : LExpr := .natBin .sub (.lit 0) (.lit 1)

/-- Both the Lean-lite source semantics (`SSteps`) and `Core4` (`Evaluates`) evaluate `0 - 1` to `0`. -/
theorem subZeroOne_source_and_core_zero :
    SSteps subZeroOne (.lit 0) ∧
    Evaluates (lowerT subZeroOne) (.nat 0) := by
  refine ⟨.next (.binLit .sub 0 1) (.refl _), ?_⟩
  simpa [subZeroOne, lowerT] using lower_sound_nat (.next (.binLit .sub 0 1) (.refl _))

/-- **Refutation of unguarded wrapping `compileTerm` on `lowerT (0 - 1)`**:
`compileTerm` compiles `lowerT subZeroOne` to `0#64 - 1#64 = 0xFFFFFFFFFFFFFFFF#64 ≠ 0#64`. -/
theorem subZeroOne_wrapping_rtl_diverges :
    ∃ e : RtlExpr,
      compileTerm [] [] 0 [] (lowerT subZeroOne) = some e ∧
      evalRtlExpr (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) e = 0xFFFFFFFFFFFFFFFF#64 ∧
      evalRtlExpr (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) e ≠ 0#64 := by
  refine ⟨.alu .sub (.const 0#64) (.const 1#64), ?_, rfl, by decide⟩
  simp [subZeroOne, lowerT, NatOp.prim, compileTerm, compilePrim]

/-- Wrapping `compileTerm` also refuses `lowerT .erased` (`box = .record []`). -/
theorem wrapping_refuses_erased :
    compileTerm [] [] 0 [] (lowerT .erased) = none := by
  simp [lowerT, box, compileTerm]

/-- **Resolution via `compileTermSat`**: saturating compilation of `lowerT subZeroOne` evaluates in
hardware (`evalRtlExpr`) to `0#64`, agreeing with `SSteps` and `Core4`! -/
theorem subZeroOne_saturating_rtl_agrees :
    ∃ e : RtlExpr,
      compileTermSat [] [] 0 [] (lowerT subZeroOne) = some e ∧
      evalRtlExpr (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) e = 0#64 := by
  refine ⟨.mux (.alu .ult (.const 0#64) (.const 1#64)) (.const 0#64) (.alu .sub (.const 0#64) (.const 1#64)), ?_, rfl⟩
  simp [subZeroOne, lowerT, NatOp.prim, compileTermSat, compilePrimSat]

/-- `compileTermSat` compiles `lowerT .erased` (`box = .record []`) to `0#64`. -/
theorem saturating_accepts_erased :
    compileTermSat [] [] 0 [] (lowerT .erased) = some (.const 0#64) := by
  simp [lowerT, box, compileTermSat]

/-! ## 2. End-to-End 4-Stage Theorem (`Lean-lite` → `Core4` → `Leaf.Book` → `RtlModule`) -/

/-- `fun n : Nat => n + n` in `LExpr`. -/
def doubleLExpr : LExpr := .lam .natural (.natBin .add (.bvar 0) (.bvar 0))

theorem doubleLExpr_runs_21 : SSteps (.app doubleLExpr (.lit 21)) (.lit 42) := by
  refine .next (.beta .natural (.natBin .add (.bvar 0) (.bvar 0)) (.lit 21)) ?_
  have hinst : (LExpr.natBin .add (.bvar 0) (.bvar 0)).inst (.lit 21) = .natBin .add (.lit 21) (.lit 21) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  exact .next (.binLit .add 21 21) (.refl _)

/-- **4-Stage Verified Chain (`lean_double_to_book_to_rtl`)**:
1. `doubleLExpr` applied to `21` reduces in `SSteps` to `42`;
2. `lowerT` applied to `21` evaluates in `Core4` to `.nat 42`;
3. `emit (leanComposition "double" (lowerT doubleLExpr))` halts on `21` with `.natural 42`;
4. `compileBookToRtl` compiles that exact `Book` to a valid `RtlModule` (`checkRtlModule = true`)
   whose hardware output at `arg = 21#64` is `[("out_double", 42#64)]`. -/
theorem lean_double_to_book_to_rtl :
    let C := leanComposition "double" (lowerT doubleLExpr)
    let B := emit C
    SSteps (.app doubleLExpr (.lit 21)) (.lit 42) ∧
    Evaluates (.app (lowerT doubleLExpr) (.nat 21)) (.nat 42) ∧
    Halts (.app (.get B.link "double") (.nat 21)) (.natural 42) ∧
    (match compileBookToRtl "lean_double_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 21#64) (fun _ => 0#64) == [("out_double", 42#64)])
     | none => false) = true := by
  refine ⟨doubleLExpr_runs_21, ?_, ?_, ?_⟩
  · simpa [lowerT] using lower_sound_nat doubleLExpr_runs_21
  · exact lean_to_book "double" doubleLExpr 21 42 (by decide +kernel) doubleLExpr_runs_21
  · decide +kernel

end Obend.Lower
end
