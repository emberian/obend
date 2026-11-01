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

2. **Universal Symbolic Saturating-Mode Soundness (`lower_sub_sat_rtl_sound`,
   `lower_to_rtl_sat_sound`, `lower_sat_rtl_agrees_with_source`)**:
   - For ALL `a, b < 2^64`, `lowerT (.natBin .sub (.lit a) (.lit b))` compiles via `compileTermSat`
     to an `RtlExpr` whose hardware evaluation equals `BitVec.ofNat 64 (a - b)`, agreeing with
     `SSteps` and `Core4` `Evaluates`.
   - For ANY `e : LExpr`, `compileTermSat_sound` lifts directly to `lowerT e` (`lower_to_rtl_sat_sound`).

3. **Verified 4-Stage Pipeline (`lean_double_to_book_to_rtl`, `smallUnderflow_wrapping_book_diverges`,
   `lean_small_to_book_to_rtl`)**:
   - Proves end-to-end 4-stage agreement (`SSteps` → `Core4.Evaluates` → `Leaf.Book.Halts` →
     `compileBookToRtl` / `compileBookToRtlSat` + `checkRtlModule` + `evalModuleOutputs`) for both
     `doubleLExpr` (`fun n => n + n`) and `smallUnderflowLExpr`
     (`fun n => if n ≤ 2 then (n - 3) + 1 else n - 3`), where the taken branch itself underflows at
     `n = 0, 2` (diverging under wrapping `compileBookToRtl` yet agreeing under `compileBookToRtlSat`).
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

/-! ## 2. Universal Symbolic Soundness (`lower_sub_sat_rtl_sound`, `lower_to_rtl_sat_sound`) -/

/-- **Universal Symbolic Soundness of Lowered `Nat` Subtraction (`lower_sub_sat_rtl_sound`)**:
For all `a, b < 2^64`, the `LExpr` subtraction `.natBin .sub (.lit a) (.lit b)`:
1. reduces in `SSteps` to `.lit (a - b)`,
2. evaluates in `Core4` (`lowerT`) to `.nat (a - b)`, and
3. compiles via `compileTermSat` to an `RtlExpr` that evaluates in `evalRtlExpr` to
   `BitVec.ofNat 64 (a - b)` under ANY port/wire/register assignment. -/
theorem lower_sub_sat_rtl_sound
    (inputs wires regs : Nat → BitVec 64) {a b : Nat}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    let src := LExpr.natBin .sub (.lit a) (.lit b)
    SSteps src (.lit (a - b)) ∧
    Evaluates (lowerT src) (.nat (a - b)) ∧
    ∃ rtl : RtlExpr,
      compileTermSat [] [] 0 [] (lowerT src) = some rtl ∧
      evalRtlExpr inputs wires regs rtl = BitVec.ofNat 64 (a - b) := by
  intro src
  have hstep : SSteps src (.lit (a - b)) := .next (.binLit .sub a b) (.refl _)
  refine ⟨hstep, by simpa [lowerT] using lower_sound_nat hstep, ?_⟩
  let rtl : RtlExpr :=
    .mux (.alu .ult (.const (BitVec.ofNat 64 a)) (.const (BitVec.ofNat 64 b)))
      (.const 0#64)
      (.alu .sub (.const (BitVec.ofNat 64 a)) (.const (BitVec.ofNat 64 b)))
  have hcomp : compileTermSat [] [] 0 [] (lowerT src) = some rtl := by
    simp [src, lowerT, NatOp.prim, compileTermSat, compilePrimSat, rtl]
  refine ⟨rtl, hcomp, ?_⟩
  have hsound := compileTermSat_sound inputs wires regs [] [] (lowerT src) 0 [] rtl hcomp
  simp only [src, lowerT, NatOp.prim, List.map_nil, evalTermHwSat,
    evalPrimHwSat_subtract_eq_ofNat_sub ha hb, Option.some.injEq] at hsound
  exact hsound.symm

/-- **General Structural Bridge (`lower_to_rtl_sat_sound`)**: for any `e : LExpr`, if `lowerT e`
compiles via `compileTermSat` to `rtl`, then `evalRtlExpr` on `rtl` matches `evalTermHwSat` on
`lowerT e`. -/
theorem lower_to_rtl_sat_sound
    (inputs wires regs : Nat → BitVec 64)
    (slots : List String)
    (slotBodies : List RtlExpr)
    (e : LExpr)
    (selfDepth : Nat) (varEnv : List RtlExpr) (rtl : RtlExpr)
    (h : compileTermSat slots slotBodies selfDepth varEnv (lowerT e) = some rtl) :
    evalTermHwSat slots slotBodies inputs wires regs selfDepth
      (varEnv.map (evalRtlExpr inputs wires regs)) (lowerT e) =
      some (evalRtlExpr inputs wires regs rtl) :=
  compileTermSat_sound inputs wires regs slots slotBodies (lowerT e) selfDepth varEnv rtl h

/-- **End-to-End Agreement of `SSteps`, `Core4`, and `compileTermSat` (`lower_sat_rtl_agrees_with_source`)**:
for any closed `e : LExpr` and `n : Nat` with `SSteps e (.lit n)` and `compileTermSat [] [] 0 [] (lowerT e) = some rtl`,
if `evalTermHwSat` on `lowerT e` agrees with `BitVec.ofNat 64 n`, then:
1. `Evaluates (lowerT e) (.nat n)`, and
2. `evalRtlExpr inputs wires regs rtl = BitVec.ofNat 64 n`. -/
theorem lower_sat_rtl_agrees_with_source
    (inputs wires regs : Nat → BitVec 64)
    {e : LExpr} {n : Nat} {rtl : RtlExpr}
    (hstep : SSteps e (.lit n))
    (hcomp : compileTermSat [] [] 0 [] (lowerT e) = some rtl)
    (hhw : evalTermHwSat [] [] inputs wires regs 0 [] (lowerT e) = some (BitVec.ofNat 64 n)) :
    Evaluates (lowerT e) (.nat n) ∧
    evalRtlExpr inputs wires regs rtl = BitVec.ofNat 64 n := by
  refine ⟨by simpa [lowerT] using lower_sound_nat hstep, ?_⟩
  have hsound := lower_to_rtl_sat_sound inputs wires regs [] [] e 0 [] rtl hcomp
  simp only [List.map_nil, hhw, Option.some.injEq] at hsound
  exact hsound.symm

/-! ## 3. End-to-End 4-Stage Theorems (`Lean-lite` → `Core4` → `Leaf.Book` → `RtlModule`) -/

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

/-- `fun n : Nat => if n ≤ 2 then (n - 3) + 1 else n - 3` in `LExpr`:
exercises `boolRec`, `NatOp.ble`, and underflowing `NatOp.sub` (`n - 3` at `n = 0, 2`) inside the
taken branch itself. -/
def smallUnderflowLExpr : LExpr :=
  .lam .natural
    (.boolRec .natural
      (.natBin .sub (.bvar 0) (.lit 3))
      (.natBin .add (.natBin .sub (.bvar 0) (.lit 3)) (.lit 1))
      (.natBin .ble (.bvar 0) (.lit 2)))

theorem smallUnderflow_runs_2 : SSteps (.app smallUnderflowLExpr (.lit 2)) (.lit 1) := by
  refine .next (SStep.beta .natural _ (.lit 2)) ?_
  have hinst :
      (LExpr.boolRec .natural
        (.natBin .sub (.bvar 0) (.lit 3))
        (.natBin .add (.natBin .sub (.bvar 0) (.lit 3)) (.lit 1))
        (.natBin .ble (.bvar 0) (.lit 2))).inst (.lit 2) =
      .boolRec .natural
        (.natBin .sub (.lit 2) (.lit 3))
        (.natBin .add (.natBin .sub (.lit 2) (.lit 3)) (.lit 1))
        (.natBin .ble (.lit 2) (.lit 2)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (SStep.boolRecMajor .natural _ _ (SStep.binLit .ble 2 2)) ?_
  refine .next (SStep.boolRecTrue .natural _ _) ?_
  refine .next (SStep.binLeft .add (.lit 1) (SStep.binLit .sub 2 3)) ?_
  exact .next (SStep.binLit .add 0 1) (.refl _)

theorem smallUnderflow_runs_10 : SSteps (.app smallUnderflowLExpr (.lit 10)) (.lit 7) := by
  refine .next (SStep.beta .natural _ (.lit 10)) ?_
  have hinst :
      (LExpr.boolRec .natural
        (.natBin .sub (.bvar 0) (.lit 3))
        (.natBin .add (.natBin .sub (.bvar 0) (.lit 3)) (.lit 1))
        (.natBin .ble (.bvar 0) (.lit 2))).inst (.lit 10) =
      .boolRec .natural
        (.natBin .sub (.lit 10) (.lit 3))
        (.natBin .add (.natBin .sub (.lit 10) (.lit 3)) (.lit 1))
        (.natBin .ble (.lit 10) (.lit 2)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (SStep.boolRecMajor .natural _ _ (SStep.binLit .ble 10 2)) ?_
  refine .next (SStep.boolRecFalse .natural _ _) ?_
  exact .next (SStep.binLit .sub 10 3) (.refl _)

/-- **Wrapping `compileBookToRtl` Diverges on `smallUnderflowLExpr` at `n = 2`**:
Wrapping `compileBookToRtl` produces `2#64 - 3#64 + 1#64 = 0#64 ≠ 1#64`! -/
theorem smallUnderflow_wrapping_book_diverges :
    let C := leanComposition "small" (lowerT smallUnderflowLExpr)
    let B := emit C
    (match compileBookToRtl "lean_small_wrap_rtl" B with
     | some m =>
       evalModuleOutputs m (fun _ => 2#64) (fun _ => 0#64) == [("out_small", 1#64)]
     | none => true) = false := by
  decide +kernel

/-- **4-Stage Saturating Verified Chain (`lean_small_to_book_to_rtl`)**:
Under `compileBookToRtlSat`, `smallUnderflowLExpr` (`if n ≤ 2 then (n - 3) + 1 else n - 3`) agrees
across all 4 stages (`SSteps`, `Core4.Evaluates`, `Leaf.Book.Halts`, and `compileBookToRtlSat`
hardware simulation) at both the underflowing input `n = 2` (`= 1`) and the non-underflowing input
`n = 10` (`= 7`), as well as `n = 0` (`= 1`) and `n = 3` (`= 0`)! -/
theorem lean_small_to_book_to_rtl :
    let C := leanComposition "small" (lowerT smallUnderflowLExpr)
    let B := emit C
    SSteps (.app smallUnderflowLExpr (.lit 2)) (.lit 1) ∧
    SSteps (.app smallUnderflowLExpr (.lit 10)) (.lit 7) ∧
    Evaluates (.app (lowerT smallUnderflowLExpr) (.nat 2)) (.nat 1) ∧
    Evaluates (.app (lowerT smallUnderflowLExpr) (.nat 10)) (.nat 7) ∧
    Halts (.app (.get B.link "small") (.nat 2)) (.natural 1) ∧
    Halts (.app (.get B.link "small") (.nat 10)) (.natural 7) ∧
    (match compileBookToRtlSat "lean_small_sat_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 0#64) (fun _ => 0#64) == [("out_small", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 2#64) (fun _ => 0#64) == [("out_small", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) == [("out_small", 0#64)]) &&
       (evalModuleOutputs m (fun _ => 10#64) (fun _ => 0#64) == [("out_small", 7#64)])
     | none => false) = true := by
  refine ⟨smallUnderflow_runs_2, smallUnderflow_runs_10, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lowerT] using lower_sound_nat smallUnderflow_runs_2
  · simpa [lowerT] using lower_sound_nat smallUnderflow_runs_10
  · exact lean_to_book "small" smallUnderflowLExpr 2 1 (by decide +kernel) smallUnderflow_runs_2
  · exact lean_to_book "small" smallUnderflowLExpr 10 7 (by decide +kernel) smallUnderflow_runs_10
  · decide +kernel

end Obend.Lower
end
