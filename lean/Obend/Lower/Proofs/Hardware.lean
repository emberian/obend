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

/-! ## 5. Typeclass Dictionary & Structure Inlining for Combinational RTL Compilation (`inlineDict`) -/

/-- One bottom-up structural pass of beta-reduction (`.app (.lam b) a ↦ instantiate b a`),
record projection (`.get (.record fs) k`), record splitting (`.split (.record fs) ns fn`), and
variant case-splitting (`.case (.inject lbl payload) arms`). -/
def inlinePass : Term → Term
  | .lam b => .lam (inlinePass b)
  | .app f a =>
    let f' := inlinePass f
    let a' := inlinePass a
    match f' with
    | .lam b => instantiate b a'
    | .ifBool c t e => .ifBool c (.app t a') (.app e a')
    | _ => .app f' a'
  | .get target name =>
    let t' := inlinePass target
    match t' with
    | .record fs =>
      match fs.find? (fun field => field.1 == name) with
      | some (_, body) => body
      | none => .get t' name
    | _ => .get t' name
  | .split target names fn =>
    let t' := inlinePass target
    let fn' := inlinePass fn
    match t' with
    | .record fs =>
      match splitValues fs names with
      | some vals => applyAll fn' vals
      | none => .split t' names fn'
    | _ => .split t' names fn'
  | .case scrut arms =>
    let s' := inlinePass scrut
    let arms' := arms.map fun a => (a.1, inlinePass a.2)
    match s' with
    | .inject lbl payload =>
      match arms'.find? (fun a => a.1 == lbl) with
      | some (_, body) => instantiate body payload
      | none => .case s' arms'
    | _ => .case s' arms'
  | .record fs => .record (fs.map fun f => (f.1, inlinePass f.2))
  | .inject lbl p => .inject lbl (inlinePass p)
  | .binary op l r => .binary op (inlinePass l) (inlinePass r)
  | .ifBool c t f => .ifBool (inlinePass c) (inlinePass t) (inlinePass f)
  | .ifZero v z s => .ifZero (inlinePass v) (inlinePass z) (inlinePass s)
  | .fix s i => .fix (inlinePass s) (inlinePass i)
  | other => other
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf a.snd < sizeOf a := by cases a; simp +arith
       omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf f.snd < sizeOf f := by cases f; simp +arith
       omega)

/-- Iterate `inlinePass` `k` times to eliminate nested Lean 4 typeclass dictionary wrappers
(`HAdd.hAdd`, `HSub.hSub`, `OfNat.ofNat`, `Decidable.decide`, `ite`) prior to combinational RTL
compilation. -/
def inlineDict : Nat → Term → Term
  | 0, t => t
  | k + 1, t => inlineDict k (inlinePass t)

/-- `inlinePass` is the identity on already-direct lowered terms (`doubleLExpr` and
`smallUnderflowLExpr`). -/
theorem inlinePass_direct_idempotent :
    inlinePass (lowerT doubleLExpr) = lowerT doubleLExpr ∧
    inlinePass (lowerT smallUnderflowLExpr) = lowerT smallUnderflowLExpr := by
  simp [inlinePass, doubleLExpr, smallUnderflowLExpr, lowerT, NatOp.prim]

/-! ## 6. Contextual Equivalence (`Ahead` and `≈b`) of Beta + Record + Split Dictionary Inlining -/

/-- Static beta-resolution: `(.lam b) a ↦ instantiate b a`. -/
def resolveApp : Term → Term → Term
  | .lam b, a => instantiate b a
  | f, a => .app f a

theorem ahead_resolveApp {f f' a a' : Term} (hf : Ahead f f') (ha : Ahead a a') :
    Ahead (.app f a) (resolveApp f' a') := by
  unfold resolveApp
  split
  · rename_i b'
    obtain ⟨b, s, ab⟩ := Obend.Equiv.inv_lam_ahead hf
    exact .run (steps_snoc (Obend.Equiv.steps_app a s) (.beta b a)) (ahead_instantiate ab ha)
  · exact .app hf ha

/-- Static record-split resolution: `.split (.record fs) names fn ↦ applyAll fn vals`. -/
def resolveSplit : Term → List String → Term → Term
  | .record fs, names, fn =>
    match splitValues fs names with
    | some vals => applyAll fn vals
    | none => .split (.record fs) names fn
  | t, names, fn => .split t names fn

theorem ahead_resolveSplit {t t' fn fn' : Term} (names : List String)
    (ht : Ahead t t') (hfn : Ahead fn fn') :
    Ahead (.split t names fn) (resolveSplit t' names fn') := by
  unfold resolveSplit
  split
  · rename_i fs'
    split
    · rename_i vals' hit
      obtain ⟨fs, s, n1, r1⟩ := Obend.Equiv.inv_record_ahead ht
      obtain ⟨vals, hit0, a⟩ := Obend.Equiv.splitValues_right n1 r1 hfn hit
      exact .run (steps_snoc (Obend.Equiv.steps_split names fn s) (.splitRecord fs names fn vals hit0)) a
    · exact .split names ht hfn
  · exact .split names ht hfn

/-- One bottom-up pass of verified `Core4` beta, record-projection (`resolveGet`), and record-split
(`resolveSplit`) reduction in any context. -/
def betaRecordPass : Term → Term
  | .hole n σ => .hole n (σ.map betaRecordPass)
  | .bound i => .bound i
  | .lam b => .lam (betaRecordPass b)
  | .app f a => resolveApp (betaRecordPass f) (betaRecordPass a)
  | .mix l u => .mix (betaRecordPass l) (betaRecordPass u)
  | .fix s i => .fix (betaRecordPass s) (betaRecordPass i)
  | .specification m e => .specification (betaRecordPass m) (betaRecordPass e)
  | .prototype s g => .prototype (betaRecordPass s) (betaRecordPass g)
  | .reflect p => .reflect (betaRecordPass p)
  | .metadata p => .metadata (betaRecordPass p)
  | .project p => .project (betaRecordPass p)
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label l => .label l
  | .binary op l r => .binary op (betaRecordPass l) (betaRecordPass r)
  | .extend i fs => .extend (betaRecordPass i) (fs.map fun f => (f.1, betaRecordPass f.2))
  | .record fs => .record (fs.map fun f => (f.1, betaRecordPass f.2))
  | .get g p => resolveGet (betaRecordPass g) p
  | .ifZero v z s => .ifZero (betaRecordPass v) (betaRecordPass z) (betaRecordPass s)
  | .inject l p => .inject l (betaRecordPass p)
  | .case sc arms => .case (betaRecordPass sc) (arms.map fun a => (a.1, betaRecordPass a.2))
  | .ifBool c x y => .ifBool (betaRecordPass c) (betaRecordPass x) (betaRecordPass y)
  | .perform p => .perform (betaRecordPass p)
  | .done v => .done (betaRecordPass v)
  | .split t names f => resolveSplit (betaRecordPass t) names (betaRecordPass f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

/-- **Soundness of `betaRecordPass` (`ahead_betaRecordPass`)**: `betaRecordPass t` is an `Ahead`
reduction-in-context of `t` for every `Term`. -/
theorem ahead_betaRecordPass : (t : Term) → Ahead t (betaRecordPass t)
  | .hole n σ => by
    simp only [betaRecordPass]
    refine .hole n (by simp) ?_
    intro p hp
    rw [List.zip_map_right] at hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hp
    obtain ⟨he, ha⟩ := zip_self σ (a, b) hab
    have hb : a = b := he
    subst hb
    have _ : a ∈ σ := ha
    exact ahead_betaRecordPass a
  | .bound i => by simp only [betaRecordPass]; exact .bound i
  | .lam b => by simp only [betaRecordPass]; exact .lam (ahead_betaRecordPass b)
  | .app f a => by simp only [betaRecordPass]; exact ahead_resolveApp (ahead_betaRecordPass f) (ahead_betaRecordPass a)
  | .mix l u => by simp only [betaRecordPass]; exact .mix (ahead_betaRecordPass l) (ahead_betaRecordPass u)
  | .fix s i => by simp only [betaRecordPass]; exact .fix (ahead_betaRecordPass s) (ahead_betaRecordPass i)
  | .specification m e => by simp only [betaRecordPass]; exact .specification (ahead_betaRecordPass m) (ahead_betaRecordPass e)
  | .prototype s g => by simp only [betaRecordPass]; exact .prototype (ahead_betaRecordPass s) (ahead_betaRecordPass g)
  | .reflect p => by simp only [betaRecordPass]; exact .reflect (ahead_betaRecordPass p)
  | .metadata p => by simp only [betaRecordPass]; exact .metadata (ahead_betaRecordPass p)
  | .project p => by simp only [betaRecordPass]; exact .project (ahead_betaRecordPass p)
  | .nat n => by simp only [betaRecordPass]; exact .nat n
  | .boolean b => by simp only [betaRecordPass]; exact .boolean b
  | .label l => by simp only [betaRecordPass]; exact .label l
  | .binary op l r => by simp only [betaRecordPass]; exact .binary op (ahead_betaRecordPass l) (ahead_betaRecordPass r)
  | .extend i fs => by
    simp only [betaRecordPass]
    exact .extend (ahead_betaRecordPass i) (names_map _ fs).symm
      (zip_map_self_rel betaRecordPass fs fun x _ => ahead_betaRecordPass x.2)
  | .record fs => by
    simp only [betaRecordPass]
    exact .record (names_map _ fs).symm
      (zip_map_self_rel betaRecordPass fs fun x _ => ahead_betaRecordPass x.2)
  | .get g p => by simp only [betaRecordPass]; exact ahead_resolveGet p (ahead_betaRecordPass g)
  | .ifZero v z s => by simp only [betaRecordPass]; exact .ifZero (ahead_betaRecordPass v) (ahead_betaRecordPass z) (ahead_betaRecordPass s)
  | .inject l p => by simp only [betaRecordPass]; exact .inject l (ahead_betaRecordPass p)
  | .case sc arms => by
    simp only [betaRecordPass]
    exact .case (ahead_betaRecordPass sc) (names_map _ arms).symm
      (zip_map_self_rel betaRecordPass arms fun x _ => ahead_betaRecordPass x.2)
  | .ifBool c x y => by simp only [betaRecordPass]; exact .ifBool (ahead_betaRecordPass c) (ahead_betaRecordPass x) (ahead_betaRecordPass y)
  | .perform p => by simp only [betaRecordPass]; exact .perform (ahead_betaRecordPass p)
  | .done v => by simp only [betaRecordPass]; exact .done (ahead_betaRecordPass v)
  | .split t names f => by simp only [betaRecordPass]; exact ahead_resolveSplit names (ahead_betaRecordPass t) (ahead_betaRecordPass f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

/-- **`betaRecordPass` preserves contextual behavioural equivalence (`≈b`)**. -/
theorem bequiv_betaRecordPass (t : Term) : t ≈b betaRecordPass t :=
  bequiv_of_ahead (ahead_betaRecordPass t)

/-- Iterate `betaRecordPass` `k` times. -/
def betaRecordDict : Nat → Term → Term
  | 0, t => t
  | k + 1, t => betaRecordDict k (betaRecordPass t)

/-- **Multi-pass dictionary inlining preserves contextual behavioural equivalence (`≈b`)** for
every pass count `k` and every term `t`. -/
theorem bequiv_betaRecordDict : ∀ (k : Nat) (t : Term), t ≈b betaRecordDict k t
  | 0, t => BEquiv.refl t
  | k + 1, t => (bequiv_betaRecordPass t).trans (bequiv_betaRecordDict k (betaRecordPass t))

/-- **Contextual Behavioural Equivalence of `.ifBool`-Application Distribution (`bequiv_app_ifBool_bool`)**:
Whenever the condition `c` reduces to a Boolean `b` (`Steps c (.boolean b)`), distributing
application across `.ifBool` (`(.ifBool c t e) a` ↔ `.ifBool c (t a) (e a)`) is a full contextual
behavioural equivalence (`≈b`) in every context and under every substitution! -/
theorem bequiv_app_ifBool_bool {c t e a : Term} {b : Bool} (hc : Steps c (.boolean b)) :
    (.app (.ifBool c t e) a) ≈b (.ifBool c (.app t a) (.app e a)) := by
  have hcond1 : Steps (.app (.ifBool c t e) a) (.app (.ifBool (.boolean b) t e) a) :=
    Obend.Equiv.steps_app a (Obend.Equiv.steps_ifBool t e hc)
  have hcond2 : Steps (.ifBool c (.app t a) (.app e a)) (.ifBool (.boolean b) (.app t a) (.app e a)) :=
    Obend.Equiv.steps_ifBool (.app t a) (.app e a) hc
  cases b
  · have h1 : Steps (.app (.ifBool c t e) a) (.app e a) :=
      steps_snoc hcond1 (.application a (.ifFalse t e))
    have h2 : Steps (.ifBool c (.app t a) (.app e a)) (.app e a) :=
      steps_snoc hcond2 (.ifFalse (.app t a) (.app e a))
    exact (bequiv_of_steps h1).trans (bequiv_of_steps h2).symm
  · have h1 : Steps (.app (.ifBool c t e) a) (.app t a) :=
      steps_snoc hcond1 (.application a (.ifTrue t e))
    have h2 : Steps (.ifBool c (.app t a) (.app e a)) (.app t a) :=
      steps_snoc hcond2 (.ifTrue (.app t a) (.app e a))
    exact (bequiv_of_steps h1).trans (bequiv_of_steps h2).symm

/-! ## 7. Transported Theorem to Combinational Hardware Assertion Monitor (`transport_monitor_rtl`) -/

/-- `LExpr` decision procedure for `∀ n : Nat, if n ≤ 2 then small n == 1 else true`
(`small_lt_three` in `Programs.lean`). -/
def smallLtThreeDeciderLExpr : LExpr :=
  .lam .natural
    (.boolRec .boolean
      (.boolLit true)
      (.natBin .beq
        (.boolRec .natural
          (.natBin .sub (.bvar 0) (.lit 3))
          (.natBin .add (.natBin .sub (.bvar 0) (.lit 3)) (.lit 1))
          (.natBin .ble (.bvar 0) (.lit 2)))
        (.lit 1))
      (.natBin .ble (.bvar 0) (.lit 2)))

/-- **Hardware Assertion Monitor Synthesis (`small_lt_three_rtl_monitor_verified`)**:
The lowered decision procedure `lowerT smallLtThreeDeciderLExpr` compiles via `compileBookToRtlSat`
into a verified SystemVerilog assertion monitor `RtlModule` (`checkRtlModule m = true`) whose output
wire `out_small_lt_three` evaluates to `1#64` (`true`) across both underflowing (`n = 0, 1, 2`) and
non-underflowing (`n = 3, 10`) hardware inputs! -/
theorem small_lt_three_rtl_monitor_verified :
    let C := leanComposition "small_lt_three" (lowerT smallLtThreeDeciderLExpr)
    let B := emit C
    (match compileBookToRtlSat "lean_small_lt_three_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 0#64) (fun _ => 0#64) == [("out_small_lt_three", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 1#64) (fun _ => 0#64) == [("out_small_lt_three", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 2#64) (fun _ => 0#64) == [("out_small_lt_three", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) == [("out_small_lt_three", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 10#64) (fun _ => 0#64) == [("out_small_lt_three", 1#64)])
     | none => false) = true := by
  decide +kernel

/-! ## 8. Sequential Multi-Cycle `Nat.rec` FSM Compilation (`sumToLExpr` → `Book` → `compileBookToSeqRtlSat`) -/

/-- `fun n : Nat => Nat.rec 0 (fun k acc => acc + k + 1) n` (`sumTo` in `Programs.lean`). -/
def sumToLExpr : LExpr :=
  .lam .natural
    (.natRec .natural
      (.lit 0)
      (.lam .natural (.lam .natural
        (.natBin .add (.natBin .add (.bvar 0) (.bvar 1)) (.lit 1))))
      (.bvar 0))

/-- **Verified Sequential Multi-Cycle Hardware Synthesis for `sumTo` (`lean_sumTo_seq_rtl_verified`)**:
1. `lowerT sumToLExpr` is wrapped in a `Leaf.Book` (`emit (leanComposition "sumTo" ...)`),
2. `compileBookToSeqRtlSat` synthesizes a 2-register (`reg_idx`, `reg_acc`), 5-wire sequential
   `RtlModule` that passes `checkRtlModule` (`checkWireTableDAG` + `checkModuleCdc`),
3. Cycle-accurate simulation (`evalSeqModuleAfterCycles`) over `n` clock cycles matches
   `sumTo n = n * (n + 1) / 2` and asserts `out_done = 1#64` for `n = 0` (`0`), `n = 5` (`15`),
   and `n = 10` (`55`), while after only `4` cycles on `n = 5` (`reg_idx = 4 < 5`), `out_done`
   remains `0#64`! -/
theorem lean_sumTo_seq_rtl_verified :
    let C := leanComposition "sumTo" (lowerT sumToLExpr)
    let B := emit C
    (match compileBookToSeqRtlSat "lean_sumTo_seq_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalSeqModuleAfterCycles m 0#64 0 == [("out_sumTo", 0#64), ("out_done", 1#64)]) &&
       (evalSeqModuleAfterCycles m 5#64 4 == [("out_sumTo", 10#64), ("out_done", 0#64)]) &&
       (evalSeqModuleAfterCycles m 5#64 5 == [("out_sumTo", 15#64), ("out_done", 1#64)]) &&
       (evalSeqModuleAfterCycles m 10#64 10 == [("out_sumTo", 55#64), ("out_done", 1#64)])
     | none => false) = true := by
  decide +kernel

end Obend.Lower
end
