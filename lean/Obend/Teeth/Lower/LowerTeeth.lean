module
/-
# Obend.Teeth.Lower.LowerTeeth — Positive/Negative Poles & `#tooth` Kernel Mutation Suite for `Obend.Lower`

Covers all components of the `Lean-lite` → `Core4` → `Leaf.Book` → `Hardware.Compiler` and
`transport@1` stack:
* `Obend.Lower.Proofs.Sound` (`lower_sound_nat`)
* `Obend.Lower.Proofs.Complete` (`lower_complete_nat`, `checkL`, `checkL_sound`, `nonEmptySplits`)
* `Obend.Lower.Judge` (`lower@1`, `bad_refused`)
* `Obend.Lower.Transport` (`transport@1`, `badTransport_refused`, `methodSupport_blocked_on_override`,
  all 5 refusal clauses of `transportCheck`)
* `Obend.Hardware.Compiler` (`compilePrimSat_sound`, `evalPrimHwSat_subtract_eq_ofNat_sub`,
  `saturating_accepts_erased`)
-/
public import Obend.Tactic.Tooth
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Lower.Syntax
import all Obend.Lower.Semantics
import all Obend.Lower.Lower
import all Obend.Lower.Typing
import all Obend.Lower.Judge
import all Obend.Lower.Proofs.Subst
import all Obend.Lower.Proofs.Sound
import all Obend.Lower.Proofs.Complete
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Proofs.Hardware
import all Obend.Lower.Transport
import all Obend.Hardware.Compiler
public import Obend.Lower.Transport
public import Obend.Lower.Proofs.Hardware
@[expose] public section

namespace Obend.Teeth.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Logic
open Obend.Lower
open Obend.Hardware.HDL Obend.Hardware.Compiler
set_option autoImplicit false

/-! ## 1. Positive and Negative Poles for `checkL`, `nonEmptySplits`, and `transportCheck` -/

/-- `checkL` accepts `doubleLExpr` at `fn .natural .natural` and refuses `.lit 5` at `.boolean`. -/
theorem checkL_acceptance_and_refusal_poles :
    checkL [] doubleLExpr (fn .natural .natural) = true ∧
    checkL [] smallUnderflowLExpr (fn .natural .natural) = true ∧
    checkL [] (.lit 5) .boolean = false ∧
    nonEmptySplits erasedElim = false := by
  decide +kernel

/-- Valid decision procedure `fun n : Nat => n == n`. -/
def reflNatDecider : LExpr :=
  .lam .natural (.natBin .beq (.bvar 0) (.bvar 0))

def reflNatObj : TransportObj := ⟨reflNatDecider, [.natural]⟩

def reflNatCert : TransportCert :=
  ⟨sourceDigest reflNatDecider, lowerProp reflNatDecider, [.natural], []⟩

theorem checkL_reflNatDecider :
    checkL [] reflNatDecider (curry [.natural] .boolean) = true ∧
    nonEmptySplits reflNatDecider = true := by
  decide +kernel

/-- `transportCheck` accepts `reflNatCert` and exercises all 5 refusal clauses (`notTheLowering`,
`otherSource`, `wrongArgTys`, `emptySplit`, `illTyped`). -/
theorem transportCheck_all_clauses_exercised :
    transportCheck 0 reflNatObj reflNatCert = .ok ∧
    transportCheck 0 reflNatObj { reflNatCert with claim := .boolean false } =
      .refused .notTheLowering [] ∧
    transportCheck 0 reflNatObj { reflNatCert with digest := sourceDigest reflNatDecider + 1 } =
      .refused .otherSource [] ∧
    transportCheck 0 reflNatObj { reflNatCert with argTys := [] } =
      .refused .wrongArgTys [] ∧
    (let emptySplitExpr : LExpr := .split [] (.boolLit true) .erased
     transportCheck 0 ⟨emptySplitExpr, []⟩
       ⟨sourceDigest emptySplitExpr, lowerProp emptySplitExpr, [], []⟩ =
       .refused .emptySplit []) ∧
    (let illTypedExpr : LExpr := .lit 42
     transportCheck 0 ⟨illTypedExpr, []⟩
       ⟨sourceDigest illTypedExpr, lowerProp illTypedExpr, [], []⟩ =
       .refused .illTyped []) := by
  have h1 := checkL_reflNatDecider.1
  have h2 := checkL_reflNatDecider.2
  have hterm_false : Obend.Law.termEq (lowerProp reflNatDecider) (.boolean false) = false := by
    decide +kernel
  have hty_false : (([] : List Ty) == [.natural]) = false := by
    decide +kernel
  have hempty_split : nonEmptySplits (.split [] (.boolLit true) .erased) = false := by
    decide +kernel
  have hill_split : nonEmptySplits (.lit 42) = true := by
    decide +kernel
  have hill_check : checkL [] (.lit 42) (curry [] .boolean) = false := by
    decide +kernel
  have hdig_ne : (sourceDigest reflNatDecider + 1 == sourceDigest reflNatDecider) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [transportCheck, reflNatObj, reflNatCert, Obend.Logic.termEq_refl', h1, h2]
  · simp [transportCheck, reflNatObj, hterm_false]
  · simp [transportCheck, reflNatObj, reflNatCert, Obend.Logic.termEq_refl', hdig_ne]
  · simp [transportCheck, reflNatObj, reflNatCert, Obend.Logic.termEq_refl', hty_false]
  · simp [transportCheck, Obend.Logic.termEq_refl', hempty_split]
  · simp [transportCheck, Obend.Logic.termEq_refl', hill_split, hill_check]

/-! ## 2. `#tooth` Kernel Mutation Suite (9 Mutations Across `Lower` and `Hardware.Compiler`) -/

/-- 1. Broken `lowerT` that maps every `LExpr` to `.nat 0`. -/
def lowerConstZero (_ : LExpr) : Term := .nat 0

#tooth Obend.Lower.lower_sound_nat by mutation Obend.Lower.lowerT := lowerConstZero

-- 2. The same broken `lowerT` is also caught by converse simulation (`lower_complete_nat`).
#tooth Obend.Lower.lower_complete_nat by mutation Obend.Lower.lowerT := lowerConstZero

/-- 3. Broken bidirectional checker `checkL` that accepts every `(Γ, e, T)`. -/
def checkLAlwaysTrue (_ : List Ty) (_ : LExpr) (_ : Ty) : Bool := true

#tooth Obend.Lower.checkL_sound by mutation Obend.Lower.checkL := checkLAlwaysTrue

/-- 4. Broken `lower@1` judge that accepts every certificate without checking `termEq` or `digest`. -/
def checkLowerAcceptAll (_ : Nat) (_ : LExpr) (_ : Cert) : Obend.Judge.Verdict Clause := .ok

#tooth Obend.Lower.bad_refused by mutation Obend.Lower.check := checkLowerAcceptAll

/-- 5. Broken `transport@1` judge that accepts every certificate. -/
def transportCheckAcceptAll (_ : Nat) (_ : TransportObj) (_ : TransportCert) :
    Obend.Judge.Verdict TransportClause := .ok

#tooth Obend.Lower.badTransport_refused by mutation Obend.Lower.transportCheck := transportCheckAcceptAll

/-- 6. Broken `Support.holds` that ignores subclass overrides and always returns `true`. -/
def supportHoldsAlwaysTrue (_ : Composition) (_ : Nat) (_ : Support) : Bool := true

#tooth Obend.Lower.methodSupport_blocked_on_override by mutation Obend.Logic.Support.holds := supportHoldsAlwaysTrue

/-- 7. Broken `compilePrimSat` that compiles `.subtract` as wrapping `.alu .sub l r` instead of saturating at `0#64`. -/
def compilePrimSatWrappingSub (op : Primitive) (l r : RtlExpr) : Option RtlExpr :=
  match op with
  | .add         => some (.alu .add l r)
  | .multiply    => some (.alu .mul l r)
  | .subtract    => some (.alu .sub l r)
  | .equal       => some (.alu .eq l r)
  | .conjunction => some (.alu .bitAnd l r)
  | .less        => some (.alu .ult l r)
  | .lessEqual   => some (.mux (.alu .ult r l) (.const 0#64) (.const 1#64))
  | _            => none

#tooth Obend.Hardware.Compiler.compilePrimSat_sound by mutation Obend.Hardware.Compiler.compilePrimSat := compilePrimSatWrappingSub

/-- 8. Broken `evalPrimHwSat` that uses wrapping `a - b` instead of saturating at `0#64` when `a < b`. -/
def evalPrimHwSatWrappingSub (op : Primitive) (a b : BitVec 64) : Option (BitVec 64) :=
  match op with
  | .add         => some (a + b)
  | .multiply    => some (a * b)
  | .subtract    => some (a - b)
  | .equal       => some (if a == b then 1#64 else 0#64)
  | .conjunction => some (a &&& b)
  | .less        => some (if BitVec.ult a b then 1#64 else 0#64)
  | .lessEqual   => some (if BitVec.ult b a then 0#64 else 1#64)
  | _            => none

#tooth Obend.Hardware.Compiler.evalPrimHwSat_subtract_eq_ofNat_sub by mutation Obend.Hardware.Compiler.evalPrimHwSat := evalPrimHwSatWrappingSub

/-- 9. Broken `compileTermSat` that refuses `box = .record []` (`none`), caught by `saturating_accepts_erased`. -/
def compileTermSatRefuseBox
    (slots : List String)
    (slotBodies : List RtlExpr)
    (selfDepth : Nat)
    (varEnv : List RtlExpr) : Term → Option RtlExpr :=
  compileTerm slots slotBodies selfDepth varEnv

#tooth Obend.Lower.saturating_accepts_erased by mutation Obend.Hardware.Compiler.compileTermSat := compileTermSatRefuseBox

end Obend.Teeth.Lower
end
