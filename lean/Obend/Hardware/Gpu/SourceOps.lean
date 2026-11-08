module
/- Core4 encodings of GPU word operations. Arithmetic is explicitly modulo 2^64.
Subtraction adds 2^64 before Nat subtraction; shifts guard the count because Core4
masks it modulo 64 whereas GPU element operations return zero for counts ≥ 64. -/
public import Obend.Hardware.Gpu
public import Obend.Leaf.Emit
@[expose] public section
namespace Obend.Hardware.Gpu.Source
open Obend.Core.Term Obend.Equiv Obend.Leaf
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
set_option autoImplicit false

inductive Binary where
  | add | mul | sub | band | bor | ult | shl | shr
  deriving DecidableEq, Repr

def Binary.eval : Binary → Word → Word → Word
  | .add, x, y => x + y
  | .mul, x, y => x * y
  | .sub, x, y => x - y
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .ult, x, y => if BitVec.ult x y then 1#64 else 0#64
  | .shl, x, y => wordShl x y
  | .shr, x, y => wordShr x y

def Binary.op : Binary → ElemOp
  | .add => .scalar .add
  | .mul => .scalar .mul
  | .sub => .scalar .sub
  | .band => .band
  | .bor => .bor
  | .ult => .ult
  | .shl => .shl
  | .shr => .shr

def Binary.term : Binary → Term → Term → Term
  | .add, x, y => .binary .modulo (.binary .add x y) (.nat (2^64))
  | .mul, x, y => .binary .modulo (.binary .multiply x y) (.nat (2^64))
  | .sub, x, y => .binary .modulo
      (.binary .subtract (.binary .add x (.nat (2^64))) y) (.nat (2^64))
  | .band, x, y => .binary .bitAnd x y
  | .bor, x, y => .binary .bitOr x y
  | .ult, x, y => .ifBool (.binary .less x y) (.nat 1) (.nat 0)
  | .shl, x, y => .ifBool (.binary .less y (.nat 64)) (.binary .shl x y) (.nat 0)
  | .shr, x, y => .ifBool (.binary .less y (.nat 64)) (.binary .lshr x y) (.nat 0)

theorem Binary.substitute (b : Binary) (x y : Term) (σ : Nat → Term) :
    (b.term x y).substitute σ = b.term (x.substitute σ) (y.substitute σ) := by
  cases b <;> simp [Binary.term, Term.substitute]

theorem Binary.congrAhead (b : Binary) {l l' r r' : Term}
    (hl : Ahead l l') (hr : Ahead r r') : Ahead (b.term l r) (b.term l' r') := by
  cases b with
  | add => exact .binary _ (.binary _ hl hr) (.nat _)
  | mul => exact .binary _ (.binary _ hl hr) (.nat _)
  | sub => exact .binary _ (.binary _ (.binary _ hl (.nat _)) hr) (.nat _)
  | band => exact .binary _ hl hr
  | bor => exact .binary _ hl hr
  | ult => exact .ifBool (.binary _ hl hr) (.nat _) (.nat _)
  | shl => exact .ifBool (.binary _ hr (.nat _)) (.binary _ hl hr) (.nat _)
  | shr => exact .ifBool (.binary _ hr (.nat _)) (.binary _ hl hr) (.nat _)

theorem Binary.steps (b : Binary) (x y : Word) :
    Steps (b.term (.nat x.toNat) (.nat y.toNat)) (.nat (b.eval x y).toNat) := by
  cases b with
  | add =>
    refine .next (.binaryLeft .modulo _ (.primitive .add _ _ _ (.natural _) (.natural _) rfl)) ?_
    exact .next (.primitive .modulo _ _ _ (.natural _) (.natural _) (by simp [primitiveResult, Binary.eval, BitVec.toNat_add])) (.refl _)
  | mul =>
    refine .next (.binaryLeft .modulo _ (.primitive .multiply _ _ _ (.natural _) (.natural _) rfl)) ?_
    exact .next (.primitive .modulo _ _ _ (.natural _) (.natural _) (by simp [primitiveResult, Binary.eval, BitVec.toNat_mul])) (.refl _)
  | sub =>
    refine .next (.binaryLeft .modulo _ (.binaryLeft .subtract _
      (.primitive .add _ _ _ (.natural _) (.natural _) rfl))) ?_
    refine .next (.binaryLeft .modulo _ (.primitive .subtract _ _ _ (.natural _) (.natural _) rfl)) ?_
    refine .next (.primitive .modulo _ _ _ (.natural _) (.natural _) ?_) (.refl _)
    have hy := y.isLt
    have heq : x.toNat + 2^64 - y.toNat = (2^64 - y.toNat) + x.toNat := by omega
    simp [primitiveResult, Binary.eval, BitVec.toNat_sub, heq]
  | band =>
    exact .next (.primitive .bitAnd _ _ _ (.natural _) (.natural _) (by simp [primitiveResult, Binary.eval, word64])) (.refl _)
  | bor =>
    exact .next (.primitive .bitOr _ _ _ (.natural _) (.natural _) (by simp [primitiveResult, Binary.eval, word64])) (.refl _)
  | ult =>
    refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
    by_cases h : x.toNat < y.toNat
    · simpa [Binary.eval, BitVec.ult_eq_decide, h] using
        (Steps.next (Step.ifTrue (.nat 1) (.nat 0)) (.refl _))
    · simpa [Binary.eval, BitVec.ult_eq_decide, h] using
        (Steps.next (Step.ifFalse (.nat 1) (.nat 0)) (.refl _))
  | shl =>
    refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
    by_cases h : y.toNat < 64
    · simp only [h, decide_true]
      refine .next (.ifTrue _ _) ?_
      exact .next (.primitive .shl _ _ _ (.natural _) (.natural _)
        (by simp [primitiveResult, Binary.eval, word64, Nat.mod_eq_of_lt h])) (.refl _)
    · simp only [h, decide_false]
      simpa [Binary.eval, BitVec.shiftLeft_eq_zero (Nat.le_of_not_lt h)] using
        (Steps.next (Step.ifFalse (.binary .shl (.nat x.toNat) (.nat y.toNat)) (.nat 0)) (.refl _))
  | shr =>
    refine .next (.ifCondition _ _ (.primitive .less _ _ _ (.natural _) (.natural _) rfl)) ?_
    by_cases h : y.toNat < 64
    · simp only [h, decide_true]
      refine .next (.ifTrue _ _) ?_
      exact .next (.primitive .lshr _ _ _ (.natural _) (.natural _)
        (by simp [primitiveResult, Binary.eval, word64, Nat.mod_eq_of_lt h])) (.refl _)
    · simp only [h, decide_false]
      simpa [Binary.eval, BitVec.ushiftRight_eq_zero (Nat.le_of_not_lt h)] using
        (Steps.next (Step.ifFalse (.binary .lshr (.nat x.toNat) (.nat y.toNat)) (.nat 0)) (.refl _))

def muxEval (c x y : Word) : Word := if c != 0#64 then x else y

def muxTerm (c x y : Term) : Term := .ifBool (.binary .equal c (.nat 0)) y x

theorem mux_substitute (c x y : Term) (σ : Nat → Term) :
    (muxTerm c x y).substitute σ =
      muxTerm (c.substitute σ) (x.substitute σ) (y.substitute σ) := by
  simp [muxTerm, Term.substitute]

theorem mux_congrAhead {c c' x x' y y' : Term}
    (hc : Ahead c c') (hx : Ahead x x') (hy : Ahead y y') :
    Ahead (muxTerm c x y) (muxTerm c' x' y') :=
  .ifBool (.binary _ hc (.nat _)) hy hx

theorem mux_steps (c x y : Word) :
    Steps (muxTerm (.nat c.toNat) (.nat x.toNat) (.nat y.toNat))
      (.nat (muxEval c x y).toNat) := by
  refine .next (.ifCondition _ _ (.primitive .equal _ _ _ (.natural _) (.natural _) rfl)) ?_
  by_cases h : c = 0#64
  · subst c
    simpa [muxEval] using (Steps.next (Step.ifTrue (.nat y.toNat) (.nat x.toNat)) (.refl _))
  · have hn : c.toNat ≠ 0 := by
      intro hn
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa using hn
    have hb : (c.toNat == 0) = false := beq_eq_false_iff_ne.mpr hn
    simpa [muxEval, h, hb] using (Steps.next (Step.ifFalse (.nat y.toNat) (.nat x.toNat)) (.refl _))

end Obend.Hardware.Gpu.Source
end
