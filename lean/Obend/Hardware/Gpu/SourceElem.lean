module
public import Obend.Hardware.Gpu.SourceOps
@[expose] public section
namespace Obend.Hardware.Gpu.Source
open Obend.Core.Term Obend.Equiv Obend.Leaf
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
set_option autoImplicit false

/-- Lift a canonical word result through reductions in arbitrary operand positions. -/
theorem steps_of_ahead_word {t t' : Term} (v : Word)
    (h : Ahead t t') (s : Steps t' (.nat v.toNat)) : Steps t (.nat v.toNat) := by
  obtain ⟨r, hr, ha⟩ := evaluates_ahead h ⟨s, .natural _⟩
  exact steps_trans hr.1 (inv_literal_ahead (.nat _) ha)

theorem Binary.sound (b : Binary) {l r : Term} (x y : Word)
    (hl : Steps l (.nat x.toNat)) (hr : Steps r (.nat y.toNat)) :
    Steps (b.term l r) (.nat (b.eval x y).toNat) :=
  steps_of_ahead_word _ (b.congrAhead (.run hl (.nat _)) (.run hr (.nat _))) (b.steps x y)

theorem mux_sound {c x y : Term} (cv xv yv : Word)
    (hc : Steps c (.nat cv.toNat)) (hx : Steps x (.nat xv.toNat))
    (hy : Steps y (.nat yv.toNat)) :
    Steps (muxTerm c x y) (.nat (muxEval cv xv yv).toNat) :=
  steps_of_ahead_word _ (mux_congrAhead (.run hc (.nat _)) (.run hx (.nat _))
    (.run hy (.nat _))) (mux_steps cv xv yv)

/-- Core4 meaning of every GPU element operation, including missing-operand zero defaults. -/
def elemTerm (op : ElemOp) (args : List Term) : Term :=
  let a0 := args.getD 0 (.nat 0)
  let a1 := args.getD 1 (.nat 0)
  let a2 := args.getD 2 (.nat 0)
  match op with
  | .scalar (.const v) => .nat (BitVec.ofInt 64 v).toNat
  | .scalar .add => Binary.add.term a0 a1
  | .scalar .sub => Binary.sub.term a0 a1
  | .scalar .mul => Binary.mul.term a0 a1
  | .scalar (.scale k) => Binary.mul.term (.nat (BitVec.ofInt 64 k).toNat) a0
  | .scalar .mac => Binary.add.term (Binary.mul.term a0 a1) a2
  | .scalar .mux => muxTerm a0 a1 a2
  | .ult => Binary.ult.term a0 a1
  | .band => Binary.band.term a0 a1
  | .bor => Binary.bor.term a0 a1
  | .shl => Binary.shl.term a0 a1
  | .shr => Binary.shr.term a0 a1

theorem elemTerm_congrAhead (op : ElemOp) (args args' : List Term)
    (h : ∀ i, Ahead (args.getD i (.nat 0)) (args'.getD i (.nat 0))) :
    Ahead (elemTerm op args) (elemTerm op args') := by
  cases op with
  | scalar op =>
    cases op with
    | const v => exact .nat _
    | add => exact Binary.add.congrAhead (h 0) (h 1)
    | sub => exact Binary.sub.congrAhead (h 0) (h 1)
    | mul => exact Binary.mul.congrAhead (h 0) (h 1)
    | scale k => exact Binary.mul.congrAhead (.nat _) (h 0)
    | mac => exact Binary.add.congrAhead (Binary.mul.congrAhead (h 0) (h 1)) (h 2)
    | mux => exact mux_congrAhead (h 0) (h 1) (h 2)
  | ult => exact Binary.ult.congrAhead (h 0) (h 1)
  | band => exact Binary.band.congrAhead (h 0) (h 1)
  | bor => exact Binary.bor.congrAhead (h 0) (h 1)
  | shl => exact Binary.shl.congrAhead (h 0) (h 1)
  | shr => exact Binary.shr.congrAhead (h 0) (h 1)

theorem getD_substitute (args : List Term) (i : Nat) (σ : Nat → Term) :
    (args.map (fun t => t.substitute σ)).getD i (.nat 0) =
      (args.getD i (.nat 0)).substitute σ := by
  induction args generalizing i with
  | nil => simp [Term.substitute]
  | cons a args ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem elemTerm_substitute (op : ElemOp) (args : List Term) (σ : Nat → Term) :
    (elemTerm op args).substitute σ = elemTerm op (args.map fun t => t.substitute σ) := by
  cases op with
  | scalar op => cases op <;>
      simp only [elemTerm, Binary.substitute, mux_substitute, getD_substitute, Term.substitute]
  | ult | band | bor | shl | shr =>
      simp only [elemTerm, Binary.substitute, getD_substitute]

/-- Universal reduction theorem with independently reducible operands. -/
theorem elemTerm_sound (op : ElemOp) (args : List Term) (xs : List Word)
    (h : ∀ i, Steps (args.getD i (.nat 0)) (.nat (xs.getD i 0#64).toNat)) :
    Steps (elemTerm op args) (.nat (evalElemOp op xs).toNat) := by
  cases op with
  | scalar op =>
    cases op with
    | const v => exact .refl _
    | add => exact Binary.add.sound _ _ (h 0) (h 1)
    | sub => exact Binary.sub.sound _ _ (h 0) (h 1)
    | mul => exact Binary.mul.sound _ _ (h 0) (h 1)
    | scale k => exact Binary.mul.sound _ _ (.refl _) (h 0)
    | mac => exact Binary.add.sound _ _ (Binary.mul.sound _ _ (h 0) (h 1)) (h 2)
    | mux => exact mux_sound _ _ _ (h 0) (h 1) (h 2)
  | ult => exact Binary.ult.sound _ _ (h 0) (h 1)
  | band => exact Binary.band.sound _ _ (h 0) (h 1)
  | bor => exact Binary.bor.sound _ _ (h 0) (h 1)
  | shl => exact Binary.shl.sound _ _ (h 0) (h 1)
  | shr => exact Binary.shr.sound _ _ (h 0) (h 1)

theorem getD_wordTerms (xs : List Word) (i : Nat) :
    (xs.map fun x => Term.nat x.toNat).getD i (.nat 0) = .nat (xs.getD i 0#64).toNat := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem elemTerm_steps (op : ElemOp) (xs : List Word) :
    Steps (elemTerm op (xs.map fun x => .nat x.toNat)) (.nat (evalElemOp op xs).toNat) := by
  apply elemTerm_sound
  intro i
  rw [getD_wordTerms]
  exact .refl _

end Obend.Hardware.Gpu.Source
end
