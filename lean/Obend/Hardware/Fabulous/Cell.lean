module
/-
# Obend.Hardware.Fabulous.Cell — the LUT4 cell model, read as Booleans

`lut4cModule` (in `Obend.Hardware.Fabulous.Tile`) is `LUT4c_frame_config_dffesr.v` transcribed as an
`RtlModule`, and `hardware/fabulous/lec_tile.sh` proves it equal to FABulous's Verilog. The grid
semantics (`Obend.Hardware.Fabulous.Readback`) evaluates every LUT4 cell of the fabric through it. This
file reads its output `O` and its flop's next value as Boolean functions of the cell's inputs and its 19
configuration bits (`lut4c_O`, `lut4c_next`), the form the readback proof uses.
-/
public import Obend.Hardware.Fabulous.TileEval
public import Obend.Hardware.Fabulous.Net
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware.HDL

/-- The input vector of `lut4cModule` for Boolean inputs: `I` as a 4-bit word, `Ci`, `SR`, `EN` as 0/1
words, `ConfigBits` as a 19-bit word from `cb`. -/
def cellIns (i0 i1 i2 i3 ci sr en : Bool) (cb : Nat → Bool) : Nat → BitVec 64
  | 0 => (BitVec.ofBoolListLE [i0, i1, i2, i3]).setWidth 64
  | 1 => boolBV ci
  | 2 => boolBV sr
  | 3 => boolBV en
  | 4 => (BitVec.ofBoolListLE ((List.range 19).map cb)).setWidth 64
  | _ => 0#64

/-- The LUT4 function over a truth table given as a function (`lut4 init = lut4F init.getLsbD`). -/
def lut4F (l : Nat → Bool) (a b c d : Bool) : Bool :=
  mux2 d
    (mux2 c (mux2 b (mux2 a (l 0) (l 1)) (mux2 a (l 2) (l 3))) (mux2 b (mux2 a (l 4) (l 5)) (mux2 a (l 6) (l 7))))
    (mux2 c (mux2 b (mux2 a (l 8) (l 9)) (mux2 a (l 10) (l 11))) (mux2 b (mux2 a (l 12) (l 13)) (mux2 a (l 14) (l 15))))

theorem lut4_eq_lut4F (init : BitVec 16) (a b c d : Bool) : lut4 init a b c d = lut4F init.getLsbD a b c d := rfl

theorem lut4F_congr (l l' : Nat → Bool) (h : ∀ j < 16, l j = l' j) (a b c d : Bool) :
    lut4F l a b c d = lut4F l' a b c d := by
  simp only [lut4F, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide),
    h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]

theorem eval_bitOf (ins w r : Nat → BitVec 64) (i k : Nat) :
    evalRtlExpr ins w r (bitOf i k) = boolBV ((ins i).getLsbD k) := by
  simp only [bitOf, evalRtlExpr, evalWidthOp]
  rw [show k + 1 - k = 1 by omega, truncToWidth_one]
  simp

theorem mux_boolBV (s a b : Bool) :
    (if boolBV s != 0#64 then boolBV b else boolBV a) = boolBV (mux2 s a b) := by
  cases s <;> cases a <;> cases b <;> decide

theorem and_boolBV (a b : Bool) : boolBV a &&& boolBV b = boolBV (a && b) := by
  cases a <;> cases b <;> decide

theorem or_boolBV (a b : Bool) : boolBV a ||| boolBV b = boolBV (a || b) := by
  cases a <;> cases b <;> decide

theorem cellIns_bit0 (i0 i1 i2 i3 ci sr en : Bool) (cb : Nat → Bool) (k : Nat) (hk : k < 4) :
    (cellIns i0 i1 i2 i3 ci sr en cb 0).getLsbD k = [i0, i1, i2, i3].getD k false := by
  simp [cellIns, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]; omega

theorem cellIns_cfg (i0 i1 i2 i3 ci sr en : Bool) (cb : Nat → Bool) (k : Nat) (hk : k < 19) :
    (cellIns i0 i1 i2 i3 ci sr en cb 4).getLsbD k = cb k := by
  simp only [cellIns, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp; omega

/-- The cell's `LUT_out`: the truth table `cb 0..15` at `{I3, I2, I1, I0mux}`, `I0mux = cb 17 ? Ci : I0`. -/
def cellLut (i0 i1 i2 i3 ci : Bool) (cb : Nat → Bool) : Bool :=
  lut4F cb (if cb 17 then ci else i0) i1 i2 i3

theorem ite_boolBV (c : Bool) (x y : Bool) :
    (if c = true then boolBV x else boolBV y) = boolBV (if c then x else y) := by cases c <;> rfl

theorem cellIns_one (i0 i1 i2 i3 ci sr en : Bool) (cb : Nat → Bool) : cellIns i0 i1 i2 i3 ci sr en cb 1 = boolBV ci := rfl
theorem cellIns_two (i0 i1 i2 i3 ci sr en : Bool) (cb : Nat → Bool) : cellIns i0 i1 i2 i3 ci sr en cb 2 = boolBV sr := rfl
theorem cellIns_three (i0 i1 i2 i3 ci sr en : Bool) (cb : Nat → Bool) : cellIns i0 i1 i2 i3 ci sr en cb 3 = boolBV en := rfl

set_option maxRecDepth 4000 in
/-- **The cell's output.** `O` is the flop with `FF` (`cb 16`) set, otherwise `LUT_out`. -/
theorem lut4c_O (i0 i1 i2 i3 ci sr en qv : Bool) (cb : Nat → Bool) :
    (evalModuleOutputsW lut4cModule (cellIns i0 i1 i2 i3 ci sr en cb) (fun _ => boolBV qv))[0]? =
      some ("O", boolBV (if cb 16 then qv else cellLut i0 i1 i2 i3 ci cb)) := by
  simp only [evalModuleOutputsW, lut4cModule, evalWireTable, List.foldl, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, true_and, evalRtlExpr, m21, eval_bitOf,
    beq_self_eq_true, ite_true, Nat.reduceBEq, Bool.false_eq_true, ite_false, lut4cModule.tree,
    lut4cModule.tree.pr, List.range_succ, List.range_zero, List.map_nil, List.nil_append, List.cons_append,
    List.headD_cons]
  simp (disch := decide) only [cellIns_bit0, cellIns_cfg, cellIns_one,
    List.getD_cons_zero, List.getD_cons_succ, boolBV_ne_zero, ite_boolBV, truncToWidth_one_boolBV]
  congr 1
  simp only [cellLut, lut4F, mux2]
  cases cb 16 <;> cases cb 17 <;> cases i0 <;> cases i1 <;> cases i2 <;> cases i3 <;> cases ci <;> simp

set_option maxRecDepth 4000 in
/-- **The cell's flop.** On an edge it loads `EN ? (SR ? SET_NORESET : LUT_out) : itself`. -/
theorem lut4c_next (rst i0 i1 i2 i3 ci sr en qv : Bool) (cb : Nat → Bool) :
    stepModuleRegs lut4cModule rst (cellIns i0 i1 i2 i3 ci sr en cb) (fun _ => boolBV qv) 0 =
      boolBV (mux2 en qv (mux2 sr (cellLut i0 i1 i2 i3 ci cb) (cb 18))) := by
  simp only [stepModuleRegs, lut4cModule, evalWireTable, List.foldl, evalRtlExpr, m21, eval_bitOf,
    beq_self_eq_true, ite_true, Nat.reduceBEq, Bool.false_eq_true, ite_false, lut4cModule.tree,
    lut4cModule.tree.pr, List.range_succ, List.range_zero, List.map_nil, List.nil_append, List.cons_append,
    List.map_cons, List.headD_cons]
  simp (disch := decide) only [cellIns_bit0, cellIns_cfg, cellIns_one, cellIns_two, cellIns_three,
    List.getD_cons_zero, List.getD_cons_succ, boolBV_ne_zero, ite_boolBV]
  congr 1
  simp only [cellLut, lut4F, mux2]
  cases cb 17 <;> cases cb 18 <;> cases i0 <;> cases i1 <;> cases i2 <;> cases i3 <;> cases ci <;> cases sr <;>
    cases en <;> simp

/-- The truth table does not depend on input `i` (the extraction then leaves that input unrouted). -/
def ignores (init : BitVec 16) (i : Nat) : Bool :=
  (List.range 16).all fun k => init.getLsbD k == init.getLsbD (k ^^^ (1 <<< i))

theorem ignores_at {init : BitVec 16} {i : Nat} (h : ignores init i = true) (k : Nat) (hk : k < 16) :
    init.getLsbD k = init.getLsbD (k ^^^ (1 <<< i)) := by
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa using this

/-- An input the truth table ignores can be read as anything. -/
theorem lut4_ignored (init : BitVec 16) (a b c d : Bool) :
    (ignores init 0 = true → lut4 init a b c d = lut4 init false b c d) ∧
    (ignores init 1 = true → lut4 init a b c d = lut4 init a false c d) ∧
    (ignores init 2 = true → lut4 init a b c d = lut4 init a b false d) ∧
    (ignores init 3 = true → lut4 init a b c d = lut4 init a b c false) := by
  simp only [lut4_eq_getLsbD]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    cases a <;> cases b <;> cases c <;> cases d <;> simp <;>
    first | rfl | exact ignores_at h _ (by decide) | exact (ignores_at h _ (by decide)).symm

end Obend.Hardware.Fabulous
