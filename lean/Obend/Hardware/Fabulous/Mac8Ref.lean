module
/-
# Obend.Hardware.Fabulous.Mac8Ref — `iceStickMac8` on the fabric's pins, bit by bit

The pin map of `hardware/fabulous/top_wrapper.v` (`a`, `b`, `c`, `rst`, then `mac_out`, two pins per
`W_IO` row from `X0Y1`), and the module's next registers as 16-bit words (`mac8Next`), the form the
generated obligations of `Obend.Hardware.Fabulous.Mac8Net` compare the fabric against.
-/
public import Obend.Hardware.Fabulous.Net
public import Obend.Hardware.Mac8
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
public import Obend.AssertCompiled
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware.HDL

/-- The pins of `top_wrapper.v`, in order. -/
def mac8Roles : List PinRole :=
  (List.range 8).map (.input 0) ++ (List.range 8).map (.input 1) ++ (List.range 16).map (.input 2) ++
  [.reset] ++ (List.range 16).map (.output 0)

/-- `iceStickMac8`'s registers after one edge, as 16-bit words: `mulReg`, `cReg`, `outReg`. -/
def mac8Next (a b : BitVec 8) (c r0 r1 : BitVec 16) (rst : Bool) : Nat → BitVec 16
  | 0 => if rst then 0#16 else a.setWidth 16 * b.setWidth 16
  | 1 => if rst then 0#16 else c
  | 2 => if rst then 0#16 else r0 + r1
  | _ => 0#16

/-- A 64-bit word below `2^w` is a `w`-bit word zero-extended. -/
theorem exists_setWidth_of_lt {w : Nat} (x : BitVec 64) (h : x.toNat < 2 ^ w) :
    ∃ X : BitVec w, x = X.setWidth 64 := by
  refine ⟨x.setWidth w, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt x.isLt]

theorem mac8_module_step (ins regs : Nat → BitVec 64) (rst : Bool) (a b : BitVec 8) (c r0 r1 : BitVec 16)
    (ha : ins 0 = a.setWidth 64) (hb : ins 1 = b.setWidth 64) (hc : ins 2 = c.setWidth 64)
    (hr0 : regs 0 = r0.setWidth 64) (hr1 : regs 1 = r1.setWidth 64) :
    stepModuleRegs iceStickMac8 rst ins regs 0 = (mac8Next a b c r0 r1 rst 0).setWidth 64 ∧
    stepModuleRegs iceStickMac8 rst ins regs 1 = (mac8Next a b c r0 r1 rst 1).setWidth 64 ∧
    stepModuleRegs iceStickMac8 rst ins regs 2 = (mac8Next a b c r0 r1 rst 2).setWidth 64 := by
  simp only [stepModuleRegs, iceStickMac8, evalWireTable, List.foldl_cons, List.foldl_nil, mac8Next]
  cases rst <;> simp only [evalRtlExpr, ha, hb, hc, hr0, hr1, evalAluOp, evalWidthOp, truncToWidth] <;>
    simp <;> bv_decide

#assert_compiled mac8_module_step

/-- The pins of `top_wrapper.v`. -/
def mac8Pins : List Pin := pinsInOrder mac8Roles

/-- What the input pins carry, bit by bit. -/
theorem mac8_pins (c : Bool × (Nat → BitVec 64)) (a b : BitVec 8) (cc : BitVec 16)
    (ha : c.2 0 = a.setWidth 64) (hb : c.2 1 = b.setWidth 64) (hc : c.2 2 = cc.setWidth 64) :
    pinValues mac8Pins c 0 = a.getLsbD 0 ∧
    pinValues mac8Pins c 1 = a.getLsbD 1 ∧
    pinValues mac8Pins c 2 = a.getLsbD 2 ∧
    pinValues mac8Pins c 3 = a.getLsbD 3 ∧
    pinValues mac8Pins c 4 = a.getLsbD 4 ∧
    pinValues mac8Pins c 5 = a.getLsbD 5 ∧
    pinValues mac8Pins c 6 = a.getLsbD 6 ∧
    pinValues mac8Pins c 7 = a.getLsbD 7 ∧
    pinValues mac8Pins c 8 = b.getLsbD 0 ∧
    pinValues mac8Pins c 9 = b.getLsbD 1 ∧
    pinValues mac8Pins c 10 = b.getLsbD 2 ∧
    pinValues mac8Pins c 11 = b.getLsbD 3 ∧
    pinValues mac8Pins c 12 = b.getLsbD 4 ∧
    pinValues mac8Pins c 13 = b.getLsbD 5 ∧
    pinValues mac8Pins c 14 = b.getLsbD 6 ∧
    pinValues mac8Pins c 15 = b.getLsbD 7 ∧
    pinValues mac8Pins c 16 = cc.getLsbD 0 ∧
    pinValues mac8Pins c 17 = cc.getLsbD 1 ∧
    pinValues mac8Pins c 18 = cc.getLsbD 2 ∧
    pinValues mac8Pins c 19 = cc.getLsbD 3 ∧
    pinValues mac8Pins c 20 = cc.getLsbD 4 ∧
    pinValues mac8Pins c 21 = cc.getLsbD 5 ∧
    pinValues mac8Pins c 22 = cc.getLsbD 6 ∧
    pinValues mac8Pins c 23 = cc.getLsbD 7 ∧
    pinValues mac8Pins c 24 = cc.getLsbD 8 ∧
    pinValues mac8Pins c 25 = cc.getLsbD 9 ∧
    pinValues mac8Pins c 26 = cc.getLsbD 10 ∧
    pinValues mac8Pins c 27 = cc.getLsbD 11 ∧
    pinValues mac8Pins c 28 = cc.getLsbD 12 ∧
    pinValues mac8Pins c 29 = cc.getLsbD 13 ∧
    pinValues mac8Pins c 30 = cc.getLsbD 14 ∧
    pinValues mac8Pins c 31 = cc.getLsbD 15 ∧
    pinValues mac8Pins c 32 = c.1 :=
  ⟨(show pinValues mac8Pins c 0 = (c.2 0).getLsbD 0 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 1 = (c.2 0).getLsbD 1 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 2 = (c.2 0).getLsbD 2 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 3 = (c.2 0).getLsbD 3 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 4 = (c.2 0).getLsbD 4 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 5 = (c.2 0).getLsbD 5 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 6 = (c.2 0).getLsbD 6 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 7 = (c.2 0).getLsbD 7 from rfl).trans (by rw [ha]; simp),
   (show pinValues mac8Pins c 8 = (c.2 1).getLsbD 0 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 9 = (c.2 1).getLsbD 1 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 10 = (c.2 1).getLsbD 2 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 11 = (c.2 1).getLsbD 3 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 12 = (c.2 1).getLsbD 4 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 13 = (c.2 1).getLsbD 5 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 14 = (c.2 1).getLsbD 6 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 15 = (c.2 1).getLsbD 7 from rfl).trans (by rw [hb]; simp),
   (show pinValues mac8Pins c 16 = (c.2 2).getLsbD 0 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 17 = (c.2 2).getLsbD 1 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 18 = (c.2 2).getLsbD 2 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 19 = (c.2 2).getLsbD 3 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 20 = (c.2 2).getLsbD 4 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 21 = (c.2 2).getLsbD 5 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 22 = (c.2 2).getLsbD 6 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 23 = (c.2 2).getLsbD 7 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 24 = (c.2 2).getLsbD 8 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 25 = (c.2 2).getLsbD 9 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 26 = (c.2 2).getLsbD 10 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 27 = (c.2 2).getLsbD 11 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 28 = (c.2 2).getLsbD 12 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 29 = (c.2 2).getLsbD 13 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 30 = (c.2 2).getLsbD 14 from rfl).trans (by rw [hc]; simp),
   (show pinValues mac8Pins c 31 = (c.2 2).getLsbD 15 from rfl).trans (by rw [hc]; simp),
   rfl⟩

/-- What the output pins should show: `mac_out`, bit by bit. -/
theorem mac8_outs (ins regs : Nat → BitVec 64) (r2 : BitVec 16) (hr2 : regs 2 = r2.setWidth 64) :
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 33 = r2.getLsbD 0 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 34 = r2.getLsbD 1 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 35 = r2.getLsbD 2 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 36 = r2.getLsbD 3 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 37 = r2.getLsbD 4 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 38 = r2.getLsbD 5 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 39 = r2.getLsbD 6 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 40 = r2.getLsbD 7 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 41 = r2.getLsbD 8 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 42 = r2.getLsbD 9 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 43 = r2.getLsbD 10 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 44 = r2.getLsbD 11 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 45 = r2.getLsbD 12 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 46 = r2.getLsbD 13 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 47 = r2.getLsbD 14 ∧
    outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 48 = r2.getLsbD 15 :=
  ⟨(show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 33 = (truncToWidth 16 (regs 2)).getLsbD 0 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 34 = (truncToWidth 16 (regs 2)).getLsbD 1 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 35 = (truncToWidth 16 (regs 2)).getLsbD 2 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 36 = (truncToWidth 16 (regs 2)).getLsbD 3 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 37 = (truncToWidth 16 (regs 2)).getLsbD 4 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 38 = (truncToWidth 16 (regs 2)).getLsbD 5 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 39 = (truncToWidth 16 (regs 2)).getLsbD 6 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 40 = (truncToWidth 16 (regs 2)).getLsbD 7 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 41 = (truncToWidth 16 (regs 2)).getLsbD 8 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 42 = (truncToWidth 16 (regs 2)).getLsbD 9 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 43 = (truncToWidth 16 (regs 2)).getLsbD 10 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 44 = (truncToWidth 16 (regs 2)).getLsbD 11 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 45 = (truncToWidth 16 (regs 2)).getLsbD 12 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 46 = (truncToWidth 16 (regs 2)).getLsbD 13 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 47 = (truncToWidth 16 (regs 2)).getLsbD 14 from rfl).trans (by rw [hr2]; simp [truncToWidth]),
   (show outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 ins regs) 48 = (truncToWidth 16 (regs 2)).getLsbD 15 from rfl).trans (by rw [hr2]; simp [truncToWidth])⟩

/-- A reset cycle clears every register. -/
theorem mac8_module_reset (ins regs : Nat → BitVec 64) :
    stepModuleRegs iceStickMac8 true ins regs 0 = 0#64 ∧
    stepModuleRegs iceStickMac8 true ins regs 1 = 0#64 ∧
    stepModuleRegs iceStickMac8 true ins regs 2 = 0#64 := by
  simp only [stepModuleRegs, iceStickMac8, List.foldl_cons, List.foldl_nil]
  simp

end Obend.Hardware.Fabulous
