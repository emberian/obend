module
/-
# `Obend.Leaf.BytecodeRegisterJit` — Flat Register Bytecode VM, Dictionary Erasure & Range-Safe Loop Compiler

Clears `review/EXPERT-compiler-runtime-20261103.md` §2.3 (typeclass dictionary-passing overhead in
tight numerical loops):
1. **Unboxed Register/Bytecode Engine (`ByteInstr`, `execBytecode`)**: flat `Array ByteInstr` over
   unboxed `Array UInt64` registers with bounds-checked instructions and fuel-bounded execution.
2. **Dictionary-Passing & Projection Erasure (`specializeDictTerm`)**: multi-pass bottom-up static
   reduction (`Obend.Leaf.Static.dataPinSteps`) proved observationally equivalent (`≈b`) and ground
   value-preserving (`specializeDictTerm_evaluates_iff`) on open expressions closed under any `env`.
3. **Range-Safe Bytecode Compiler (`compileExprToBytecode`, `compileExprToBytecode_sound`)**:
   relocatable register-allocating compiler over the `Obend.Core.RangeSafe` scalar/control fragment
   (`.nat`, `.boolean`, `.bound`, `let`, `.binary`, `.ifBool`, `.ifZero`) proved sound (`SimulatesBytecode`)
   against unspecialized `Core4` `Evaluates` with `< 2^64` overflow/underflow certification.
4. **Countdown Loop Specializer & C99 Emitter (`specializeAndCompileLoop`, `emitRegisterBytecodeC99`)**:
   strips `HAdd.hAdd` dictionary records from loop bodies, compiles to tight register loops, executes
   `sumTo 30000 = 450,015,000` cleanly, and emits standalone bounds-checked C99.
-/
public import Obend.Core.Term
public import Obend.Core.RangeSafe
public import Obend.Equiv.Behaviour
public import Obend.Leaf.Static
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.RangeSafe
import all Obend.Equiv.Simulation
import all Obend.Equiv.Behaviour
import all Obend.Leaf.Flatten
import all Obend.Leaf.Static

public section
namespace Obend.Leaf.BytecodeRegisterJit

open Obend.Core.Term
open Obend.Core.RangeSafe
open Obend.Equiv
open Obend.Leaf
open Obend.Leaf.Static

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## 1. Flat Unboxed Register Bytecode ISA & Virtual Machine (`ByteInstr`, `execBytecode`) -/

/-- Unboxed 64-bit ALU and comparison opcodes for `ByteInstr`. -/
inductive ByteBinOp where
  | add | sub | mul | div | mod
  | eq | lt | le | conj
  | bitAnd | bitOr | bitXor
  deriving @[expose] DecidableEq, Repr

/-- Flat register-transfer bytecode instruction set. -/
inductive ByteInstr where
  | loadImm (dst : Nat) (imm : UInt64)
  | mov (dst src : Nat)
  | binOp (op : ByteBinOp) (dst lhs rhs : Nat)
  | jz (cond targetPc : Nat)
  | jmp (targetPc : Nat)
  | ret (src : Nat)
  deriving @[expose] DecidableEq, Repr

/-- Total 64-bit semantics of `ByteBinOp`, matching `Core.Term.primitiveResult` on `< 2^64` inputs. -/
@[expose] def evalByteBinOp (op : ByteBinOp) (a b : UInt64) : UInt64 :=
  match op with
  | .add => a + b | .sub => a - b | .mul => a * b
  | .div => if b == 0 then 0 else a / b | .mod => if b == 0 then a else a % b
  | .eq => if a == b then 1 else 0 | .lt => if a < b then 1 else 0 | .le => if a ≤ b then 1 else 0
  | .conj => if a != 0 && b != 0 then 1 else 0
  | .bitAnd => a &&& b | .bitOr => a ||| b | .bitXor => a ^^^ b

/-- Single-instruction transition returning either `.inl (nextPc, nextRegs)` or `.inr result`.
    Out-of-bounds register indices deterministically refuse (`none`). -/
def stepByteInstr (ins : ByteInstr) (pc : Nat) (regs : Array UInt64) :
    PSum (Nat × Array UInt64) (Option UInt64) :=
  match ins with
  | .loadImm dst imm =>
    if h : dst < regs.size then .inl (pc + 1, regs.set dst imm h) else .inr none
  | .mov dst src =>
    if hd : dst < regs.size then
      if hs : src < regs.size then .inl (pc + 1, regs.set dst regs[src] hd) else .inr none
    else .inr none
  | .binOp op dst lhs rhs =>
    if hd : dst < regs.size then
      if hl : lhs < regs.size then
        if hr : rhs < regs.size then
          .inl (pc + 1, regs.set dst (evalByteBinOp op regs[lhs] regs[rhs]) hd)
        else .inr none
      else .inr none
    else .inr none
  | .jz cond targetPc =>
    if hc : cond < regs.size then
      .inl ((if regs[cond] == 0 then targetPc else pc + 1), regs)
    else .inr none
  | .jmp targetPc => .inl (targetPc, regs)
  | .ret src =>
    if hs : src < regs.size then .inr (some regs[src]) else .inr none

/-- Fuel-indexed bytecode execution starting at arbitrary program counter `pc`. -/
def execBytecodeAt (code : Array ByteInstr) (pc : Nat) (regs : Array UInt64) : Nat → Option UInt64
  | 0 => none
  | fuel + 1 =>
    if hpc : pc < code.size then
      match stepByteInstr code[pc] pc regs with
      | .inl (nextPc, nextRegs) => execBytecodeAt code nextPc nextRegs fuel
      | .inr res => res
    else none

/-- Execute flat `Array ByteInstr` from `pc = 0` over unboxed `Array UInt64` registers. -/
@[expose] def execBytecode (code : Array ByteInstr) (regs : Array UInt64) (fuel : Nat) : Option UInt64 :=
  execBytecodeAt code 0 regs fuel

theorem execBytecode_eq (code : Array ByteInstr) (regs : Array UInt64) (fuel : Nat) :
    execBytecode code regs fuel = execBytecodeAt code 0 regs fuel := rfl

/-! ## 2. Dictionary-Passing & Record-Projection Erasure (`specializeDictTerm`) -/

/-- Multi-pass static reducer stripping dictionary records, projections, and β-redexes. -/
@[expose] def specializeDictTerm (passes : Nat) (t : Term) : Term :=
  dataPinSteps passes t

theorem specializeDictTerm_bequiv (passes : Nat) (t : Term) :
    t ≈b specializeDictTerm passes t :=
  bequiv_dataPinSteps passes t

theorem specializeDictTerm_sameRuns (passes : Nat) (env : List Term) (t : Term) :
    SameRuns (closeTerm env t) (closeTerm env (specializeDictTerm passes t)) := by
  have h := (specializeDictTerm_bequiv passes t) (envSubst env) (.bound 0)
  simpa only [instantiate, Term.substitute, single, closeTerm] using h

private theorem halts_natural_iff_evaluates {u : Term} {n : Nat} :
    Halts u (.natural n) ↔ Evaluates u (.nat n) := by
  constructor
  · rintro ⟨v, hev, hobs⟩; cases hobs; exact hev
  · intro hev; exact ⟨.nat n, hev, .natural n⟩

private theorem halts_boolean_iff_evaluates {u : Term} {b : Bool} :
    Halts u (.boolean b) ↔ Evaluates u (.boolean b) := by
  constructor
  · rintro ⟨v, hev, hobs⟩; cases hobs; exact hev
  · intro hev; exact ⟨.boolean b, hev, .boolean b⟩

/-- Closing `t` and closing `specializeDictTerm passes t` evaluate to the exact same scalar values. -/
theorem specializeDictTerm_evaluates_scalar_iff
    (passes : Nat) (env : List Term) (t v : Term) {I : Interval}
    (hv : ValueInInterval I v) :
    Evaluates (closeTerm env t) v ↔ Evaluates (closeTerm env (specializeDictTerm passes t)) v := by
  have hSame := specializeDictTerm_sameRuns passes env t
  cases hs : I.sort <;> simp only [ValueInInterval, hs] at hv
  · obtain ⟨n, rfl, _, _⟩ := hv
    rw [← halts_natural_iff_evaluates, ← halts_natural_iff_evaluates]
    exact hSame.halts (.natural n)
  · obtain ⟨b, rfl, _, _⟩ := hv
    rw [← halts_boolean_iff_evaluates, ← halts_boolean_iff_evaluates]
    exact hSame.halts (.boolean b)

/-! ## 3. Range-Safe Expression Compiler (`compileExprToBytecode`) & Simulation Proof -/

/-- `Core4` primitives lowered directly to `ByteBinOp`. -/
@[expose] def compilePrimOp : Primitive → Option ByteBinOp
  | .add => some .add | .subtract => some .sub | .multiply => some .mul
  | .divide => some .div | .modulo => some .mod | .equal => some .eq
  | .less => some .lt | .lessEqual => some .le | .conjunction => some .conj
  | .bitAnd => some .bitAnd | .bitOr => some .bitOr | .bitXor => some .bitXor
  | _ => none

/-- Allowed primitive predicate for 64-bit bytecode range certification. -/
@[expose] def isBytecodePrim (op : Primitive) : Bool := (compilePrimOp op).isSome

/-- Certify that all intermediate and output values of `t` fit in `< 2^64` with zero underflow. -/
@[expose] def checkRangeSafeBytecode (Γ : List Interval) (t : Term) : Bool :=
  checkRangeSafeWith isBytecodePrim (2 ^ 64) Γ t

/-- Relocatable expression compiler emitting `(frag, dstReg, maxRegs, fuelBound)` at `basePc`. -/
def compileExprAt (basePc : Nat) (regMap : List Nat) (nextReg : Nat) :
    Term → Option (Array ByteInstr × Nat × Nat × Nat)
  | .nat n => some (#[.loadImm nextReg (UInt64.ofNat n)], nextReg, nextReg + 1, 1)
  | .boolean b => some (#[.loadImm nextReg (if b then 1 else 0)], nextReg, nextReg + 1, 1)
  | .bound idx =>
    match regMap[idx]? with
    | some r => if r < nextReg then some (#[], r, nextReg, 0) else none
    | none => none
  | .app (.lam subBody) arg =>
    match compileExprAt basePc regMap nextReg arg with
    | some (fragArg, rArg, max1, fuelArg) =>
      match compileExprAt (basePc + fragArg.size) (rArg :: regMap) max1 subBody with
      | some (fragBody, rBody, max2, fuelBody) =>
        some (fragArg ++ fragBody, rBody, max2, fuelArg + fuelBody)
      | none => none
    | none => none
  | .binary op l r =>
    match compilePrimOp op with
    | some bop =>
      match compileExprAt basePc regMap nextReg l with
      | some (fragL, rl, max1, fuelL) =>
        match compileExprAt (basePc + fragL.size) regMap max1 r with
        | some (fragR, rr, max2, fuelR) =>
          some (fragL ++ fragR ++ #[.binOp bop max2 rl rr], max2, max2 + 1, fuelL + fuelR + 1)
        | none => none
      | none => none
    | none => none
  | .ifBool c tBranch fBranch =>
    match compileExprAt basePc regMap nextReg c with
    | some (fragC, rc, max1, fuelC) =>
      let dst := max1
      let truePc := basePc + fragC.size + 1
      match compileExprAt truePc regMap (dst + 1) tBranch with
      | some (fragT, rt, max2, fuelT) =>
        let falsePc := truePc + fragT.size + 2
        match compileExprAt falsePc regMap (dst + 1) fBranch with
        | some (fragF, rf, max3, fuelF) =>
          let endPc := falsePc + fragF.size + 1
          let frag := fragC ++ #[.jz rc falsePc] ++ fragT ++ #[.mov dst rt, .jmp endPc] ++
                      fragF ++ #[.mov dst rf]
          some (frag, dst, max max2 max3, fuelC + max fuelT fuelF + 3)
        | none => none
      | none => none
    | none => none
  | .ifZero v z s =>
    match compileExprAt basePc regMap nextReg v with
    | some (fragV, rv, max1, fuelV) =>
      let dst := max1
      let rPred := max1 + 1
      let rOne := max1 + 2
      let succHdrPc := basePc + fragV.size + 1
      match compileExprAt (succHdrPc + 2) (rPred :: regMap) (max1 + 3) s with
      | some (fragS, rs, max2, fuelS) =>
        let zeroPc := succHdrPc + 2 + fragS.size + 2
        match compileExprAt zeroPc regMap (max1 + 3) z with
        | some (fragZ, rz, max3, fuelZ) =>
          let endPc := zeroPc + fragZ.size + 1
          let frag := fragV ++ #[.jz rv zeroPc, .loadImm rOne 1, .binOp .sub rPred rv rOne] ++
                      fragS ++ #[.mov dst rs, .jmp endPc] ++ fragZ ++ #[.mov dst rz]
          some (frag, dst, max max2 max3, fuelV + max (fuelS + 2) fuelZ + 3)
        | none => none
      | none => none
    | none => none
  | _ => none

/-- Specialize dictionary overhead and compile `t` to standalone bytecode ending in `.ret dst`. -/
def compileExprToBytecode (passes : Nat) (regMap : List Nat) (nextReg : Nat) (t : Term) :
    Option (Array ByteInstr × Nat × Nat) :=
  let clean := specializeDictTerm passes t
  match compileExprAt 0 regMap nextReg clean with
  | some (frag, dst, maxRegs, fuelBound) =>
    some (frag ++ #[.ret dst], maxRegs, fuelBound + 1)
  | none => none

/-- Simulation invariant connecting interval environment `Γ`, `Core4` closing environment `env`,
    logical register map `regMap`, and unboxed machine register file `regs`. -/
@[expose] def SimulatesBytecode
    (Γ : List Interval) (regMap : List Nat) (nextReg : Nat)
    (env : List Term) (regs : Array UInt64) : Prop :=
  EnvInIntervals Γ env ∧
  nextReg ≤ regs.size ∧
  ∀ (idx : Nat) (I : Interval), Γ[idx]? = some I →
    ∃ r e v, regMap[idx]? = some r ∧ r < nextReg ∧
      env[idx]? = some e ∧ Evaluates e v ∧ ValueInInterval I v ∧
      regs[r]? = some (UInt64.ofNat (scalarToNat v))

theorem simulatesBytecode_nil (regs : Array UInt64) :
    SimulatesBytecode [] [] 0 [] regs :=
  ⟨envInIntervals_nil, Nat.zero_le _, fun _ _ h => by simp at h⟩

/-- Contiguous instruction slice witness `code[basePc + i] = frag[i]`. -/
def CodeSliceAt (code : Array ByteInstr) (basePc : Nat) (frag : Array ByteInstr) : Prop :=
  basePc + frag.size ≤ code.size ∧
  ∀ (i : Nat) (hi : i < frag.size), code[basePc + i]? = some frag[i]

private theorem get_set_ne {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) (v : α)
    {j : Nat} (hne : i ≠ j) : (xs.set i v h)[j]? = xs[j]? := by
  simp [Array.getElem?_set, hne]

private theorem execBytecodeAt_one_add (code : Array ByteInstr) (pc : Nat) (regs : Array UInt64) (f : Nat) :
    execBytecodeAt code pc regs (1 + f) =
      if hpc : pc < code.size then
        match stepByteInstr code[pc] pc regs with
        | .inl (nPc, nR) => execBytecodeAt code nPc nR f
        | .inr res => res
      else none := by
  rw [Nat.add_comm 1 f]; rfl

private theorem codeSliceAt_self (frag : Array ByteInstr) : CodeSliceAt frag 0 frag :=
  ⟨by simp, fun i hi => by simp [hi]⟩

private theorem codeSliceAt_split {code : Array ByteInstr} {pc : Nat} {a b : Array ByteInstr}
    (h : CodeSliceAt code pc (a ++ b)) :
    CodeSliceAt code pc a ∧ CodeSliceAt code (pc + a.size) b := by
  have hBound : pc + (a.size + b.size) ≤ code.size := by simpa [Array.size_append] using h.1
  refine ⟨⟨by omega, fun i hi => ?_⟩, ⟨by omega, fun j hj => ?_⟩⟩
  · have hi' : i < (a ++ b).size := by simp [Array.size_append]; omega
    have hEq := h.2 i hi'
    rwa [Array.getElem_append_left hi] at hEq
  · have hj' : a.size + j < (a ++ b).size := by simp [Array.size_append]; omega
    have hEq := h.2 (a.size + j) hj'
    rw [show pc + (a.size + j) = pc + a.size + j by omega] at hEq
    simpa [Array.getElem_append_right (Nat.le_add_right a.size j)] using hEq

private theorem codeSliceAt_get0 {code : Array ByteInstr} {pc : Nat} {ins : ByteInstr}
    (h : CodeSliceAt code pc #[ins]) :
    ∃ (hpc : pc < code.size), code[pc] = ins := by
  have hlt : pc < code.size := by have := h.1; simp at this; omega
  have h0 := h.2 0 (by simp)
  simp only [Nat.add_zero, Array.getElem?_eq_getElem hlt, Option.some.injEq] at h0
  exact ⟨hlt, h0⟩

private theorem codeSliceAt_pc_eq {code : Array ByteInstr} {pc1 pc2 : Nat} {frag : Array ByteInstr}
    (h : CodeSliceAt code pc1 frag) (hp : pc1 = pc2) : CodeSliceAt code pc2 frag := hp ▸ h
private theorem codeSliceAt_frag_eq {code : Array ByteInstr} {pc : Nat} {f1 f2 : Array ByteInstr}
    (h : CodeSliceAt code pc f1) (hf : f1 = f2) : CodeSliceAt code pc f2 := hf ▸ h
private theorem codeSliceAt_get0_at {code : Array ByteInstr} {pc1 pc2 : Nat} {ins : ByteInstr}
    (h : CodeSliceAt code pc1 #[ins]) (hp : pc1 = pc2) :
    ∃ (hpc : pc2 < code.size), code[pc2] = ins := codeSliceAt_get0 (hp ▸ h)

private theorem compileExprAt_bounds {basePc : Nat} {regMap : List Nat} {nextReg : Nat} {t : Term}
    {frag : Array ByteInstr} {dst maxRegs fuel : Nat}
    (hc : compileExprAt basePc regMap nextReg t = some (frag, dst, maxRegs, fuel)) :
    nextReg ≤ maxRegs ∧ dst < maxRegs := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _ | .prototype _ _ | .reflect _
  | .metadata _ | .project _ | .label _ | .extend _ _ | .record _ | .get _ _ | .inject _ _
  | .case _ _ | .perform _ | .done _ | .split _ _ _ => simp [compileExprAt] at hc
  | .nat _ | .boolean _ =>
    simp only [compileExprAt, Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨_, rfl, rfl, _⟩; omega
  | .bound idx =>
    simp only [compileExprAt] at hc; cases hr : regMap[idx]? <;> simp [hr] at hc
    rcases hc with ⟨hlt, _, rfl, rfl, _⟩; exact ⟨Nat.le_refl _, hlt⟩
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [compileExprAt] at hc
      cases h1 : compileExprAt basePc regMap nextReg arg <;> simp only [h1] at hc
      · simp at hc
      · rename_i r1; rcases r1 with ⟨fa, ra, m1, f1⟩
        cases h2 : compileExprAt (basePc + fa.size) (ra :: regMap) m1 subBody <;> simp [h2] at hc
        rcases hc with ⟨_, rfl, rfl, _⟩
        have := compileExprAt_bounds h1; have := compileExprAt_bounds h2; omega
    | _ => simp [compileExprAt] at hc
  | .binary op l r =>
    simp only [compileExprAt] at hc; cases hop : compilePrimOp op <;> simp only [hop] at hc
    · simp at hc
    · cases h1 : compileExprAt basePc regMap nextReg l <;> simp only [h1] at hc
      · simp at hc
      · rename_i r1; rcases r1 with ⟨fl, rl, m1, f1⟩
        cases h2 : compileExprAt (basePc + fl.size) regMap m1 r <;> simp [h2] at hc
        rcases hc with ⟨_, rfl, rfl, _⟩
        have := compileExprAt_bounds h1; have := compileExprAt_bounds h2; omega
  | .ifBool c tB fB =>
    simp only [compileExprAt] at hc
    cases h1 : compileExprAt basePc regMap nextReg c <;> simp only [h1] at hc
    · simp at hc
    · rename_i r1; rcases r1 with ⟨fc, rc, m1, f1⟩
      cases h2 : compileExprAt (basePc + fc.size + 1) regMap (m1 + 1) tB <;> simp only [h2] at hc
      · simp at hc
      · rename_i r2; rcases r2 with ⟨ft, rt, m2, f2⟩
        cases h3 : compileExprAt (basePc + fc.size + 1 + ft.size + 2) regMap (m1 + 1) fB <;> simp [h3] at hc
        rcases hc with ⟨_, rfl, rfl, _⟩
        have := compileExprAt_bounds h1; have := compileExprAt_bounds h2; have := compileExprAt_bounds h3; omega
  | .ifZero v z s =>
    simp only [compileExprAt] at hc
    cases h1 : compileExprAt basePc regMap nextReg v <;> simp only [h1] at hc
    · simp at hc
    · rename_i r1; rcases r1 with ⟨fv, rv, m1, f1⟩
      cases h2 : compileExprAt (basePc + fv.size + 1 + 2) ((m1 + 1) :: regMap) (m1 + 3) s <;> simp only [h2] at hc
      · simp at hc
      · rename_i r2; rcases r2 with ⟨fs, rs, m2, f2⟩
        cases h3 : compileExprAt (basePc + fv.size + 1 + 2 + fs.size + 2) regMap (m1 + 3) z <;> simp [h3] at hc
        rcases hc with ⟨_, rfl, rfl, _⟩
        have := compileExprAt_bounds h1; have := compileExprAt_bounds h2; have := compileExprAt_bounds h3; omega

theorem compileExprAt_complete
    (basePc : Nat) (Γ : List Interval) (regMap : List Nat) (nextReg : Nat) (t : Term)
    (hSafe : checkRangeSafeBytecode Γ t = true)
    (hMap : ∀ (idx : Nat) (I : Interval), Γ[idx]? = some I → ∃ r, regMap[idx]? = some r ∧ r < nextReg) :
    ∃ frag dst maxRegs fuel, compileExprAt basePc regMap nextReg t = some (frag, dst, maxRegs, fuel) := by
  unfold checkRangeSafeBytecode at hSafe
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _ | .prototype _ _ | .reflect _
  | .metadata _ | .project _ | .label _ | .extend _ _ | .record _ | .get _ _ | .inject _ _
  | .case _ _ | .perform _ | .done _ | .split _ _ _ => simp [checkRangeSafeWith] at hSafe
  | .nat _ | .boolean _ => exact ⟨_, _, _, _, rfl⟩
  | .bound idx =>
    simp only [checkRangeSafeWith] at hSafe; cases hG : Γ[idx]? <;> simp [hG] at hSafe
    rename_i I; obtain ⟨r, hr, hlt⟩ := hMap idx I hG
    exact ⟨#[], r, nextReg, 0, by simp [compileExprAt, hr, hlt]⟩
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafe; cases hArg : inferRange Γ arg <;> simp [hArg] at hSafe
      rename_i iArg
      obtain ⟨fa, ra, m1, f1, hc1⟩ := compileExprAt_complete basePc Γ regMap nextReg arg hSafe.1.2 hMap
      have hb1 := compileExprAt_bounds hc1
      have hMap' : ∀ (idx : Nat) (J : Interval), (iArg :: Γ)[idx]? = some J → ∃ r, (ra :: regMap)[idx]? = some r ∧ r < m1 := by
        intro idx J hJ; cases idx with
        | zero => exact ⟨ra, rfl, hb1.2⟩
        | succ k => obtain ⟨r, hr, hlt⟩ := hMap k J hJ; exact ⟨r, hr, Nat.lt_of_lt_of_le hlt hb1.1⟩
      obtain ⟨fb, rb, m2, f2, hc2⟩ := compileExprAt_complete (basePc + fa.size) (iArg :: Γ) (ra :: regMap) m1 subBody hSafe.2 hMap'
      exact ⟨_, _, _, _, by simp only [compileExprAt, hc1, hc2]; rfl⟩
    | _ => simp [checkRangeSafeWith] at hSafe
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    obtain ⟨⟨⟨hPrim, hSafeL⟩, hSafeR⟩, _⟩ := hSafe
    obtain ⟨bop, hbop⟩ := Option.isSome_iff_exists.mp hPrim
    obtain ⟨fl, rl, m1, f1, hc1⟩ := compileExprAt_complete basePc Γ regMap nextReg l hSafeL hMap
    have hb1 := compileExprAt_bounds hc1
    have hMap1 : ∀ (idx : Nat) (J : Interval), Γ[idx]? = some J → ∃ reg, regMap[idx]? = some reg ∧ reg < m1 := by
      intro idx J hJ; obtain ⟨reg, hr, hlt⟩ := hMap idx J hJ; exact ⟨reg, hr, Nat.lt_of_lt_of_le hlt hb1.1⟩
    obtain ⟨fr, rr, m2, f2, hc2⟩ := compileExprAt_complete (basePc + fl.size) Γ regMap m1 r hSafeR hMap1
    exact ⟨_, _, _, _, by simp only [compileExprAt, hbop, hc1, hc2]; rfl⟩
  | .ifBool c tB fB =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    obtain ⟨⟨⟨hSafeC, hSafeT⟩, hSafeF⟩, _⟩ := hSafe
    obtain ⟨fc, rc, m1, f1, hc1⟩ := compileExprAt_complete basePc Γ regMap nextReg c hSafeC hMap
    have hb1 := compileExprAt_bounds hc1
    have hMap1 : ∀ (idx : Nat) (J : Interval), Γ[idx]? = some J → ∃ reg, regMap[idx]? = some reg ∧ reg < m1 + 1 := by
      intro idx J hJ; obtain ⟨reg, hr, hlt⟩ := hMap idx J hJ; exact ⟨reg, hr, by omega⟩
    obtain ⟨ft, rt, m2, f2, hc2⟩ := compileExprAt_complete (basePc + fc.size + 1) Γ regMap (m1 + 1) tB hSafeT hMap1
    obtain ⟨ff, rf, m3, f3, hc3⟩ := compileExprAt_complete (basePc + fc.size + 1 + ft.size + 2) Γ regMap (m1 + 1) fB hSafeF hMap1
    exact ⟨_, _, _, _, by simp only [compileExprAt, hc1, hc2, hc3]; rfl⟩
  | .ifZero v z s =>
    simp only [checkRangeSafeWith] at hSafe; cases hv : inferRange Γ v <;> simp only [hv] at hSafe
    · simp at hSafe
    · rename_i iv; cases hOut : inferRange Γ (.ifZero v z s) <;> simp [hOut] at hSafe
      obtain ⟨⟨⟨_, hSafeV⟩, hSafeZ⟩, hSafeS⟩ := hSafe
      obtain ⟨fv, rv, m1, f1, hc1⟩ := compileExprAt_complete basePc Γ regMap nextReg v hSafeV hMap
      have hb1 := compileExprAt_bounds hc1
      have hMapZ : ∀ (idx : Nat) (J : Interval), Γ[idx]? = some J → ∃ reg, regMap[idx]? = some reg ∧ reg < m1 + 3 := by
        intro idx J hJ; obtain ⟨reg, hr, hlt⟩ := hMap idx J hJ; exact ⟨reg, hr, by omega⟩
      have hMapS : ∀ (idx : Nat) (J : Interval), (Interval.pred iv :: Γ)[idx]? = some J → ∃ reg, ((m1 + 1) :: regMap)[idx]? = some reg ∧ reg < m1 + 3 := by
        intro idx J hJ; cases idx with
        | zero => exact ⟨m1 + 1, rfl, by omega⟩
        | succ k => obtain ⟨reg, hr, hlt⟩ := hMap k J hJ; exact ⟨reg, hr, by omega⟩
      obtain ⟨fs, rs, m2, f2, hc2⟩ := compileExprAt_complete (basePc + fv.size + 1 + 2) (Interval.pred iv :: Γ) ((m1 + 1) :: regMap) (m1 + 3) s hSafeS hMapS
      obtain ⟨fz, rz, m3, f3, hc3⟩ := compileExprAt_complete (basePc + fv.size + 1 + 2 + fs.size + 2) Γ regMap (m1 + 3) z hSafeZ hMapZ
      exact ⟨_, _, _, _, by simp only [compileExprAt, hc1, hc2, hc3]; rfl⟩

private theorem uint64_toNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem uint64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem uint64_beq_zero_false {n : Nat} (h0 : n ≠ 0) (hlt : n < 2 ^ 64) :
    (UInt64.ofNat n == 0) = false := by
  apply Bool.eq_false_iff.mpr; intro hEq
  have ht := congrArg UInt64.toNat (eq_of_beq hEq)
  rw [uint64_toNat_of_lt hlt] at ht; exact h0 ht

private theorem valNat {I : Interval} {v : Term} (hs : I.sort = .nat) (h : ValueInInterval I v) :
    ∃ n, v = .nat n ∧ I.lo ≤ n ∧ n ≤ I.hi := by
  unfold ValueInInterval at h; rw [hs] at h; exact h

private theorem valBool {I : Interval} {v : Term} (hs : I.sort = .bool) (h : ValueInInterval I v) :
    ∃ b, v = .boolean b ∧ (I.lo ≤ if b then 1 else 0) ∧ (if b then 1 else 0) ≤ I.hi := by
  unfold ValueInInterval at h; rw [hs] at h; exact h

private theorem evalByteBinOp_matches_prim
    {op : Primitive} {bop : ByteBinOp} {il ir iOut : Interval} {vl vr vOut : Term}
    (hOp : compilePrimOp op = some bop) (hPrimRange : inferPrimRange op il ir = some iOut)
    (hSubSafe : (if op == .subtract then decide (ir.hi ≤ il.lo) else true) = true)
    (hInL : ValueInInterval il vl) (hLtL : il.hi < 2 ^ 64)
    (hInR : ValueInInterval ir vr) (hLtR : ir.hi < 2 ^ 64)
    (hPrimRes : primitiveResult op vl vr = some vOut) :
    evalByteBinOp bop (UInt64.ofNat (scalarToNat vl)) (UInt64.ofNat (scalarToNat vr)) =
      UInt64.ofNat (scalarToNat vOut) := by
  cases op with
  | labelEqual | shl | lshr | ashr | slt | qmul32 => simp [compilePrimOp] at hOp
  | conjunction =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    simp only [inferPrimRange] at hPrimRange
    by_cases hs : (il.sort == .bool && ir.sort == .bool) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨ba, rfl, _, _⟩ := valBool hs.1 hInL; obtain ⟨bb, rfl, _, _⟩ := valBool hs.2 hInR
      simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
      cases ba <;> cases bb <;> decide
    · simp [hs] at hPrimRange
  | add =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, _⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, _⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    simp [evalByteBinOp, scalarToNat, UInt64.ofNat_add]
  | multiply =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, _⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, _⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    simp [evalByteBinOp, scalarToNat, UInt64.ofNat_mul]
  | subtract =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    simp only [beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at hSubSafe
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    obtain ⟨na, rfl, hal, hah⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, hbh⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    apply uint64_eq_of_toNat
    have hna : na < 2 ^ 64 := by omega
    have hnb : nb < 2 ^ 64 := by omega
    have hle : nb ≤ na := by omega
    have hsub : na - nb < 2 ^ 64 := by omega
    have hLeU : UInt64.ofNat nb ≤ UInt64.ofNat na := by
      rw [UInt64.le_iff_toNat_le, uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb]; exact hle
    simp only [evalByteBinOp, scalarToNat, UInt64.toNat_sub_of_le _ _ hLeU,
      uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb, uint64_toNat_of_lt hsub]
  | divide =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr⟩ : il.sort = .nat ∧ ir.sort = .nat := by
      simp only [inferPrimRange] at hPrimRange; split at hPrimRange
      · exact ⟨(natOut_eq_some hPrimRange).1, (natOut_eq_some hPrimRange).2.1⟩
      · exact ⟨(natOut_eq_some hPrimRange).1, (natOut_eq_some hPrimRange).2.1⟩
    obtain ⟨na, rfl, _, hah⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, hbh⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < 2 ^ 64 := by omega
    have hnb : nb < 2 ^ 64 := by omega
    apply uint64_eq_of_toNat; by_cases h0 : nb = 0
    · subst h0; simp [evalByteBinOp, scalarToNat]
    · have hdiv : na / nb < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self na nb) hna
      simp [evalByteBinOp, uint64_beq_zero_false h0 hnb, scalarToNat, UInt64.toNat_div, uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb, uint64_toNat_of_lt hdiv]
  | modulo =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr⟩ : il.sort = .nat ∧ ir.sort = .nat := by
      simp only [inferPrimRange] at hPrimRange; split at hPrimRange
      · exact ⟨(natOut_eq_some hPrimRange).1, (natOut_eq_some hPrimRange).2.1⟩
      · exact ⟨(natOut_eq_some hPrimRange).1, (natOut_eq_some hPrimRange).2.1⟩
    obtain ⟨na, rfl, _, hah⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, hbh⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < 2 ^ 64 := by omega
    have hnb : nb < 2 ^ 64 := by omega
    apply uint64_eq_of_toNat; by_cases h0 : nb = 0
    · subst h0; simp [evalByteBinOp, scalarToNat, uint64_toNat_of_lt hna]
    · have hmod : na % nb < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le na nb) hna
      simp [evalByteBinOp, uint64_beq_zero_false h0 hnb, scalarToNat, UInt64.toNat_mod, uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb, uint64_toNat_of_lt hmod]
  | equal =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, hah⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, hbh⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < 2 ^ 64 := by omega
    have hnb : nb < 2 ^ 64 := by omega
    have hEqIff : (UInt64.ofNat na == UInt64.ofNat nb) = (na == nb) := by
      by_cases h : na = nb
      · subst h; simp
      · rw [beq_eq_false_iff_ne.mpr h]; apply Bool.eq_false_iff.mpr
        intro hc; have ht := congrArg UInt64.toNat (beq_iff_eq.mp hc)
        rw [uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb] at ht; exact h ht
    simp only [evalByteBinOp, scalarToNat, hEqIff]; cases (na == nb) <;> rfl
  | less =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, hah⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, hbh⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < 2 ^ 64 := by omega
    have hnb : nb < 2 ^ 64 := by omega
    simp only [evalByteBinOp, scalarToNat, UInt64.lt_iff_toNat_lt, uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb]
    by_cases h : na < nb <;> simp [h]
  | lessEqual =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, hah⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, hbh⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < 2 ^ 64 := by omega
    have hnb : nb < 2 ^ 64 := by omega
    simp only [evalByteBinOp, scalarToNat, UInt64.le_iff_toNat_le, uint64_toNat_of_lt hna, uint64_toNat_of_lt hnb]
    by_cases h : na ≤ nb <;> simp [h]
  | bitAnd =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, _⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, _⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    apply uint64_eq_of_toNat
    simp [evalByteBinOp, scalarToNat, word64, uint64_toNat_of_lt (word64 na &&& word64 nb).isLt, UInt64.toNat_and, UInt64.toNat_ofNat]
  | bitOr =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, _⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, _⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    apply uint64_eq_of_toNat
    simp [evalByteBinOp, scalarToNat, word64, uint64_toNat_of_lt (word64 na ||| word64 nb).isLt, UInt64.toNat_or, UInt64.toNat_ofNat]
  | bitXor =>
    simp only [compilePrimOp, Option.some.injEq] at hOp; subst hOp
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    obtain ⟨na, rfl, _, _⟩ := valNat hsl hInL; obtain ⟨nb, rfl, _, _⟩ := valNat hsr hInR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    apply uint64_eq_of_toNat
    simp [evalByteBinOp, scalarToNat, word64, uint64_toNat_of_lt (word64 na ^^^ word64 nb).isLt, UInt64.toNat_xor, UInt64.toNat_ofNat]

private theorem simulatesBytecode_mono_regs
    {Γ : List Interval} {regMap : List Nat} {n1 n2 : Nat} {env : List Term} {r1 r2 : Array UInt64}
    (hSim : SimulatesBytecode Γ regMap n1 env r1)
    (hn : n1 ≤ n2) (hSz : n2 ≤ r2.size)
    (hPres : ∀ r < n1, r2[r]? = r1[r]?) :
    SimulatesBytecode Γ regMap n2 env r2 := by
  refine ⟨hSim.1, hSz, fun idx I hI => ?_⟩
  obtain ⟨r, e, v, hr, hlt, henv, hev, hval, hreg⟩ := hSim.2.2 idx I hI
  exact ⟨r, e, v, hr, Nat.lt_of_lt_of_le hlt hn, henv, hev, hval, (hPres r hlt).trans hreg⟩

private theorem simulatesBytecode_cons
    {I : Interval} {Γ : List Interval} {rNew nextReg : Nat} {e v : Term} {env : List Term}
    {regMap : List Nat} {regs : Array UInt64}
    (hSim : SimulatesBytecode Γ regMap nextReg env regs)
    (hrLt : rNew < nextReg) (he : Evaluates e v) (hv : ValueInInterval I v)
    (hRegVal : regs[rNew]? = some (UInt64.ofNat (scalarToNat v))) :
    SimulatesBytecode (I :: Γ) (rNew :: regMap) nextReg (e :: env) regs := by
  refine ⟨envInIntervals_cons he hv hSim.1, hSim.2.1, fun idx J hJ => ?_⟩
  cases idx with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ
    exact ⟨rNew, e, v, rfl, hrLt, rfl, he, hv, hRegVal⟩
  | succ k =>
    simp only [List.getElem?_cons_succ] at hJ ⊢
    exact hSim.2.2 k J hJ

/-- **Relocatable Region Simulation (`compileExprAt_sound`)**:
    Executing any compiled expression slice `frag` inside `code` advances `pc` from `basePc` to
    `basePc + frag.size` in `used ≤ fuelBound` steps without modifying registers `< nextReg`,
    depositing `UInt64.ofNat (scalarToNat v)` into `dst`. -/
theorem compileExprAt_sound
    (code : Array ByteInstr) (basePc : Nat) (Γ : List Interval)
    (regMap : List Nat) (nextReg : Nat) (t : Term)
    (frag : Array ByteInstr) (dst maxRegs fuelBound : Nat)
    (env : List Term) (regs : Array UInt64)
    (hSafe : checkRangeSafeBytecode Γ t = true)
    (hComp : compileExprAt basePc regMap nextReg t = some (frag, dst, maxRegs, fuelBound))
    (hSlice : CodeSliceAt code basePc frag)
    (hSim : SimulatesBytecode Γ regMap nextReg env regs)
    (hMaxSz : maxRegs ≤ regs.size) :
    ∃ (I : Interval) (v : Term) (used : Nat) (regs' : Array UInt64),
      inferRange Γ t = some I ∧ I.hi < 2 ^ 64 ∧
      Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      used ≤ fuelBound ∧
      regs'.size = regs.size ∧
      (∀ r < nextReg, regs'[r]? = regs[r]?) ∧
      regs'[dst]? = some (UInt64.ofNat (scalarToNat v)) ∧
      (∀ restFuel, execBytecodeAt code basePc regs (used + restFuel) =
        execBytecodeAt code (basePc + frag.size) regs' restFuel) := by
  have hb := compileExprAt_bounds hComp
  unfold checkRangeSafeBytecode at hSafe
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _ | .prototype _ _ | .reflect _
  | .metadata _ | .project _ | .label _ | .extend _ _ | .record _ | .get _ _ | .inject _ _
  | .case _ _ | .perform _ | .done _ | .split _ _ _ => simp [compileExprAt] at hComp
  | .nat n =>
    simp only [checkRangeSafeWith, decide_eq_true_eq] at hSafe
    simp only [compileExprAt, Option.some.injEq, Prod.mk.injEq] at hComp; rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨hpc, hins⟩ := codeSliceAt_get0 hSlice
    have hDstLt : nextReg < regs.size := by omega
    refine ⟨_, .nat n, 1, regs.set nextReg (UInt64.ofNat n) hDstLt, rfl, hSafe, ?_, ⟨n, rfl, Nat.le_refl n, Nat.le_refl n⟩,
      Nat.le_refl 1, by simp, fun r hr => get_set_ne _ _ _ _ (by omega), by simp [Array.getElem?_set_self, scalarToNat], ?_⟩
    · simp only [closeTerm, Term.substitute]; exact ⟨.refl _, .natural n⟩
    · intro restFuel; rw [execBytecodeAt_one_add]; simp [hpc, hins, stepByteInstr, hDstLt]
  | .boolean b =>
    simp only [checkRangeSafeWith, decide_eq_true_eq] at hSafe
    simp only [compileExprAt, Option.some.injEq, Prod.mk.injEq] at hComp; rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨hpc, hins⟩ := codeSliceAt_get0 hSlice
    have hDstLt : nextReg < regs.size := by omega
    let k := if b then 1 else 0
    refine ⟨{ lo := k, hi := k, sort := .bool, wf := Nat.le_refl k }, .boolean b, 1,
      regs.set nextReg (if b then 1 else 0) hDstLt, rfl, by cases b <;> decide, ?_, ⟨b, rfl, Nat.le_refl _, Nat.le_refl _⟩,
      Nat.le_refl 1, by simp, fun r hr => get_set_ne _ _ _ _ (by omega), by cases b <;> simp [Array.getElem?_set_self, scalarToNat], ?_⟩
    · simp only [closeTerm, Term.substitute]; exact ⟨.refl _, .boolean b⟩
    · intro restFuel; rw [execBytecodeAt_one_add]; simp [hpc, hins, stepByteInstr, hDstLt]
  | .bound idx =>
    simp only [checkRangeSafeWith] at hSafe; cases hG : Γ[idx]? <;> simp only [hG] at hSafe
    · simp at hSafe
    · rename_i I; simp only [Bool.and_eq_true, decide_eq_true_eq] at hSafe
      obtain ⟨r, e, v, hr, hrLt, henv, hev, hval, hreg⟩ := hSim.2.2 idx I hG
      simp only [compileExprAt, hr, hrLt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hComp
      rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨I, v, 0, regs, by simp [inferRange, hG], hSafe.1, ?_, hval, Nat.le_refl 0, rfl, fun _ _ => rfl, hreg, fun _ => by simp⟩
      simp only [closeTerm, Term.substitute, envSubst, henv]; exact hev
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafe; cases hArgI : inferRange Γ arg <;> simp only [hArgI] at hSafe
      · simp at hSafe
      · rename_i iArg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hSafe
        simp only [compileExprAt] at hComp
        cases hc1 : compileExprAt basePc regMap nextReg arg <;> simp only [hc1] at hComp
        · simp at hComp
        · rename_i res1; rcases res1 with ⟨fa, ra, m1, f1⟩
          cases hc2 : compileExprAt (basePc + fa.size) (ra :: regMap) m1 subBody <;> simp only [hc2] at hComp
          · simp at hComp
          · rename_i res2; rcases res2 with ⟨fb, rb, m2, f2⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hComp; rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨hSlA, hSlB⟩ := codeSliceAt_split hSlice
            have hb1 := compileExprAt_bounds hc1; have hb2 := compileExprAt_bounds hc2
            obtain ⟨iA, vA, u1, regs1, hInfA, _, hEvA, hInA, hu1, hSz1, hPr1, hDst1, hEx1⟩ :=
              compileExprAt_sound code basePc Γ regMap nextReg arg fa ra m1 f1 env regs hSafe.1.2 hc1 hSlA hSim (by omega)
            rw [hArgI] at hInfA; injection hInfA with hEqI; subst hEqI
            have hSim1 := simulatesBytecode_cons (simulatesBytecode_mono_regs hSim hb1.1 (by omega) hPr1) hb1.2 hEvA hInA hDst1
            obtain ⟨iB, vB, u2, regs2, hInfB, hHiB, hEvB, hInB, hu2, hSz2, hPr2, hDst2, hEx2⟩ :=
              compileExprAt_sound code (basePc + fa.size) (iArg :: Γ) (ra :: regMap) m1 subBody fb rb m2 f2
                (closeTerm env arg :: env) regs1 hSafe.2 hc2 hSlB hSim1 (by omega)
            have hEvLet : Evaluates (closeTerm env (.app (.lam subBody) arg)) vB := by
              refine ⟨?_, hEvB.2⟩; simp only [closeTerm, Term.substitute]
              have st : Step (.app (.lam (subBody.substitute (liftSubstitution (envSubst env)))) (arg.substitute (envSubst env)))
                  (instantiate (subBody.substitute (liftSubstitution (envSubst env))) (arg.substitute (envSubst env))) := .beta _ _
              rw [instantiate_closeTerm_lift] at st; exact .next st hEvB.1
            refine ⟨iB, vB, u1 + u2, regs2, by simp [inferRange, hArgI, hInfB], hHiB, hEvLet, hInB,
              Nat.add_le_add hu1 hu2, hSz2.trans hSz1, fun r hr => (hPr2 r (Nat.lt_of_lt_of_le hr hb1.1)).trans (hPr1 r hr), hDst2, ?_⟩
            intro restFuel; rw [Nat.add_assoc, hEx1 (u2 + restFuel), hEx2 restFuel, Array.size_append, Nat.add_assoc]
    | _ => simp [compileExprAt] at hComp
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe; obtain ⟨⟨⟨_, hSafeL⟩, hSafeR⟩, hRest⟩ := hSafe
    simp only [compileExprAt] at hComp; cases hOp : compilePrimOp op <;> simp only [hOp] at hComp
    · simp at hComp
    · rename_i bop; cases hc1 : compileExprAt basePc regMap nextReg l <;> simp only [hc1] at hComp
      · simp at hComp
      · rename_i res1; rcases res1 with ⟨fl, rl, m1, f1⟩
        cases hc2 : compileExprAt (basePc + fl.size) regMap m1 r <;> simp only [hc2] at hComp
        · simp at hComp
        · rename_i res2; rcases res2 with ⟨fr, rr, m2, f2⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hComp; rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
          have hb1 := compileExprAt_bounds hc1; have hb2 := compileExprAt_bounds hc2
          obtain ⟨hSlLR, hSlOp⟩ := codeSliceAt_split hSlice; obtain ⟨hSlL, hSlR⟩ := codeSliceAt_split hSlLR
          obtain ⟨il, vl, u1, regs1, hInfL, hHiL, hEvL, hInL, hu1, hSz1, hPr1, hDst1, hEx1⟩ :=
            compileExprAt_sound code basePc Γ regMap nextReg l fl rl m1 f1 env regs hSafeL hc1 hSlL hSim (by omega)
          have hSim1 := simulatesBytecode_mono_regs hSim hb1.1 (by omega) hPr1
          obtain ⟨ir, vr, u2, regs2, hInfR, hHiR, hEvR, hInR, hu2, hSz2, hPr2, hDst2, hEx2⟩ :=
            compileExprAt_sound code (basePc + fl.size) Γ regMap m1 r fr rr m2 f2 env regs1 hSafeR hc2 hSlR hSim1 (by omega)
          simp only [hInfL, hInfR] at hRest; cases hOut : inferPrimRange op il ir <;> simp only [hOut] at hRest
          · simp at hRest
          · rename_i iOut; simp only [Bool.and_eq_true, decide_eq_true_eq] at hRest
            obtain ⟨vOut, hPrimRes, hInOut⟩ := inferPrimRange_sound hOut hInL hInR
            have hEvBin : Evaluates (closeTerm env (.binary op l r)) vOut := by
              refine ⟨?_, valueInInterval_is_value hInOut⟩; simp only [closeTerm, Term.substitute]
              exact Equiv.steps_trans (steps_binaryLeft _ hEvL.1) (Equiv.steps_trans (steps_binaryRight hEvL.2 hEvR.1)
                (.next (.primitive op vl vr vOut hEvL.2 hEvR.2 hPrimRes) (.refl vOut)))
            have hRl2 : regs2[rl]? = some (UInt64.ofNat (scalarToNat vl)) := (hPr2 rl hb1.2).trans hDst1
            have hRlLt : rl < regs2.size := by omega
            have hRrLt : rr < regs2.size := by omega
            have hDstLt : m2 < regs2.size := by omega
            have hRlVal : regs2[rl] = UInt64.ofNat (scalarToNat vl) := by rw [Array.getElem?_eq_getElem hRlLt] at hRl2; injection hRl2
            have hRrVal : regs2[rr] = UInt64.ofNat (scalarToNat vr) := by rw [Array.getElem?_eq_getElem hRrLt] at hDst2; injection hDst2
            have hAlu := evalByteBinOp_matches_prim hOp hOut hRest.2 hInL hHiL hInR hHiR hPrimRes
            rw [Array.size_append] at hSlOp; obtain ⟨hpcOp, hinsOp⟩ := codeSliceAt_get0 hSlOp
            let regs3 := regs2.set m2 (UInt64.ofNat (scalarToNat vOut)) hDstLt
            refine ⟨iOut, vOut, u1 + u2 + 1, regs3, by simp [inferRange, hInfL, hInfR, hOut], hRest.1,
              hEvBin, hInOut, by omega, (Array.size_set ..).trans (hSz2.trans hSz1), ?_, by simp [regs3, Array.getElem?_set_self], ?_⟩
            · intro reg hr; rw [get_set_ne _ _ _ _ (by omega)]; exact (hPr2 reg (Nat.lt_of_lt_of_le hr hb1.1)).trans (hPr1 reg hr)
            · intro restFuel
              have hStepOp : execBytecodeAt code (basePc + (fl.size + fr.size)) regs2 (1 + restFuel) =
                  execBytecodeAt code (basePc + (fl.size + fr.size) + 1) regs3 restFuel := by
                rw [execBytecodeAt_one_add]; simp [hpcOp, hinsOp, stepByteInstr, hDstLt, hRlLt, hRrLt, hRlVal, hRrVal, hAlu, regs3]
              rw [Nat.add_assoc u1 u2 1, Nat.add_assoc u1 (u2 + 1) restFuel, hEx1 ((u2 + 1) + restFuel),
                Nat.add_assoc u2 1 restFuel, hEx2 (1 + restFuel), show basePc + fl.size + fr.size = basePc + (fl.size + fr.size) by omega, hStepOp]
              simp [Array.size_append, Nat.add_assoc]
  | .ifBool c tB fB =>
    simp only [checkRangeSafeWith, Bool.and_eq_true, decide_eq_true_eq] at hSafe
    obtain ⟨⟨⟨hSafeC, hSafeT⟩, hSafeF⟩, hJoinCheck⟩ := hSafe; simp only [compileExprAt] at hComp
    cases hc1 : compileExprAt basePc regMap nextReg c <;> simp only [hc1] at hComp
    · simp at hComp
    · rename_i res1; rcases res1 with ⟨fc, rc, m1, f1⟩
      cases hc2 : compileExprAt (basePc + fc.size + 1) regMap (m1 + 1) tB <;> simp only [hc2] at hComp
      · simp at hComp
      · rename_i res2; rcases res2 with ⟨ft, rt, m2, f2⟩
        cases hc3 : compileExprAt (basePc + fc.size + 1 + ft.size + 2) regMap (m1 + 1) fB <;> simp only [hc3] at hComp
        · simp at hComp
        · rename_i res3; rcases res3 with ⟨ff, rf, m3, f3⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hComp; rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
          have hb1 := compileExprAt_bounds hc1; have hb2 := compileExprAt_bounds hc2; have hb3 := compileExprAt_bounds hc3
          have hMaxL := Nat.le_max_left m2 m3; have hMaxR := Nat.le_max_right m2 m3
          have hFuelL := Nat.le_max_left f2 f3; have hFuelR := Nat.le_max_right f2 f3
          have hSimSz := hSim.2.1
          cases hOut : inferRange Γ (.ifBool c tB fB) <;> simp only [hOut, decide_eq_true_eq] at hJoinCheck
          · simp at hJoinCheck
          · rename_i iOut
            obtain ⟨hSlPre5, hSlMovF⟩ := codeSliceAt_split hSlice; obtain ⟨hSlPre4, hSlF⟩ := codeSliceAt_split hSlPre5
            obtain ⟨hSlPre3, hSlMovT⟩ := codeSliceAt_split hSlPre4; obtain ⟨hSlPre2, hSlT⟩ := codeSliceAt_split hSlPre3
            obtain ⟨hSlC, hSlJz⟩ := codeSliceAt_split hSlPre2
            obtain ⟨ic, vc, uC, regsC, hInfC, _, hEvC, hInC, huC, hSzC, hPrC, hDstC, hExC⟩ :=
              compileExprAt_sound code basePc Γ regMap nextReg c fc rc m1 f1 env regs hSafeC hc1 hSlC hSim (by omega)
            have hIfInf := hOut; simp only [inferRange, hInfC] at hIfInf
            cases hInfT : inferRange Γ tB <;> simp only [hInfT] at hIfInf
            · simp at hIfInf
            · rename_i it; cases hInfF : inferRange Γ fB <;> simp only [hInfF] at hIfInf
              · simp at hIfInf
              · rename_i iff
                cases hSort : (ic.sort == .bool) with
                | false => simp [hSort] at hIfInf
                | true =>
                  simp only [hSort, ↓reduceIte] at hIfInf
                  obtain ⟨b, rfl, _, _⟩ := valBool (beq_iff_eq.mp hSort) hInC
                  obtain ⟨hpcJz, hinsJz⟩ := codeSliceAt_get0 hSlJz
                  have hRcLt : rc < regsC.size := by omega
                  have hRcVal : regsC[rc] = if b then 1 else 0 := by
                    rw [Array.getElem?_eq_getElem hRcLt] at hDstC; injection hDstC with hEq
                    cases b <;> simpa [scalarToNat] using hEq
                  have hSimBranch : SimulatesBytecode Γ regMap (m1 + 1) env regsC :=
                    simulatesBytecode_mono_regs hSim (by omega) (by omega) (fun reg hr => hPrC reg hr)
                  cases b with
                  | true =>
                    obtain ⟨it', vt, uT, regsT, hInfT', _, hEvT, hInT, huT, hSzT, hPrT, hDstT, hExT⟩ :=
                      compileExprAt_sound code (basePc + fc.size + 1) Γ regMap (m1 + 1) tB ft rt m2 f2 env regsC
                        hSafeT hc2 (codeSliceAt_pc_eq hSlT (by simp [Array.size_append]; omega)) hSimBranch (by omega)
                    rw [hInfT] at hInfT'; injection hInfT' with hEqT; subst hEqT
                    have hMovTSl : CodeSliceAt code (basePc + fc.size + 1 + ft.size)
                        #[.mov m1 rt, .jmp (basePc + fc.size + 1 + ft.size + 2 + ff.size + 1)] :=
                      codeSliceAt_pc_eq hSlMovT (by simp [Array.size_append]; omega)
                    obtain ⟨hSlM1, hSlJmp⟩ := codeSliceAt_split (a := #[.mov m1 rt]) (b := #[.jmp _]) hMovTSl
                    obtain ⟨hpcM1, hinsM1⟩ := codeSliceAt_get0 hSlM1
                    obtain ⟨hpcJmp, hinsJmp⟩ := codeSliceAt_get0_at (pc2 := basePc + fc.size + 1 + ft.size + 1) hSlJmp (by simp)
                    have hM1Lt : m1 < regsT.size := by omega
                    have hRtLt : rt < regsT.size := by omega
                    have hRtVal : regsT[rt] = UInt64.ofNat (scalarToNat vt) := by rw [Array.getElem?_eq_getElem hRtLt] at hDstT; injection hDstT
                    let regsEnd := regsT.set m1 regsT[rt] hM1Lt
                    have hEvIf : Evaluates (closeTerm env (.ifBool c tB fB)) vt :=
                      ⟨by simp only [closeTerm, Term.substitute]; exact Equiv.steps_trans (steps_ifCondition _ _ hEvC.1) (.next (.ifTrue _ _) hEvT.1), hEvT.2⟩
                    refine ⟨iOut, vt, uC + 1 + uT + 2, regsEnd, rfl, hJoinCheck, hEvIf, valueInInterval_join_left hIfInf hInT,
                      by omega, (Array.size_set ..).trans (hSzT.trans hSzC), ?_, by simp [regsEnd, Array.getElem?_set_self, hRtVal], ?_⟩
                    · intro reg hr; rw [get_set_ne _ _ _ _ (by omega)]; exact (hPrT reg (by omega)).trans (hPrC reg hr)
                    · intro restFuel
                      have hJzStep : execBytecodeAt code (basePc + fc.size) regsC (1 + (uT + (2 + restFuel))) =
                          execBytecodeAt code (basePc + fc.size + 1) regsC (uT + (2 + restFuel)) := by
                        rw [execBytecodeAt_one_add]; simp [hpcJz, hinsJz, stepByteInstr, hRcLt, hRcVal]
                      have hTailStep : execBytecodeAt code (basePc + fc.size + 1 + ft.size) regsT (2 + restFuel) =
                          execBytecodeAt code (basePc + fc.size + 1 + ft.size + 2 + ff.size + 1) regsEnd restFuel := by
                        rw [show 2 + restFuel = 1 + (1 + restFuel) by omega, execBytecodeAt_one_add]
                        simp only [hpcM1, ↓reduceDIte, hinsM1, stepByteInstr, hM1Lt, hRtLt]
                        rw [execBytecodeAt_one_add]; simp [hpcJmp, hinsJmp, stepByteInstr, regsEnd]
                      calc execBytecodeAt code basePc regs ((uC + 1 + uT + 2) + restFuel)
                        _ = execBytecodeAt code basePc regs (uC + (1 + (uT + (2 + restFuel)))) := by congr 1; omega
                        _ = execBytecodeAt code (basePc + fc.size + 1 + ft.size + 2 + ff.size + 1) regsEnd restFuel := by rw [hExC, hJzStep, hExT, hTailStep]
                        _ = _ := by congr 1; simp [Array.size_append]; omega
                  | false =>
                    obtain ⟨iff', vf, uF, regsF, hInfF', _, hEvF, hInF, huF, hSzF, hPrF, hDstF, hExF⟩ :=
                      compileExprAt_sound code (basePc + fc.size + 1 + ft.size + 2) Γ regMap (m1 + 1) fB ff rf m3 f3 env regsC
                        hSafeF hc3 (codeSliceAt_pc_eq hSlF (by simp [Array.size_append]; omega)) hSimBranch (by omega)
                    rw [hInfF] at hInfF'; injection hInfF' with hEqF; subst hEqF
                    obtain ⟨hpcMF, hinsMF⟩ := codeSliceAt_get0_at (pc2 := basePc + fc.size + 1 + ft.size + 2 + ff.size) hSlMovF (by simp [Array.size_append]; omega)
                    have hM1Lt : m1 < regsF.size := by omega
                    have hRfLt : rf < regsF.size := by omega
                    have hRfVal : regsF[rf] = UInt64.ofNat (scalarToNat vf) := by rw [Array.getElem?_eq_getElem hRfLt] at hDstF; injection hDstF
                    let regsEnd := regsF.set m1 regsF[rf] hM1Lt
                    have hEvIf : Evaluates (closeTerm env (.ifBool c tB fB)) vf :=
                      ⟨by simp only [closeTerm, Term.substitute]; exact Equiv.steps_trans (steps_ifCondition _ _ hEvC.1) (.next (.ifFalse _ _) hEvF.1), hEvF.2⟩
                    refine ⟨iOut, vf, uC + 1 + uF + 1, regsEnd, rfl, hJoinCheck, hEvIf, valueInInterval_join_right hIfInf hInF,
                      by omega, (Array.size_set ..).trans (hSzF.trans hSzC), ?_, by simp [regsEnd, Array.getElem?_set_self, hRfVal], ?_⟩
                    · intro reg hr; rw [get_set_ne _ _ _ _ (by omega)]; exact (hPrF reg (by omega)).trans (hPrC reg hr)
                    · intro restFuel
                      have hJzStep : execBytecodeAt code (basePc + fc.size) regsC (1 + (uF + (1 + restFuel))) =
                          execBytecodeAt code (basePc + fc.size + 1 + ft.size + 2) regsC (uF + (1 + restFuel)) := by
                        rw [execBytecodeAt_one_add]; simp [hpcJz, hinsJz, stepByteInstr, hRcLt, hRcVal]
                      have hTailStep : execBytecodeAt code (basePc + fc.size + 1 + ft.size + 2 + ff.size) regsF (1 + restFuel) =
                          execBytecodeAt code (basePc + fc.size + 1 + ft.size + 2 + ff.size + 1) regsEnd restFuel := by
                        rw [execBytecodeAt_one_add]; simp [hpcMF, hinsMF, stepByteInstr, hM1Lt, hRfLt, regsEnd]
                      calc execBytecodeAt code basePc regs ((uC + 1 + uF + 1) + restFuel)
                        _ = execBytecodeAt code basePc regs (uC + (1 + (uF + (1 + restFuel)))) := by congr 1; omega
                        _ = execBytecodeAt code (basePc + fc.size + 1 + ft.size + 2 + ff.size + 1) regsEnd restFuel := by rw [hExC, hJzStep, hExF, hTailStep]
                        _ = _ := by congr 1; simp [Array.size_append]; omega
  | .ifZero v z s =>
    simp only [checkRangeSafeWith] at hSafe; cases hv : inferRange Γ v <;> simp only [hv] at hSafe
    · simp at hSafe
    · rename_i iv; cases hOut : inferRange Γ (.ifZero v z s) <;> simp only [hOut, Bool.and_eq_true, decide_eq_true_eq] at hSafe
      · simp at hSafe
      · rename_i iOut; obtain ⟨⟨⟨hHiOut, hSafeV⟩, hSafeZ⟩, hSafeS⟩ := hSafe; simp only [compileExprAt] at hComp
        cases hc1 : compileExprAt basePc regMap nextReg v <;> simp only [hc1] at hComp
        · simp at hComp
        · rename_i res1; rcases res1 with ⟨fv, rv, m1, f1⟩
          cases hc2 : compileExprAt (basePc + fv.size + 1 + 2) ((m1 + 1) :: regMap) (m1 + 3) s <;> simp only [hc2] at hComp
          · simp at hComp
          · rename_i res2; rcases res2 with ⟨fs, rs, m2, f2⟩
            cases hc3 : compileExprAt (basePc + fv.size + 1 + 2 + fs.size + 2) regMap (m1 + 3) z <;> simp only [hc3] at hComp
            · simp at hComp
            · rename_i res3; rcases res3 with ⟨fz, rz, m3, f3⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at hComp; rcases hComp with ⟨rfl, rfl, rfl, rfl⟩
              have hb1 := compileExprAt_bounds hc1; have hb2 := compileExprAt_bounds hc2; have hb3 := compileExprAt_bounds hc3
              have hMaxL := Nat.le_max_left m2 m3; have hMaxR := Nat.le_max_right m2 m3
              have hFuelL := Nat.le_max_left (f2 + 2) f3; have hFuelR := Nat.le_max_right (f2 + 2) f3
              have hSimSz := hSim.2.1
              obtain ⟨hSlPre5, hSlMovZ⟩ := codeSliceAt_split hSlice; obtain ⟨hSlPre4, hSlZ⟩ := codeSliceAt_split hSlPre5
              obtain ⟨hSlPre3, hSlMovS⟩ := codeSliceAt_split hSlPre4; obtain ⟨hSlPre2, hSlS⟩ := codeSliceAt_split hSlPre3
              obtain ⟨hSlV, hSlHdr⟩ := codeSliceAt_split hSlPre2
              obtain ⟨iv', vv, uV, regsV, hInfV, hHiV, hEvV, hInV, huV, hSzV, hPrV, hDstV, hExV⟩ :=
                compileExprAt_sound code basePc Γ regMap nextReg v fv rv m1 f1 env regs hSafeV hc1 hSlV hSim (by omega)
              rw [hv] at hInfV; injection hInfV with hEqIv; subst hEqIv
              have hIfInf := hOut; simp only [inferRange, hv] at hIfInf
              cases hzInf : inferRange Γ z <;> simp only [hzInf] at hIfInf
              · simp at hIfInf
              · rename_i iz; cases hSort : (iv.sort == .nat) with
                | false => simp [hSort] at hIfInf
                | true =>
                  simp only [hSort, ↓reduceIte] at hIfInf
                  cases hsInf : inferRange (Interval.pred iv :: Γ) s <;> simp only [hsInf] at hIfInf
                  · simp at hIfInf
                  · rename_i is
                    obtain ⟨kv, rfl, hloV, hhiV⟩ := valNat (beq_iff_eq.mp hSort) hInV
                    have hHdrSplit : CodeSliceAt code (basePc + fv.size)
                        (#[.jz rv (basePc + fv.size + 1 + 2 + fs.size + 2)] ++
                         (#[.loadImm (m1 + 2) 1] ++ #[.binOp .sub (m1 + 1) rv (m1 + 2)])) := hSlHdr
                    obtain ⟨hSlJz, hSlPredOps⟩ := codeSliceAt_split hHdrSplit
                    obtain ⟨hpcJz, hinsJz⟩ := codeSliceAt_get0 hSlJz
                    have hRvLt : rv < regsV.size := by omega
                    have hRvVal : regsV[rv] = UInt64.ofNat kv := by
                      rw [Array.getElem?_eq_getElem hRvLt] at hDstV; injection hDstV
                    cases kv with
                    | zero =>
                      have hSimZ : SimulatesBytecode Γ regMap (m1 + 3) env regsV :=
                        simulatesBytecode_mono_regs hSim (by omega) (by omega) (fun reg hr => hPrV reg hr)
                      obtain ⟨iz', vz, uZ, regsZ, hInfZ', _, hEvZ, hInZ, huZ, hSzZ, hPrZ, hDstZ, hExZ⟩ :=
                        compileExprAt_sound code (basePc + fv.size + 1 + 2 + fs.size + 2) Γ regMap (m1 + 3) z fz rz m3 f3 env regsV
                          hSafeZ hc3 (codeSliceAt_pc_eq hSlZ (by simp [Array.size_append]; omega)) hSimZ (by omega)
                      rw [hzInf] at hInfZ'; injection hInfZ' with hEqZ; subst hEqZ
                      have hMovZSl : CodeSliceAt code (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size) #[.mov m1 rz] :=
                        codeSliceAt_pc_eq hSlMovZ (by simp [Array.size_append]; omega)
                      obtain ⟨hpcMZ, hinsMZ⟩ := codeSliceAt_get0 hMovZSl
                      have hM1Lt : m1 < regsZ.size := by omega
                      have hRzLt : rz < regsZ.size := by omega
                      have hRzVal : regsZ[rz] = UInt64.ofNat (scalarToNat vz) := by
                        rw [Array.getElem?_eq_getElem hRzLt] at hDstZ; injection hDstZ
                      let regsEnd := regsZ.set m1 regsZ[rz] hM1Lt
                      have hEvIZ : Evaluates (closeTerm env (.ifZero v z s)) vz := by
                        refine ⟨?_, hEvZ.2⟩; simp only [closeTerm, Term.substitute]
                        exact Equiv.steps_trans (steps_zeroCondition _ _ hEvV.1) (.next (.zero _ _) hEvZ.1)
                      refine ⟨iOut, vz, uV + 1 + uZ + 1, regsEnd, rfl, hHiOut, hEvIZ,
                        valueInInterval_join_left hIfInf hInZ, by omega,
                        (Array.size_set ..).trans (hSzZ.trans hSzV), ?_, ?_, ?_⟩
                      · intro reg hr
                        rw [get_set_ne _ _ _ _ (by omega)]
                        exact (hPrZ reg (by omega)).trans (hPrV reg hr)
                      · simp [regsEnd, Array.getElem?_set_self, hRzVal]
                      · intro restFuel
                        have hJzStep : execBytecodeAt code (basePc + fv.size) regsV (1 + (uZ + (1 + restFuel))) =
                            execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size + 2) regsV (uZ + (1 + restFuel)) := by
                          rw [execBytecodeAt_one_add]; simp [hpcJz, hinsJz, stepByteInstr, hRvLt, hRvVal]
                        have hTailStep : execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size) regsZ (1 + restFuel) =
                            execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size + 1) regsEnd restFuel := by
                          rw [execBytecodeAt_one_add]; simp [hpcMZ, hinsMZ, stepByteInstr, hM1Lt, hRzLt, regsEnd]
                        calc execBytecodeAt code basePc regs ((uV + 1 + uZ + 1) + restFuel)
                          _ = execBytecodeAt code basePc regs (uV + (1 + (uZ + (1 + restFuel)))) := by congr 1; omega
                          _ = execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size + 1) regsEnd restFuel := by
                              rw [hExV, hJzStep, hExZ, hTailStep]
                          _ = _ := by congr 1; simp [Array.size_append]; omega
                    | succ kp =>
                      obtain ⟨hSlImm, hSlSub⟩ := codeSliceAt_split hSlPredOps
                      obtain ⟨hpcImm, hinsImm⟩ := codeSliceAt_get0_at (pc2 := basePc + fv.size + 1) hSlImm (by simp)
                      obtain ⟨hpcSub, hinsSub⟩ := codeSliceAt_get0_at (pc2 := basePc + fv.size + 1 + 1) hSlSub (by simp)
                      have hKp1Lt : kp + 1 < 2 ^ 64 := by omega
                      have hNz : (UInt64.ofNat (kp + 1) == 0) = false := uint64_beq_zero_false (by omega) hKp1Lt
                      have hSubKp : evalByteBinOp .sub (UInt64.ofNat (kp + 1)) 1 = UInt64.ofNat kp := by
                        apply uint64_eq_of_toNat
                        have hKpLt : kp < 2 ^ 64 := by omega
                        have hLe1 : (1 : UInt64) ≤ UInt64.ofNat (kp + 1) := by
                          rw [UInt64.le_iff_toNat_le, uint64_toNat_of_lt hKp1Lt]; change 1 ≤ kp + 1; omega
                        have h1Nat : (1 : UInt64).toNat = 1 := rfl
                        simp only [evalByteBinOp, UInt64.toNat_sub_of_le _ _ hLe1, uint64_toNat_of_lt hKp1Lt, uint64_toNat_of_lt hKpLt, h1Nat]
                        omega
                      have hR1Lt : m1 + 2 < regsV.size := by omega
                      let regsImm := regsV.set (m1 + 2) 1 hR1Lt
                      have hRPredLt : m1 + 1 < regsImm.size := by simp [regsImm]; omega
                      have hRvLtImm : rv < regsImm.size := by simp [regsImm]; omega
                      have hR1LtImm : m1 + 2 < regsImm.size := by simp [regsImm]; omega
                      have hRvImmVal : regsImm[rv] = UInt64.ofNat (kp + 1) := by
                        have hq : regsImm[rv]? = regsV[rv]? := get_set_ne regsV (m1 + 2) hR1Lt 1 (by omega)
                        rw [Array.getElem?_eq_getElem hRvLtImm, Array.getElem?_eq_getElem hRvLt] at hq
                        injection hq with hq'; exact hq'.trans hRvVal
                      let regsSub := regsImm.set (m1 + 1) (evalByteBinOp .sub regsImm[rv] regsImm[m1 + 2]) hRPredLt
                      have hPredIn : ValueInInterval (Interval.pred iv) (.nat kp) :=
                        ⟨kp, rfl, by simp [Interval.pred]; omega, by simp [Interval.pred]; omega⟩
                      have hSubBase : SimulatesBytecode Γ regMap (m1 + 3) env regsSub := by
                        refine simulatesBytecode_mono_regs hSim (by omega) (by simp [regsSub, regsImm]; omega) ?_
                        intro reg hr
                        simp only [regsSub, regsImm]
                        rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega)]
                        exact hPrV reg hr
                      have hImm2Val : regsImm[m1 + 2] = 1 := by simp [regsImm]
                      have hPredRegVal : regsSub[m1 + 1]? = some (UInt64.ofNat (scalarToNat (.nat kp))) := by
                        simp only [regsSub, Array.getElem?_set_self, hRvImmVal, hImm2Val, hSubKp, scalarToNat]
                      have hSimS : SimulatesBytecode (Interval.pred iv :: Γ) ((m1 + 1) :: regMap) (m1 + 3) (.nat kp :: env) regsSub :=
                        simulatesBytecode_cons hSubBase (by omega) ⟨.refl _, .natural kp⟩ hPredIn hPredRegVal
                      obtain ⟨is', vs, uS, regsS, hInfS', _, hEvS, hInS, huS, hSzS, hPrS, hDstS, hExS⟩ :=
                        compileExprAt_sound code (basePc + fv.size + 1 + 2) (Interval.pred iv :: Γ) ((m1 + 1) :: regMap) (m1 + 3) s fs rs m2 f2 (.nat kp :: env) regsSub
                          hSafeS hc2 (codeSliceAt_pc_eq hSlS (by simp [Array.size_append]; omega)) hSimS (by simp [regsSub, regsImm]; omega)
                      rw [hsInf] at hInfS'; injection hInfS' with hEqS; subst hEqS
                      have hMovSSl : CodeSliceAt code (basePc + fv.size + 1 + 2 + fs.size)
                          #[.mov m1 rs, .jmp (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size + 1)] :=
                        codeSliceAt_pc_eq hSlMovS (by simp [Array.size_append]; omega)
                      obtain ⟨hSlMS1, hSlSJmp⟩ := codeSliceAt_split (a := #[.mov m1 rs]) (b := #[.jmp _]) hMovSSl
                      obtain ⟨hpcMS, hinsMS⟩ := codeSliceAt_get0 hSlMS1
                      obtain ⟨hpcSJ, hinsSJ⟩ := codeSliceAt_get0_at (pc2 := basePc + fv.size + 1 + 2 + fs.size + 1) hSlSJmp (by simp)
                      have hM1Lt : m1 < regsS.size := by simp [regsSub, regsImm] at hSzS; omega
                      have hRsLt : rs < regsS.size := by simp [regsSub, regsImm] at hSzS; omega
                      have hRsVal : regsS[rs] = UInt64.ofNat (scalarToNat vs) := by
                        rw [Array.getElem?_eq_getElem hRsLt] at hDstS; injection hDstS
                      let regsEnd := regsS.set m1 regsS[rs] hM1Lt
                      have hEvIZ : Evaluates (closeTerm env (.ifZero v z s)) vs := by
                        refine ⟨?_, hEvS.2⟩; simp only [closeTerm, Term.substitute]
                        have st : Step
                            (.ifZero (.nat (kp + 1)) (z.substitute (envSubst env)) (s.substitute (liftSubstitution (envSubst env))))
                            (instantiate (s.substitute (liftSubstitution (envSubst env))) (.nat kp)) := .successor kp _ _
                        rw [instantiate_closeTerm_lift] at st
                        exact Equiv.steps_trans (steps_zeroCondition _ _ hEvV.1) (.next st hEvS.1)
                      refine ⟨iOut, vs, uV + 3 + uS + 2, regsEnd, rfl, hHiOut, hEvIZ,
                        valueInInterval_join_right hIfInf hInS, by omega,
                        by simp [regsEnd, hSzS, regsSub, regsImm, hSzV], ?_, ?_, ?_⟩
                      · intro reg hr
                        rw [get_set_ne _ _ _ _ (by omega)]
                        have hp1 := hPrS reg (by omega)
                        simp only [regsSub, regsImm] at hp1
                        rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega)] at hp1
                        exact hp1.trans (hPrV reg hr)
                      · simp [regsEnd, Array.getElem?_set_self, hRsVal]
                      · intro restFuel
                        have hHdrStep : execBytecodeAt code (basePc + fv.size) regsV (3 + (uS + (2 + restFuel))) =
                            execBytecodeAt code (basePc + fv.size + 1 + 2) regsSub (uS + (2 + restFuel)) := by
                          rw [show 3 + (uS + (2 + restFuel)) = 1 + (2 + (uS + (2 + restFuel))) by omega, execBytecodeAt_one_add]
                          simp only [hpcJz, ↓reduceDIte, hinsJz, stepByteInstr, hRvLt, hRvVal, hNz, Bool.false_eq_true, ↓reduceIte]
                          rw [show 2 + (uS + (2 + restFuel)) = 1 + (1 + (uS + (2 + restFuel))) by omega, execBytecodeAt_one_add]
                          simp only [hpcImm, ↓reduceDIte, hinsImm, stepByteInstr, hR1Lt]
                          change execBytecodeAt code (basePc + fv.size + 1 + 1) regsImm (1 + (uS + (2 + restFuel))) = _
                          rw [execBytecodeAt_one_add]
                          simp only [hpcSub, ↓reduceDIte, hinsSub, stepByteInstr, hRPredLt, hRvLtImm, hR1LtImm]
                          rw [show basePc + fv.size + 1 + 1 + 1 = basePc + fv.size + 1 + 2 by omega]
                        have hTailStep : execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size) regsS (2 + restFuel) =
                            execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size + 1) regsEnd restFuel := by
                          rw [show 2 + restFuel = 1 + (1 + restFuel) by omega, execBytecodeAt_one_add]
                          simp only [hpcMS, ↓reduceDIte, hinsMS, stepByteInstr, hM1Lt, hRsLt]
                          rw [execBytecodeAt_one_add]
                          simp [hpcSJ, hinsSJ, stepByteInstr, regsEnd]
                        calc execBytecodeAt code basePc regs ((uV + 3 + uS + 2) + restFuel)
                          _ = execBytecodeAt code basePc regs (uV + (3 + (uS + (2 + restFuel)))) := by congr 1; omega
                          _ = execBytecodeAt code (basePc + fv.size + 1 + 2 + fs.size + 2 + fz.size + 1) regsEnd restFuel := by
                              rw [hExV, hHdrStep, hExS, hTailStep]
                          _ = _ := by congr 1; simp [Array.size_append]; omega

/-- **End-to-End Expression Compiler Soundness (`compileExprToBytecode_sound`)**:
    Whenever `checkRangeSafeBytecode Γ (specializeDictTerm passes t) = true`, `compileExprToBytecode`
    succeeds and `execBytecode` simulates the unspecialized `Core4` source expression `closeTerm env t`
    with certified `< 2^64` arithmetic. -/
theorem compileExprToBytecode_sound
    (passes : Nat) (Γ : List Interval) (regMap : List Nat) (nextReg : Nat) (t : Term)
    (env : List Term) (regs : Array UInt64)
    (hSafe : checkRangeSafeBytecode Γ (specializeDictTerm passes t) = true)
    (hSim : SimulatesBytecode Γ regMap nextReg env regs) :
    ∃ (code : Array ByteInstr) (maxRegs fuelBound : Nat),
      compileExprToBytecode passes regMap nextReg t = some (code, maxRegs, fuelBound) ∧
      (maxRegs ≤ regs.size →
        ∃ (I : Interval) (v : Term),
          inferRange Γ (specializeDictTerm passes t) = some I ∧
          I.hi < 2 ^ 64 ∧
          Evaluates (closeTerm env t) v ∧
          ValueInInterval I v ∧
          scalarToNat v < 2 ^ 64 ∧
          ∀ extraFuel,
            execBytecode code regs (fuelBound + extraFuel) = some (UInt64.ofNat (scalarToNat v))) := by
  have hMap : ∀ (idx : Nat) (I : Interval), Γ[idx]? = some I → ∃ r, regMap[idx]? = some r ∧ r < nextReg := by
    intro idx I hI; obtain ⟨r, _, _, hr, hlt, _⟩ := hSim.2.2 idx I hI; exact ⟨r, hr, hlt⟩
  obtain ⟨frag, dst, maxRegs, fB, hComp⟩ :=
    compileExprAt_complete 0 Γ regMap nextReg (specializeDictTerm passes t) hSafe hMap
  refine ⟨frag ++ #[.ret dst], maxRegs, fB + 1, by simp [compileExprToBytecode, hComp], fun hSz => ?_⟩
  have hSlAll := codeSliceAt_self (frag ++ #[.ret dst])
  obtain ⟨hSlFrag, hSlRet⟩ := codeSliceAt_split hSlAll
  obtain ⟨I, v, used, regs', hInf, hHi, hEvClean, hInI, hUsedLe, hSz', _, hDstVal, hExecFrag⟩ :=
    compileExprAt_sound (frag ++ #[.ret dst]) 0 Γ regMap nextReg (specializeDictTerm passes t)
      frag dst maxRegs fB env regs hSafe hComp hSlFrag hSim hSz
  have hEvOrig : Evaluates (closeTerm env t) v :=
    (specializeDictTerm_evaluates_scalar_iff passes env t v hInI).2 hEvClean
  have hValLt : scalarToNat v < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (valueInInterval_bounds hInI).2 hHi
  have hb := compileExprAt_bounds hComp
  have hDstLt : dst < regs'.size := by omega
  have hDstEq : regs'[dst] = UInt64.ofNat (scalarToNat v) := by
    rw [Array.getElem?_eq_getElem hDstLt] at hDstVal; injection hDstVal
  obtain ⟨hpcRet, hinsRet⟩ := codeSliceAt_get0 hSlRet
  refine ⟨I, v, hInf, hHi, hEvOrig, hInI, hValLt, fun extraFuel => ?_⟩
  have hRemPos : ∃ rem, fB + 1 + extraFuel = used + (rem + 1) := ⟨fB - used + extraFuel, by omega⟩
  obtain ⟨rem, hFuelEq⟩ := hRemPos
  rw [execBytecode_eq, hFuelEq, hExecFrag (rem + 1), execBytecodeAt]
  simp [hpcRet, hinsRet, stepByteInstr, hDstLt, hDstEq]

/-! ## 4. Loop Dictionary Erasure (`specializeAndCompileLoop`), `sumTo 30000`, & C99 Emitter -/

/-- Multi-iteration source semantics of a countdown accumulator loop (`i = n, n-1, ..., 1`)
    where each iteration evaluates the open `Core4` expression `stepTerm` under `[acc, i]`. -/
inductive EvaluatesCountdownLoop (stepTerm : Term) : Nat → Nat → Nat → Prop where
  | done (acc : Nat) : EvaluatesCountdownLoop stepTerm 0 acc acc
  | step {k acc acc' finalAcc : Nat} :
      Evaluates (closeTerm [.nat acc, .nat (k + 1)] stepTerm) (.nat acc') →
      EvaluatesCountdownLoop stepTerm k acc' finalAcc →
      EvaluatesCountdownLoop stepTerm (k + 1) acc finalAcc

/-- Countdown run witness certifying that intermediate pre-step accumulators stay `≤ maxAcc`. -/
inductive CountdownBounded (maxAcc : Nat) (stepTerm : Term) : Nat → Nat → Nat → Prop where
  | done {acc : Nat} : CountdownBounded maxAcc stepTerm 0 acc acc
  | step {k acc acc' finalAcc : Nat} :
      acc ≤ maxAcc →
      Evaluates (closeTerm [.nat acc, .nat (k + 1)] stepTerm) (.nat acc') →
      CountdownBounded maxAcc stepTerm k acc' finalAcc →
      CountdownBounded maxAcc stepTerm (k + 1) acc finalAcc

theorem countdownBounded_evaluates {maxAcc : Nat} {stepTerm : Term} {n acc finalAcc : Nat}
    (h : CountdownBounded maxAcc stepTerm n acc finalAcc) :
    EvaluatesCountdownLoop stepTerm n acc finalAcc := by
  induction h with
  | done => exact .done _
  | step _ hev _ ih => exact .step hev ih

/-- Strip dictionary-passing overhead from `stepTerm` and compile the countdown loop over
    `r0 = acc`, `r1 = counter`, `r2 = 1` with `< 2^64` range safety over `[0..maxAcc] × [1..maxN]`. -/
def specializeAndCompileLoop (passes : Nat) (maxN maxAcc : Nat) (stepTerm : Term) :
    Option (Array ByteInstr × Nat × Nat) :=
  if hPos : 1 ≤ maxN then
    if decide (maxN < 2 ^ 64 ∧ maxAcc < 2 ^ 64) then
      let cleanStep := specializeDictTerm passes stepTerm
      let Γ := [Interval.mkNat 0 maxAcc (Nat.zero_le _), Interval.mkNat 1 maxN hPos]
      if checkRangeSafeBytecode Γ cleanStep then
        match inferRange Γ cleanStep with
        | some iOut =>
          if iOut.sort == .nat then
            match compileExprAt 1 [0, 1] 3 cleanStep with
            | some (stepFrag, rStepDst, maxRegStep, stepFuel) =>
              let exitPc := 1 + stepFrag.size + 4
              let code := #[.jz 1 exitPc] ++ stepFrag ++
                          #[.mov 0 rStepDst, .loadImm 2 1, .binOp .sub 1 1 2, .jmp 0, .ret 0]
              some (code, max 3 maxRegStep, stepFuel + 5)
            | none => none
          else none
        | none => none
      else none
    else none
  else none

/-- **Soundness of `specializeAndCompileLoop` (`specializeAndCompileLoop_sound`)**:
    Every specialized loop bytecode executes `n ≤ maxN` countdown iterations in lockstep with the
    unspecialized dictionary-passing `Core4` `stepTerm` and returns `UInt64.ofNat finalAcc`. -/
theorem specializeAndCompileLoop_sound
    (passes maxN maxAcc : Nat) (stepTerm : Term)
    (code : Array ByteInstr) (maxRegs iterFuel : Nat)
    (hLoop : specializeAndCompileLoop passes maxN maxAcc stepTerm = some (code, maxRegs, iterFuel))
    {n acc0 finalAcc : Nat} (hn : n ≤ maxN) (hAcclt : finalAcc < 2 ^ 64)
    (hRun : CountdownBounded maxAcc stepTerm n acc0 finalAcc) :
    EvaluatesCountdownLoop stepTerm n acc0 finalAcc ∧
    (UInt64.ofNat finalAcc).toNat = finalAcc ∧
    ∀ (regs : Array UInt64) (extraFuel : Nat),
      maxRegs ≤ regs.size →
      regs[0]? = some (UInt64.ofNat acc0) →
      regs[1]? = some (UInt64.ofNat n) →
      execBytecode code regs (n * iterFuel + 2 + extraFuel) = some (UInt64.ofNat finalAcc) := by
  refine ⟨countdownBounded_evaluates hRun, uint64_toNat_of_lt hAcclt, ?_⟩
  unfold specializeAndCompileLoop at hLoop
  split at hLoop
  case isFalse => simp at hLoop
  case isTrue hPos =>
    split at hLoop
    case isFalse => simp at hLoop
    case isTrue hBnd =>
      obtain ⟨hMaxNLt, _⟩ := of_decide_eq_true hBnd
      dsimp only at hLoop
      let cleanStep := specializeDictTerm passes stepTerm
      let Γ := [Interval.mkNat 0 maxAcc (Nat.zero_le _), Interval.mkNat 1 maxN hPos]
      split at hLoop
      case isFalse => simp at hLoop
      case isTrue hSafe =>
        cases hInf : inferRange Γ cleanStep with
        | none => simp [Γ, cleanStep, hInf] at hLoop
        | some iOut =>
          simp only [Γ, cleanStep, hInf] at hLoop
          split at hLoop
          case isFalse => simp at hLoop
          case isTrue hSort =>
            cases hComp : compileExprAt 1 [0, 1] 3 cleanStep with
            | none => simp [cleanStep, hComp] at hLoop
            | some resStep =>
              rcases resStep with ⟨stepFrag, rDst, maxRegStep, stepFuel⟩
              simp only [cleanStep, hComp, Option.some.injEq, Prod.mk.injEq] at hLoop
              rcases hLoop with ⟨rfl, rfl, rfl⟩
              have hbStep := compileExprAt_bounds hComp
              have hMax3L := Nat.le_max_left 3 maxRegStep
              have hMax3R := Nat.le_max_right 3 maxRegStep
              let exitPc := 1 + stepFrag.size + 4
              let fullCode := #[ByteInstr.jz 1 exitPc] ++ stepFrag ++
                              #[.mov 0 rDst, .loadImm 2 1, .binOp .sub 1 1 2, .jmp 0, .ret 0]
              have hSplitTail : fullCode = (#[.jz 1 exitPc] ++ stepFrag) ++
                  (#[.mov 0 rDst] ++ (#[.loadImm 2 1] ++ (#[.binOp .sub 1 1 2] ++ (#[.jmp 0] ++ #[.ret 0])))) := by
                simp [fullCode, Array.append_assoc]
              have hSlAll := codeSliceAt_frag_eq (codeSliceAt_self fullCode) hSplitTail
              obtain ⟨hSlHead, hSlEpilogue⟩ := codeSliceAt_split hSlAll
              obtain ⟨hSlJz0, hSlBody⟩ := codeSliceAt_split hSlHead
              obtain ⟨hSlMov0, hSlEp1⟩ := codeSliceAt_split hSlEpilogue
              obtain ⟨hSlImm2, hSlEp2⟩ := codeSliceAt_split hSlEp1
              obtain ⟨hSlSub1, hSlEp3⟩ := codeSliceAt_split hSlEp2
              obtain ⟨hSlJmp0, hSlRet0⟩ := codeSliceAt_split hSlEp3
              obtain ⟨hpcJz0, hinsJz0⟩ := codeSliceAt_get0 hSlJz0
              obtain ⟨hpcMov0, hinsMov0⟩ := codeSliceAt_get0_at (pc2 := 1 + stepFrag.size) hSlMov0 (by simp [Array.size_append])
              obtain ⟨hpcImm2, hinsImm2⟩ := codeSliceAt_get0_at (pc2 := 1 + stepFrag.size + 1) hSlImm2 (by simp [Array.size_append])
              obtain ⟨hpcSub1, hinsSub1⟩ := codeSliceAt_get0_at (pc2 := 1 + stepFrag.size + 1 + 1) hSlSub1 (by simp [Array.size_append])
              obtain ⟨hpcJmp0, hinsJmp0⟩ := codeSliceAt_get0_at (pc2 := 1 + stepFrag.size + 1 + 1 + 1) hSlJmp0 (by simp [Array.size_append])
              obtain ⟨hpcRet0, hinsRet0⟩ := codeSliceAt_get0_at (pc2 := exitPc) hSlRet0 (by simp [exitPc, Array.size_append])
              have hSlBody1 : CodeSliceAt fullCode 1 stepFrag := codeSliceAt_pc_eq hSlBody (by simp)
              clear hAcclt; revert hn
              induction hRun with
              | @done accCurr =>
                intro _ regs extraFuel hSz hr0 hr1
                have h0Lt : 0 < regs.size := by omega
                have h1Lt : 1 < regs.size := by omega
                have hr0Eq : regs[0] = UInt64.ofNat accCurr := by rw [Array.getElem?_eq_getElem h0Lt] at hr0; injection hr0
                have hr1Eq : regs[1] = 0 := by rw [Array.getElem?_eq_getElem h1Lt] at hr1; injection hr1
                change execBytecode fullCode regs (0 * (stepFuel + 5) + 2 + extraFuel) = _
                rw [execBytecode_eq, show 0 * (stepFuel + 5) + 2 + extraFuel = 1 + (1 + extraFuel) by omega, execBytecodeAt_one_add]
                simp only [hpcJz0, ↓reduceDIte, hinsJz0, stepByteInstr, h1Lt, hr1Eq, beq_self_eq_true, ↓reduceIte]
                rw [execBytecodeAt_one_add]; simp [hpcRet0, hinsRet0, stepByteInstr, h0Lt, hr0Eq]
              | @step k accCurr accNext finalAcc' hAccLe hEvOrigStep _ ih =>
                intro hn regs extraFuel hSz hr0 hr1
                have hkLe : k ≤ maxN := by omega
                have hSimIter : SimulatesBytecode Γ [0, 1] 3 [.nat accCurr, .nat (k + 1)] regs := by
                  refine ⟨⟨by simp [Γ], fun (idx : Nat) (J : Interval) hJ => ?_⟩, by omega, fun (idx : Nat) (J : Interval) hJ => ?_⟩
                  · cases idx with
                    | zero =>
                      simp only [Γ, List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ
                      exact ⟨.nat accCurr, .nat accCurr, rfl, ⟨.refl _, .natural _⟩, accCurr, rfl, Nat.zero_le _, hAccLe⟩
                    | succ m =>
                      cases m with
                      | zero =>
                        simp only [Γ, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ
                        exact ⟨.nat (k + 1), .nat (k + 1), rfl, ⟨.refl _, .natural _⟩, k + 1, rfl, by simp [Interval.mkNat], hn⟩
                      | succ _k2 => simp [Γ] at hJ
                  · cases idx with
                    | zero =>
                      simp only [Γ, List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ
                      exact ⟨0, .nat accCurr, .nat accCurr, rfl, by decide, rfl, ⟨.refl _, .natural _⟩,
                        ⟨accCurr, rfl, Nat.zero_le _, hAccLe⟩, hr0⟩
                    | succ m =>
                      cases m with
                      | zero =>
                        simp only [Γ, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ
                        exact ⟨1, .nat (k + 1), .nat (k + 1), rfl, by decide, rfl, ⟨.refl _, .natural _⟩,
                          ⟨k + 1, rfl, by simp [Interval.mkNat], hn⟩, hr1⟩
                      | succ _k2 => simp [Γ] at hJ
                obtain ⟨iOut', vStep, usedS, regsS, hInf', _, hEvClean, hInOut, hUsedLe, hSzS, hPrS, hDstS, hExS⟩ :=
                  compileExprAt_sound fullCode 1 Γ [0, 1] 3 cleanStep stepFrag rDst maxRegStep stepFuel
                    [.nat accCurr, .nat (k + 1)] regs hSafe hComp hSlBody1 hSimIter (by omega)
                rw [hInf] at hInf'; injection hInf' with hEqOut; subst hEqOut
                have hEvOrig' := (specializeDictTerm_evaluates_scalar_iff passes [.nat accCurr, .nat (k + 1)] stepTerm vStep hInOut).2 hEvClean
                have hvEq : vStep = .nat accNext := evaluates_deterministic hEvOrig' hEvOrigStep
                subst hvEq
                have h1Lt : 1 < regs.size := by omega
                have hr1Val : regs[1] = UInt64.ofNat (k + 1) := by
                  rw [Array.getElem?_eq_getElem h1Lt] at hr1; injection hr1
                have hk1Lt : k + 1 < 2 ^ 64 := by omega
                have hkLt : k < 2 ^ 64 := by omega
                have hNz1 : (UInt64.ofNat (k + 1) == 0) = false := uint64_beq_zero_false (by omega) hk1Lt
                have hSubK : evalByteBinOp .sub (UInt64.ofNat (k + 1)) 1 = UInt64.ofNat k := by
                  apply uint64_eq_of_toNat
                  have hLe1 : (1 : UInt64) ≤ UInt64.ofNat (k + 1) := by
                    rw [UInt64.le_iff_toNat_le, uint64_toNat_of_lt hk1Lt]; change 1 ≤ k + 1; omega
                  have h1Nat : (1 : UInt64).toNat = 1 := rfl
                  simp only [evalByteBinOp, UInt64.toNat_sub_of_le _ _ hLe1, uint64_toNat_of_lt hk1Lt, uint64_toNat_of_lt hkLt, h1Nat]
                  omega
                have h0LtS : 0 < regsS.size := by omega
                have hrDstLtS : rDst < regsS.size := by omega
                have hrDstVal : regsS[rDst] = UInt64.ofNat accNext := by
                  rw [Array.getElem?_eq_getElem hrDstLtS] at hDstS; injection hDstS
                let regsE1 := regsS.set 0 regsS[rDst] h0LtS
                have h2LtE1 : 2 < regsE1.size := by simp [regsE1]; omega
                let regsE2 := regsE1.set 2 1 h2LtE1
                have h1LtE2 : 1 < regsE2.size := by simp [regsE2, regsE1]; omega
                have h2LtE2 : 2 < regsE2.size := by simp [regsE2, regsE1]; omega
                have hr1E2 : regsE2[1]? = some (UInt64.ofNat (k + 1)) := by
                  simp only [regsE2, regsE1]
                  rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide)]
                  exact (hPrS 1 (by decide)).trans hr1
                have hr1E2Val : regsE2[1] = UInt64.ofNat (k + 1) := by
                  rw [Array.getElem?_eq_getElem h1LtE2] at hr1E2; injection hr1E2
                have hr2E2Val : regsE2[2] = 1 := by simp [regsE2]
                let regsNext := regsE2.set 1 (evalByteBinOp .sub regsE2[1] regsE2[2]) h1LtE2
                have hNext0 : regsNext[0]? = some (UInt64.ofNat accNext) := by
                  simp only [regsNext, regsE2, regsE1]
                  rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide)]
                  simp [Array.getElem?_set_self, hrDstVal]
                have hNext1 : regsNext[1]? = some (UInt64.ofNat k) := by
                  simp only [regsNext, Array.getElem?_set_self, hr1E2Val, hr2E2Val, hSubK]
                let remExtra := (stepFuel - usedS) + extraFuel
                let remFuel := k * (stepFuel + 5) + 2 + remExtra
                have hIH := ih hkLe regsNext remExtra (by simp [regsNext, regsE2, regsE1, hSzS]; omega) hNext0 hNext1
                rw [execBytecode_eq] at hIH ⊢
                have hJzStep : execBytecodeAt fullCode 0 regs (1 + (usedS + (4 + remFuel))) =
                    execBytecodeAt fullCode 1 regs (usedS + (4 + remFuel)) := by
                  rw [execBytecodeAt_one_add]
                  simp only [hpcJz0, ↓reduceDIte, hinsJz0, stepByteInstr, h1Lt, hr1Val, hNz1, Bool.false_eq_true, ↓reduceIte]
                have hEpStep : execBytecodeAt fullCode (1 + stepFrag.size) regsS (4 + remFuel) =
                    execBytecodeAt fullCode 0 regsNext remFuel := by
                  rw [show 4 + remFuel = 1 + (3 + remFuel) by omega, execBytecodeAt_one_add]
                  simp only [hpcMov0, ↓reduceDIte, hinsMov0, stepByteInstr, h0LtS, hrDstLtS]
                  change execBytecodeAt fullCode (1 + stepFrag.size + 1) regsE1 (3 + remFuel) = _
                  rw [show 3 + remFuel = 1 + (2 + remFuel) by omega, execBytecodeAt_one_add]
                  simp only [hpcImm2, ↓reduceDIte, hinsImm2, stepByteInstr, h2LtE1]
                  change execBytecodeAt fullCode (1 + stepFrag.size + 1 + 1) regsE2 (2 + remFuel) = _
                  rw [show 2 + remFuel = 1 + (1 + remFuel) by omega, execBytecodeAt_one_add]
                  simp only [hpcSub1, ↓reduceDIte, hinsSub1, stepByteInstr, h1LtE2, h2LtE2]
                  change execBytecodeAt fullCode (1 + stepFrag.size + 1 + 1 + 1) regsNext (1 + remFuel) = _
                  rw [execBytecodeAt_one_add]; simp [hpcJmp0, hinsJmp0, stepByteInstr]
                calc execBytecodeAt fullCode 0 regs ((k + 1) * (stepFuel + 5) + 2 + extraFuel)
                  _ = execBytecodeAt fullCode 0 regs (1 + (usedS + (4 + remFuel))) := by
                      congr 1; dsimp [remFuel, remExtra]; rw [Nat.succ_mul k (stepFuel + 5)]; omega
                  _ = execBytecodeAt fullCode 0 regsNext remFuel := by
                      rw [hJzStep, hExS (4 + remFuel), hEpStep]
                  _ = some (UInt64.ofNat finalAcc') := hIH

/-! ### `HAdd.hAdd` Dictionary-Passing Benchmark (`sumTo 30000 = 450,015,000`) & C99 Emitter -/

/-- `Core4` `Add.add` projection combinator `λα. λinstAdd. instAdd.add`. -/
def coreAddProj : Term := .lam (.lam (.get (.bound 0) "add"))

/-- `Core4` `Add Nat` instance record `{ add = λa. λb. a + b }`. -/
def coreInstAddNat : Term :=
  .record [("add", .lam (.lam (.binary .add (.bound 1) (.bound 0))))]

/-- `Core4` `instHAdd` builder wrapping `Add.add` inside `{ hAdd = λa. λb. Add.add {} inst a b }`. -/
def coreInstHAddNat : Term :=
  .app (.app
    (.lam (.lam (.record [("hAdd",
      .lam (.lam (.app (.app (.app (.app coreAddProj (.record [])) (.bound 2)) (.bound 1)) (.bound 0))))])))
    (.record []))
    coreInstAddNat

/-- `Core4` 4-argument `HAdd.hAdd` projection (`review/EXPERT-compiler-runtime-20261103.md` §2.3). -/
def coreHAddProj : Term := .lam (.lam (.lam (.lam (.get (.bound 0) "hAdd"))))

/-- Unspecialized `Core4` dictionary-passing application `HAdd.hAdd {} {} {} instHAddNat lhs rhs`. -/
def hAddDictApp (lhs rhs : Term) : Term :=
  .app (.app (.app (.app (.app (.app coreHAddProj (.record [])) (.record [])) (.record []))
    coreInstHAddNat) lhs) rhs

/-- Open loop body `HAdd.hAdd {} {} {} instHAddNat acc i` (`bound 0 = acc`, `bound 1 = i`). -/
def sumToDictStep : Term := hAddDictApp (.bound 0) (.bound 1)

theorem sumToDictStep_specializes :
    specializeDictTerm 4 sumToDictStep = .binary .add (.bound 0) (.bound 1) := by
  simp [specializeDictTerm, sumToDictStep, hAddDictApp, coreHAddProj, coreInstHAddNat,
    coreAddProj, coreInstAddNat, dataPinSteps, dataPinPass, resolveApp, resolveGet,
    resolveBinary, primitiveResult, instantiate, Term.substitute, single, liftSubstitution,
    Term.rename, liftRename]

theorem sumToDictStep_evaluates (acc m : Nat) :
    Evaluates (closeTerm [.nat acc, .nat m] sumToDictStep) (.nat (acc + m)) := by
  have hClean : Evaluates (closeTerm [.nat acc, .nat m] (specializeDictTerm 4 sumToDictStep)) (.nat (acc + m)) := by
    rw [sumToDictStep_specializes]
    refine ⟨?_, .natural (acc + m)⟩
    simp only [closeTerm, Term.substitute, envSubst]
    exact .next (.primitive .add (.nat acc) (.nat m) (.nat (acc + m)) (.natural acc) (.natural m) rfl) (.refl _)
  exact (specializeDictTerm_evaluates_scalar_iff 4 [.nat acc, .nat m] sumToDictStep (.nat (acc + m))
    (I := Interval.mkNat (acc + m) (acc + m) (Nat.le_refl _))
    ⟨acc + m, rfl, Nat.le_refl _, Nat.le_refl _⟩).2 hClean

/-- Reference countdown sum specification `acc + ∑_{j=1}^k j`. -/
def sumCountdownSpec : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => sumCountdownSpec k (acc + (k + 1))

theorem sumCountdownSpec_add (k a b : Nat) :
    sumCountdownSpec k (a + b) = a + sumCountdownSpec k b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simpa [sumCountdownSpec, Nat.add_assoc] using ih (b + (k + 1))

theorem sumCountdownSpec_twice (n : Nat) :
    2 * sumCountdownSpec n 0 = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hEq : sumCountdownSpec (k + 1) 0 = (k + 1) + sumCountdownSpec k 0 := by
      simpa [sumCountdownSpec] using sumCountdownSpec_add k (k + 1) 0
    have hMul : (k + 1) * (k + 1 + 1) = (k + 1) * k + (k + 1) * 2 := Nat.mul_add (k + 1) k 2
    have hComm : (k + 1) * k = k * (k + 1) := Nat.mul_comm (k + 1) k
    rw [hEq, Nat.mul_add, ih, hMul, hComm]; omega

theorem sumTo_countdownBounded {maxAcc k acc : Nat} (hBound : sumCountdownSpec k acc ≤ maxAcc) :
    CountdownBounded maxAcc sumToDictStep k acc (sumCountdownSpec k acc) := by
  induction k generalizing acc with
  | zero => exact .done
  | succ k ih =>
    simp only [sumCountdownSpec] at hBound ⊢
    have hGe : acc + (k + 1) ≤ sumCountdownSpec k (acc + (k + 1)) := by
      simpa using (show acc + (k + 1) + 0 ≤ acc + (k + 1) + sumCountdownSpec k 0 from
        Nat.add_le_add_left (Nat.zero_le _) _) |> fun h => by
          rwa [Nat.add_zero, ← sumCountdownSpec_add k (acc + (k + 1)) 0] at h
    exact .step (by omega) (sumToDictStep_evaluates acc (k + 1)) (ih hBound)

/-- Compiled bytecode loop for `sumTo` up to `n = 30000` (`maxAcc = 450015000`). -/
def sumToCompiledLoop : Option (Array ByteInstr × Nat × Nat) :=
  specializeAndCompileLoop 4 30000 450015000 sumToDictStep

/-- Tight 7-instruction register-bytecode loop emitted by `sumToCompiledLoop`. -/
@[expose] def sumToLoopCode : Array ByteInstr :=
  #[.jz 1 6, .binOp .add 3 0 1, .mov 0 3, .loadImm 2 1, .binOp .sub 1 1 2, .jmp 0, .ret 0]

theorem sumToCompiledLoop_eq : sumToCompiledLoop = some (sumToLoopCode, 4, 6) := by
  unfold sumToCompiledLoop specializeAndCompileLoop; dsimp only; rw [sumToDictStep_specializes]; decide

theorem checkRangeSafeBytecode_inhabited : ∃ t : Term, checkRangeSafeBytecode [] t = true :=
  ⟨.binary .add (.nat 20) (.nat 22), by decide⟩

theorem specializeAndCompileLoop_inhabited :
    ∃ code maxRegs iterFuel, specializeAndCompileLoop 4 30000 450015000 sumToDictStep = some (code, maxRegs, iterFuel) :=
  ⟨sumToLoopCode, 4, 6, sumToCompiledLoop_eq⟩

/-- Execute the specialized `sumTo` register-bytecode loop on `n`. -/
def runSumToBytecode (n : Nat) : Option UInt64 :=
  match sumToCompiledLoop with
  | some (code, maxRegs, iterFuel) =>
    let regs := (#[0, UInt64.ofNat n] ++ Array.replicate maxRegs 0)
    execBytecode code regs (n * iterFuel + 2)
  | none => none

theorem runSumToBytecode_sound (n : Nat) (hn : n ≤ 30000) :
    EvaluatesCountdownLoop sumToDictStep n 0 (sumCountdownSpec n 0) ∧
    runSumToBytecode n = some (UInt64.ofNat (sumCountdownSpec n 0)) := by
  have hLoop := sumToCompiledLoop_eq
  have hProd : n * (n + 1) ≤ 30000 * 30001 := Nat.mul_le_mul hn (by omega)
  have hTwice := sumCountdownSpec_twice n
  have hBound : sumCountdownSpec n 0 ≤ 450015000 := by omega
  have hRun := sumTo_countdownBounded hBound
  obtain ⟨hEvLoop, _, hExec⟩ :=
    specializeAndCompileLoop_sound 4 30000 450015000 sumToDictStep sumToLoopCode 4 6
      hLoop hn (by omega) hRun
  refine ⟨hEvLoop, ?_⟩
  simp only [runSumToBytecode, hLoop]
  simpa using hExec (#[0, UInt64.ofNat n] ++ Array.replicate 4 0) 0
    (by simp [Array.size_append])
    (by simp [Array.getElem?_append])
    (by simp [Array.getElem?_append])

theorem runSumToBytecode_30000 :
    EvaluatesCountdownLoop sumToDictStep 30000 0 450015000 ∧
    runSumToBytecode 30000 = some 450015000 := by
  have hSpec : sumCountdownSpec 30000 0 = 450015000 := by
    have := sumCountdownSpec_twice 30000; omega
  simpa [hSpec] using runSumToBytecode_sound 30000 (Nat.le_refl 30000)

#guard execBytecode sumToLoopCode #[0, 30000, 0, 0, 0, 0] 180002 == some 450015000

private def renderC99BinOp (op : ByteBinOp) (lhs rhs : String) : String :=
  match op with
  | .add => s!"({lhs} + {rhs})" | .sub => s!"({lhs} - {rhs})" | .mul => s!"({lhs} * {rhs})"
  | .div => s!"(({rhs} == 0ULL) ? 0ULL : ({lhs} / {rhs}))" | .mod => s!"(({rhs} == 0ULL) ? {lhs} : ({lhs} % {rhs}))"
  | .eq => s!"(({lhs} == {rhs}) ? 1ULL : 0ULL)" | .lt => s!"(({lhs} < {rhs}) ? 1ULL : 0ULL)" | .le => s!"(({lhs} <= {rhs}) ? 1ULL : 0ULL)"
  | .conj => s!"((({lhs} != 0ULL) && ({rhs} != 0ULL)) ? 1ULL : 0ULL)"
  | .bitAnd => s!"({lhs} & {rhs})" | .bitOr => s!"({lhs} | {rhs})" | .bitXor => s!"({lhs} ^ {rhs})"

private def renderC99Instr (nInstrs pc : Nat) (ins : ByteInstr) : String :=
  let fail := "{ if (ok != NULL) *ok = 0; return 0ULL; }"
  let fuelChk := s!"  if (fuel == 0ULL) {fail} fuel--;\n"
  let body := match ins with
    | .loadImm dst imm =>
      s!"  if ({dst}ULL >= n_regs) {fail}\n  regs[{dst}] = {imm.toNat}ULL;\n"
    | .mov dst src =>
      s!"  if ({dst}ULL >= n_regs || {src}ULL >= n_regs) {fail}\n  regs[{dst}] = regs[{src}];\n"
    | .binOp op dst lhs rhs =>
      let expr := renderC99BinOp op s!"regs[{lhs}]" s!"regs[{rhs}]"
      s!"  if ({dst}ULL >= n_regs || {lhs}ULL >= n_regs || {rhs}ULL >= n_regs) {fail}\n  regs[{dst}] = {expr};\n"
    | .jz cond target =>
      let tgt := if target < nInstrs then s!"L{target}" else "L_oob"
      s!"  if ({cond}ULL >= n_regs) {fail}\n  if (regs[{cond}] == 0ULL) goto {tgt};\n"
    | .jmp target => s!"  goto {if target < nInstrs then s!"L{target}" else "L_oob"};\n"
    | .ret src =>
      s!"  if ({src}ULL >= n_regs) {fail}\n  if (ok != NULL) *ok = 1;\n  return regs[{src}];\n"
  s!"L{pc}:\n" ++ fuelChk ++ body

/-- Emit standalone NULL-safe & bounds-checked C99 executing `code` with exact `execBytecode` semantics. -/
def emitRegisterBytecodeC99 (code : Array ByteInstr) : String :=
  let hdr :=
    "#include <stdint.h>\n#include <stddef.h>\n\n" ++
    "uint64_t obend_bytecode_jit_run(uint64_t *regs, size_t n_regs, uint64_t fuel, int *ok) {\n" ++
    "  if (regs == NULL && n_regs > 0U) { if (ok != NULL) *ok = 0; return 0ULL; }\n"
  let blocks := Id.run do
    let mut acc := ""
    for h : i in [0:code.size] do acc := acc ++ renderC99Instr code.size i code[i]
    return acc
  hdr ++ blocks ++ "L_oob:\n  if (ok != NULL) *ok = 0;\n  return 0ULL;\n}\n"

end Obend.Leaf.BytecodeRegisterJit
end
