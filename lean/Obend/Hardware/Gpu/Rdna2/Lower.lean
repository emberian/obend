/-
# Obend.Hardware.Gpu.Rdna2.Lower — a kernel's specification as 32-bit terms

`kernelValue` (`Obend.Hardware.Gpu`) computes in 64-bit words; the device computes in 32-bit registers.
`pKernel` writes a kernel's value at an element as a pair of 32-bit terms (low dword, high dword), built
with the same smart constructors the symbolic run uses and the limb formulas a compiler uses: an add is
an add and an add-with-carry, a multiply the three limb products (`mul_limbs`, proved by arithmetic on
the products as atoms rather than handed to a SAT solver), a shift by a known amount its 32-bit pieces.
`pKernel_sound` says the pair evaluates to `kernelValue` for every memory: it is the specification side
of the comparison `Equiv` makes.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Term
public import Obend.Hardware.Gpu
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph

/-! ## 1. 64-bit identities on 32-bit halves -/

theorem join64_add (lo hi : UInt32) : join64 lo hi = lo.toUInt64 + (hi.toUInt64 <<< 32) := by
  unfold join64; bv_decide

theorem join64_toNat (lo hi : UInt32) : (join64 lo hi).toNat = lo.toNat + 2 ^ 32 * hi.toNat := by
  have h1 := lo.toNat_lt; have h2 := hi.toNat_lt
  rw [join64_add, UInt64.toNat_add, UInt64.toNat_shiftLeft]
  simp only [UInt32.toNat_toUInt64]
  have : (32 : UInt64).toNat % 64 = 32 := by decide
  rw [this, Nat.shiftLeft_eq]
  omega

theorem mul_limbs (a0 a1 b0 b1 : UInt32) :
    join64 (a0 * b0) (mulHiBV a0 b0 + a1 * b0 + a0 * b1) = join64 a0 a1 * join64 b0 b1 := by
  apply UInt64.toNat.inj
  rw [join64_toNat, UInt64.toNat_mul, join64_toNat, join64_toNat]
  simp only [UInt32.toNat_add, UInt32.toNat_mul, mulHiBV, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have ha0 := a0.toNat_lt; have hb0 := b0.toNat_lt
  have hp : a0.toNat * b0.toNat < 2 ^ 64 := by have := Nat.mul_lt_mul'' ha0 hb0; simpa using this
  have h32 : (32 : UInt64).toNat % 64 = 32 := by decide
  simp only [h32, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hp]
  have e : (a0.toNat + 2 ^ 32 * a1.toNat) * (b0.toNat + 2 ^ 32 * b1.toNat) =
      a0.toNat * b0.toNat + 2 ^ 32 * (a1.toNat * b0.toNat + a0.toNat * b1.toNat) + 2 ^ 64 * (a1.toNat * b1.toNat) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm a0.toNat (2 ^ 32) b1.toNat,
      Nat.mul_assoc (2 ^ 32) a1.toNat b0.toNat, Nat.mul_assoc (2 ^ 32) a1.toNat (2 ^ 32 * b1.toNat),
      Nat.mul_left_comm a1.toNat (2 ^ 32) b1.toNat, ← Nat.mul_assoc (2 ^ 32) (2 ^ 32)]
    omega
  rw [e]
  generalize a0.toNat * b0.toNat = P at *
  generalize a1.toNat * b0.toNat = Q
  generalize a0.toNat * b1.toNat = R
  generalize a1.toNat * b1.toNat = S
  omega

theorem add_limbs (a0 a1 b0 b1 : UInt32) :
    join64 (a0 + b0) (a1 + b1 + (if carryBV a0 b0 then 1 else 0)) = join64 a0 a1 + join64 b0 b1 := by
  unfold join64 carryBV; bv_decide

theorem sub_limbs (a0 a1 b0 b1 : UInt32) :
    join64 (a0 - b0) (a1 - b1 - (if borrowBV a0 b0 then 1 else 0)) = join64 a0 a1 - join64 b0 b1 := by
  unfold join64 borrowBV; bv_decide

theorem w2b_b2w (b : Bool) : w2b (b2w b) = b := by cases b <;> rfl

theorem and_limbs (a0 a1 b0 b1 : UInt32) : join64 (a0 &&& b0) (a1 &&& b1) = join64 a0 a1 &&& join64 b0 b1 := by
  unfold join64; bv_decide

theorem or_limbs (a0 a1 b0 b1 : UInt32) : join64 (a0 ||| b0) (a1 ||| b1) = join64 a0 a1 ||| join64 b0 b1 := by
  unfold join64; bv_decide

theorem ult_limbs (a0 a1 b0 b1 : UInt32) :
    (join64 (if decide (join64 a0 a1 < join64 b0 b1) = true then 1 else 0) 0).toBitVec =
      if (join64 a0 a1).toBitVec.ult (join64 b0 b1).toBitVec = true then 1#64 else 0#64 := by
  unfold join64; bv_decide

theorem mux_limbs (c0 c1 a0 a1 b0 b1 : UInt32) :
    (join64 (if decide (join64 c0 c1 ≠ join64 0 0) = true then a0 else b0)
            (if decide (join64 c0 c1 ≠ join64 0 0) = true then a1 else b1)).toBitVec =
      if ((join64 c0 c1).toBitVec != 0#64) = true then (join64 a0 a1).toBitVec else (join64 b0 b1).toBitVec := by
  unfold join64; bv_decide

theorem shr_big (x : BitVec 64) (n : Nat) (h : 64 ≤ n) : x >>> n = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

theorem shl_big (x : BitVec 64) (n : Nat) (h : 64 ≤ n) : x <<< n = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 + k := ⟨n - 64, by omega⟩
  rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm (x.toNat) (2 ^ 64), Nat.mul_assoc, Nat.mul_mod_right]

theorem amt_eq (n : UInt64) (hn : n.toNat < 64) : n.toUInt32.toUInt64 &&& 63 = n := by
  have h : n < 64 := by rw [UInt64.lt_iff_toNat_lt]; simpa using hn
  bv_decide

theorem shl_amt (x n : UInt64) (hn : n.toNat < 64) :
    (x <<< (n.toUInt32.toUInt64 &&& 63)).toBitVec = x.toBitVec <<< n.toBitVec.toNat := by
  rw [amt_eq n hn, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']
  congr 1
  simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec]
  simp; omega

theorem shr_amt (x n : UInt64) (hn : n.toNat < 64) :
    (x >>> (n.toUInt32.toUInt64 &&& 63)).toBitVec = x.toBitVec >>> n.toBitVec.toNat := by
  rw [amt_eq n hn, UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq']
  congr 1
  simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec]
  simp; omega

theorem split_join (x : UInt64) : join64 x.toUInt32 (x >>> 32).toUInt32 = x := by unfold join64; bv_decide

/-! ## 2. Pairs of terms for 64-bit words -/

abbrev TP := Tm × Tm

/-- The 64-bit word a pair of 32-bit terms denotes. -/
def TP.ev (env : UInt64 → UInt32) (p : TP) : Word := (join64 (p.1.eval env) (p.2.eval env)).toBitVec

def pLit (w : Word) : TP :=
  let x := UInt64.ofBitVec w
  (Dom.lit x.toUInt32, Dom.lit (x >>> 32).toUInt32)

def pAdd (a b : TP) : TP := (Dom.add a.1 b.1, Dom.addc a.2 b.2 (Dom.carry a.1 b.1))
def pSub (a b : TP) : TP := (Dom.sub a.1 b.1, Dom.subc a.2 b.2 (Dom.borrow a.1 b.1))
def pMul (a b : TP) : TP := (Dom.mul a.1 b.1, Dom.add (Dom.add (Dom.mulHi a.1 b.1) (Dom.mul a.2 b.1)) (Dom.mul a.1 b.2))
def pAnd (a b : TP) : TP := (Dom.band a.1 b.1, Dom.band a.2 b.2)
def pOr (a b : TP) : TP := (Dom.bor a.1 b.1, Dom.bor a.2 b.2)
def pUlt (a b : TP) : TP := (Dom.ite (Dom.ult64 a.1 a.2 b.1 b.2) (Dom.lit 1) (Dom.lit 0), Dom.lit 0)
def pMux (c a b : TP) : TP :=
  let z := Dom.ne64 c.1 c.2 (Dom.lit 0) (Dom.lit 0)
  (Dom.ite z a.1 b.1, Dom.ite z a.2 b.2)

/-- A shift by an amount the specification knows (a constant word); `none` otherwise. -/
def pShift (left : Bool) (a amt : TP) : Option TP :=
  match amt.1.litVal?, amt.2.litVal? with
  | some lo, some hi =>
    let n := join64 lo hi
    if 64 ≤ n then some (Dom.lit 0, Dom.lit 0)
    else some (if left then Dom.shl64 (Dom.lit n.toUInt32) a.1 a.2 else Dom.lshr64 (Dom.lit n.toUInt32) a.1 a.2)
  | _, _ => none

section
variable (env : UInt64 → UInt32)

theorem ev_lit (w : Word) : (pLit w).ev env = w := by
  simp only [TP.ev, pLit]
  rw [show (Dom.lit (UInt64.ofBitVec w).toUInt32 : Tm) = Tm.lit (UInt64.ofBitVec w).toUInt32 from rfl,
    show (Dom.lit (UInt64.ofBitVec w >>> 32).toUInt32 : Tm) = Tm.lit (UInt64.ofBitVec w >>> 32).toUInt32 from rfl,
    Tm.eval_lit, Tm.eval_lit, split_join]

theorem ev_add (a b : TP) : (pAdd a b).ev env = a.ev env + b.ev env := by
  simp only [TP.ev, pAdd]
  rw [Tm.eval_add, Tm.eval_addc, Tm.eval_carry]
  simp only [Dom.add, Dom.addc, Dom.carry, addCi, carry_eq, w2b_b2w]
  rw [← UInt64.toBitVec_add, ← add_limbs]

theorem ev_sub (a b : TP) : (pSub a b).ev env = a.ev env - b.ev env := by
  simp only [TP.ev, pSub]
  rw [Tm.eval_sub, Tm.eval_subc, Tm.eval_borrow]
  simp only [Dom.sub, Dom.subc, Dom.borrow, subCi, borrow_eq, w2b_b2w]
  rw [← UInt64.toBitVec_sub, ← sub_limbs]

theorem ev_mul (a b : TP) : (pMul a b).ev env = a.ev env * b.ev env := by
  simp only [TP.ev, pMul]
  rw [Tm.eval_add, Tm.eval_add, Tm.eval_mul, Tm.eval_mul, Tm.eval_mul, Tm.eval_mulHi]
  simp only [Dom.add, Dom.mul, Dom.mulHi, mulLo, mulHi_eq]
  rw [← UInt64.toBitVec_mul, ← mul_limbs]

theorem ev_and (a b : TP) : (pAnd a b).ev env = a.ev env &&& b.ev env := by
  simp only [TP.ev, pAnd]; rw [Tm.eval_and, Tm.eval_and]; simp only [Dom.band]
  rw [← UInt64.toBitVec_and, ← and_limbs]

theorem ev_or (a b : TP) : (pOr a b).ev env = a.ev env ||| b.ev env := by
  simp only [TP.ev, pOr]; rw [Tm.eval_or, Tm.eval_or]; simp only [Dom.bor]
  rw [← UInt64.toBitVec_or, ← or_limbs]

theorem ev_ult (a b : TP) : (pUlt a b).ev env = if BitVec.ult (a.ev env) (b.ev env) then 1#64 else 0#64 := by
  simp only [TP.ev, pUlt]
  rw [Tm.eval_ite, Tm.eval_ult64]
  simp only [Dom.ite, Dom.ult64, w2b_b2w]
  rw [show (Dom.lit 1 : Tm) = Tm.lit 1 from rfl, show (Dom.lit 0 : Tm) = Tm.lit 0 from rfl, Tm.eval_lit, Tm.eval_lit]
  exact ult_limbs _ _ _ _

theorem ev_mux (c a b : TP) : (pMux c a b).ev env = if c.ev env != 0#64 then a.ev env else b.ev env := by
  simp only [TP.ev, pMux]
  rw [Tm.eval_ite, Tm.eval_ite, Tm.eval_ne64]
  simp only [Dom.ite, Dom.ne64, w2b_b2w]
  rw [show (Dom.lit 0 : Tm) = Tm.lit 0 from rfl, Tm.eval_lit]
  exact mux_limbs _ _ _ _ _ _

theorem ev_shift (left : Bool) (a amt r : TP) (h : pShift left a amt = some r) :
    r.ev env = if left then a.ev env <<< (amt.ev env).toNat else a.ev env >>> (amt.ev env).toNat := by
  unfold pShift at h
  split at h
  · rename_i lo hi hlo hhi
    have elo := Tm.eval_of_litVal env amt.1 lo hlo
    have ehi := Tm.eval_of_litVal env amt.2 hi hhi
    have hamt : amt.ev env = (join64 lo hi).toBitVec := by simp [TP.ev, elo, ehi]
    rw [hamt]
    generalize join64 lo hi = n at h
    by_cases hn : 64 ≤ n
    · rw [ite_eq_left hn] at h
      simp only [Option.some.injEq] at h; subst h
      have hn' : 64 ≤ n.toBitVec.toNat := by simpa [UInt64.le_iff_toNat_le] using hn
      simp only [TP.ev]
      rw [show (Dom.lit 0 : Tm) = Tm.lit 0 from rfl, Tm.eval_lit]
      have z : (join64 0 0).toBitVec = 0#64 := by decide
      cases left
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [z, shr_big _ _ hn']
      · simp only [↓reduceIte]; rw [z, shl_big _ _ hn']
    · rw [ite_eq_right hn] at h
      simp only [Option.some.injEq] at h; subst h
      have hn' : n.toNat < 64 := by simpa [UInt64.le_iff_toNat_le] using hn
      cases left with
      | true =>
        have e := Tm.eval_shl64 env (Dom.lit n.toUInt32) a.1 a.2
        have e1 : Tm.eval env (Dom.shl64 (Dom.lit n.toUInt32) a.1 a.2 : TP).1 = _ := congrArg Prod.fst e
        have e2 : Tm.eval env (Dom.shl64 (Dom.lit n.toUInt32) a.1 a.2 : TP).2 = _ := congrArg Prod.snd e
        simp only [TP.ev, ↓reduceIte]
        rw [e1, e2, Tm.eval_lit']
        simp only [Dom.shl64, Dom.lit, lshlrev64, split_join]
        exact shl_amt _ n hn'
      | false =>
        have e := Tm.eval_lshr64 env (Dom.lit n.toUInt32) a.1 a.2
        have e1 : Tm.eval env (Dom.lshr64 (Dom.lit n.toUInt32) a.1 a.2 : TP).1 = _ := congrArg Prod.fst e
        have e2 : Tm.eval env (Dom.lshr64 (Dom.lit n.toUInt32) a.1 a.2 : TP).2 = _ := congrArg Prod.snd e
        simp only [TP.ev, Bool.false_eq_true, ↓reduceIte]
        rw [e1, e2, Tm.eval_lit']
        simp only [Dom.lshr64, Dom.lit, lshrrev64, split_join]
        exact shr_amt _ n hn'
  · simp at h

end

/-! ## 3. A kernel's value at an element -/

def argP (args : List TP) (i : Nat) : TP := args.getD i (pLit 0#64)

/-- `evalElemOp` on pairs; `none` when a shift amount is not a known constant. -/
def pElem (op : ElemOp) (args : List TP) : Option TP :=
  match op with
  | .scalar (.const v) => some (pLit (BitVec.ofInt 64 v))
  | .scalar .add => some (pAdd (argP args 0) (argP args 1))
  | .scalar .sub => some (pSub (argP args 0) (argP args 1))
  | .scalar .mul => some (pMul (argP args 0) (argP args 1))
  | .scalar (.scale k) => some (pMul (pLit (BitVec.ofInt 64 k)) (argP args 0))
  | .scalar .mac => some (pAdd (pMul (argP args 0) (argP args 1)) (argP args 2))
  | .scalar .mux => some (pMux (argP args 0) (argP args 1) (argP args 2))
  | .ult => some (pUlt (argP args 0) (argP args 1))
  | .band => some (pAnd (argP args 0) (argP args 1))
  | .bor => some (pOr (argP args 0) (argP args 1))
  | .shr => pShift false (argP args 0) (argP args 1)
  | .shl => pShift true (argP args 0) (argP args 1)

/-- An array lookup is the lookup in its list (the check reads arrays, the plan lists). -/
theorem array_getD_toList {α : Type} (a : Array α) (i : Nat) (d : α) : a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

def pOperand (cs : Array Word) (rd : Nat → TP) (e : Nat) (loc : Nat → TP) : KOperand → TP
  | .read b => rd (b + e)
  | .cst i => pLit (cs.getD i 0#64)
  | .tmp w => loc w

def pStep (cs : Array Word) (rd : Nat → TP) (e : Nat) (loc : Nat → TP) (i : KInstr) : Option (Nat → TP) :=
  (pElem i.op (i.args.map (pOperand cs rd e loc))).map fun v => fun w => if w == i.dst then v else loc w

def pCode (cs : Array Word) (rd : Nat → TP) (e : Nat) : (Nat → TP) → List KInstr → Option (Nat → TP)
  | loc, [] => some loc
  | loc, i :: is => (pStep cs rd e loc i).bind fun loc' => pCode cs rd e loc' is

/-- A fold's combining operation on pairs (`ReduceOp.combine`). -/
def pCombine : ReduceOp → TP → TP → TP
  | .add => pAdd | .mul => pMul | .band => pAnd | .bor => pOr

/-- `foldRange` on pairs: the left fold of `start .. start + len - 1` from `init`. -/
def pFoldRange (op : ReduceOp) (rd : Nat → TP) (start len : Nat) (init : TP) : TP :=
  (List.range' start len).foldl (fun acc i => pCombine op acc (rd i)) init

/-- `kernelValue` as a pair of 32-bit terms, reading word `a` of the wire buffer as `rd a`. -/
def pKernel (cs : Array Word) (ix : Array Nat) (rd : Nat → TP) (k : Kernel) (e : Nat) : Option TP :=
  match k.body with
  | .prog code out => (pCode cs rd e (fun _ => pLit 0#64) code).map (· out)
  | .gather ixb b => some (rd (b + ix.getD (ixb + e) 0))
  | .concat b0 l0 b1 => some (if e < l0 then rd (b0 + e) else rd (b1 + (e - l0)))
  | .const cb => some (pLit (cs.getD (cb + e) 0#64))
  | .fold op shape b =>
    if e < shape.ranges.length then
      let r := shape.ranges.getD e (0, 0)
      some (pFoldRange op (fun i => rd (b + i)) r.1 r.2 (pLit op.identity))
    else some (pLit 0#64)

/-- A fold kernel's values for every element at once, each prefix extended by one combine when the next
range extends the previous one (a scan), so a stage's fold costs its input once (`foldRangesCached`). -/
def foldCachedGo (op : ReduceOp) (rd : Nat → TP) : List (Nat × Nat) → Nat → Nat → TP → Array TP → Array TP
  | [], _, _, _, acc => acc
  | (st, l) :: rs, ps, pl, prev, acc =>
    let v := if st == ps && l == pl + 1 then pCombine op prev (rd (st + pl)) else pFoldRange op rd st l (pLit op.identity)
    foldCachedGo op rd rs st l v (acc.push v)

def foldValues (rd : Nat → TP) (k : Kernel) : Option (Array TP) :=
  match k.body with
  | .fold op shape b => some (foldCachedGo op (fun i => rd (b + i)) shape.ranges 0 0 (pLit op.identity) #[])
  | _ => none

section
variable (env : UInt64 → UInt32)

theorem ev_argP (args : List TP) (i : Nat) : (argP args i).ev env = (args.map (·.ev env)).getD i 0#64 := by
  unfold argP
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases args[i]? <;> simp [ev_lit]

theorem pElem_sound (op : ElemOp) (args : List TP) (r : TP) (h : pElem op args = some r) :
    r.ev env = evalElemOp op (args.map (·.ev env)) := by
  cases op with
  | scalar o =>
    cases o <;> simp only [pElem, Option.some.injEq] at h <;> subst h <;>
      simp [evalElemOp, evalHypergraphOpBv, ev_lit, ev_add, ev_sub, ev_mul, ev_mux, ev_argP]
  | ult => simp only [pElem, Option.some.injEq] at h; subst h; simp [evalElemOp, ev_ult, ev_argP]
  | band => simp only [pElem, Option.some.injEq] at h; subst h; simp [evalElemOp, ev_and, ev_argP]
  | bor => simp only [pElem, Option.some.injEq] at h; subst h; simp [evalElemOp, ev_or, ev_argP]
  | shr =>
    simp only [pElem] at h
    rw [ev_shift env false _ _ r h]; simp [evalElemOp, ev_argP]
  | shl =>
    simp only [pElem] at h
    rw [ev_shift env true _ _ r h]; simp [evalElemOp, ev_argP]

theorem pOperand_sound (cs : Array Word) (rd : Nat → TP) (e : Nat) (loc : Nat → TP) (locC : Nat → Word)
    (hloc : ∀ w, (loc w).ev env = locC w) (o : KOperand) :
    (pOperand cs rd e loc o).ev env = readOperand cs.toList (fun a => (rd a).ev env) e locC o := by
  cases o <;> simp [pOperand, readOperand, ev_lit, hloc, array_getD_toList]

theorem pCode_sound (cs : Array Word) (rd : Nat → TP) (e : Nat) :
    ∀ (code : List KInstr) (loc : Nat → TP) (locC : Nat → Word) (loc' : Nat → TP),
      (∀ w, (loc w).ev env = locC w) → pCode cs rd e loc code = some loc' →
      ∀ w, (loc' w).ev env = runKCode cs.toList (fun a => (rd a).ev env) e locC code w
  | [], loc, locC, loc', hloc, h => by
    simp only [pCode, Option.some.injEq] at h; subst h; exact hloc
  | i :: is, loc, locC, loc', hloc, h => by
    simp only [pCode, Option.bind_eq_some_iff] at h
    obtain ⟨l1, hl1, hrest⟩ := h
    simp only [runKCode, List.foldl_cons]
    refine pCode_sound cs rd e is l1 _ loc' ?_ hrest
    simp only [pStep, Option.map_eq_some_iff] at hl1
    obtain ⟨v, hv, rfl⟩ := hl1
    intro w
    have hv' := pElem_sound env i.op _ v hv
    rw [List.map_map] at hv'
    simp only [stepKInstr]
    split
    · rw [hv']; congr 1; apply List.map_congr_left; intro o _
      exact pOperand_sound env cs rd e loc locC hloc o
    · exact hloc w

theorem ev_combine (op : ReduceOp) (a b : TP) : (pCombine op a b).ev env = op.combine (a.ev env) (b.ev env) := by
  cases op <;> simp [pCombine, ReduceOp.combine, ev_add, ev_mul, ev_and, ev_or]

theorem ev_foldRange (op : ReduceOp) (rd : Nat → TP) (st len : Nat) (init : TP) :
    (pFoldRange op rd st len init).ev env = foldRange op (fun i => (rd i).ev env) st len (init.ev env) := by
  unfold pFoldRange foldRange
  generalize List.range' st len = xs
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, ev_combine]

theorem pKernel_sound (cs : Array Word) (ix : Array Nat) (rd : Nat → TP) (k : Kernel) (e : Nat) (r : TP)
    (h : pKernel cs ix rd k e = some r) :
    r.ev env = kernelValue cs.toList ix.toList (fun a => (rd a).ev env) k e := by
  unfold pKernel at h
  unfold kernelValue
  split at h
  · rename_i code out hb
    rw [hb]
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨loc', hc, rfl⟩ := h
    exact pCode_sound env cs rd e code _ (fun _ => 0#64) loc' (fun w => ev_lit env 0#64) hc out
  · rename_i ixb b hb; rw [hb]; simp only [Option.some.injEq] at h; subst h; simp only [array_getD_toList]
  · rename_i b0 l0 b1 hb; rw [hb]; simp only [Option.some.injEq] at h; subst h
    by_cases he : e < l0 <;> simp [he]
  · rename_i cb hb; rw [hb]; simp only [Option.some.injEq] at h; subst h
    rw [ev_lit, array_getD_toList]
  · rename_i op shape b hb; rw [hb]; dsimp only
    unfold evalFold
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h; subst h
      rw [ev_foldRange, ev_lit]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]
    · rename_i he
      simp only [Option.some.injEq] at h; subst h
      rw [ev_lit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by omega)]
      rfl

theorem pFoldRange_succ (op : ReduceOp) (rd : Nat → TP) (st l : Nat) (init : TP) :
    pFoldRange op rd st (l + 1) init = pCombine op (pFoldRange op rd st l init) (rd (st + l)) := by
  unfold pFoldRange; rw [List.range'_concat, List.foldl_append]; simp

theorem foldCachedGo_get (op : ReduceOp) (rd : Nat → TP) :
    ∀ (rs : List (Nat × Nat)) (ps pl : Nat) (prev : TP) (acc : Array TP),
      prev = pFoldRange op rd ps pl (pLit op.identity) →
      ∀ e, (foldCachedGo op rd rs ps pl prev acc)[e]? =
        if e < acc.size then acc[e]? else (rs.map fun r => pFoldRange op rd r.1 r.2 (pLit op.identity))[e - acc.size]?
  | [], _, _, _, acc, _, e => by
    simp only [foldCachedGo, List.map_nil, List.getElem?_nil]
    split
    · rfl
    · rename_i he; exact Array.getElem?_eq_none (by omega)
  | (st, l) :: rs, ps, pl, prev, acc, hp, e => by
    have hv : (if st == ps && l == pl + 1 then pCombine op prev (rd (st + pl)) else pFoldRange op rd st l (pLit op.identity)) =
        pFoldRange op rd st l (pLit op.identity) := by
      split
      · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
        rw [hp, pFoldRange_succ]
      · rfl
    simp only [foldCachedGo]
    rw [foldCachedGo_get op rd rs st l _ _ hv e, hv]
    simp only [Array.size_push, List.map_cons]
    by_cases h1 : e < acc.size
    · rw [if_pos (by omega), if_pos h1, Array.getElem?_push_lt h1, Array.getElem?_eq_getElem h1]
    · rw [if_neg h1]
      by_cases h2 : e = acc.size
      · subst h2; rw [if_pos (by omega), Array.getElem?_push_eq]; simp
      · rw [if_neg (by omega), show e - acc.size = (e - (acc.size + 1)) + 1 by omega]; simp

/-- A cached fold value is the kernel's value term at that element. -/
theorem foldValues_get (cs : Array Word) (ix : Array Nat) (rd : Nat → TP) (k : Kernel) (arr : Array TP)
    (h : foldValues rd k = some arr) (e : Nat) (r : TP) (he : arr[e]? = some r) : pKernel cs ix rd k e = some r := by
  unfold foldValues at h
  split at h
  · rename_i op shape b hb
    simp only [Option.some.injEq] at h; subst h
    rw [foldCachedGo_get op _ shape.ranges 0 0 _ #[] (by simp [pFoldRange]) e] at he
    simp only [List.size_toArray, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
      List.getElem?_map, Array.size_empty] at he
    unfold pKernel; rw [hb]
    cases hr : shape.ranges[e]? with
    | none => rw [hr] at he; simp at he
    | some rg =>
      rw [hr] at he; simp only [Option.map_some, Option.some.injEq] at he; subst he
      have hlt : e < shape.ranges.length := by
        rcases List.getElem?_eq_some_iff.mp hr with ⟨hl, _⟩; exact hl
      dsimp only
      rw [if_pos hlt]
      simp [List.getD_eq_getElem?_getD, hr]
  · simp at h

end
end Obend.Hardware.Gpu.Rdna2
