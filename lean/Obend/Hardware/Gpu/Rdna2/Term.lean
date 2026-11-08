/-
# Obend.Hardware.Gpu.Rdna2.Term — the symbolic instance of the wave model

A `Tm` is a 32-bit term over the dwords of memory (`var a`), built by smart constructors that fold
constants and normalize the commutative operations (sums flattened, operands ordered by a cached
structural hash), so that the code a compiler emits and the specification lowered to 32-bit pieces meet
as the same term wherever they compute the same thing the same way. `Tm.eval env` is its value when
memory holds `env`; the semantics of every operation (`TOp.sem`) is stated with bitvector conditions only
(a carry is `a + b < a`), so `bv_decide` reads it, and `sem_*` lemmas tie each to the model's own
operation (`Dom UInt32`, the manual's pseudo-code). `eval_*` lemmas say each smart constructor
evaluates to the model's operation on the values of its operands: they are what makes the symbolic run of
`Semantics` a run of the model (`Obend.Hardware.Gpu.Rdna2.Natural`).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Semantics
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. Bitvector forms of the model's operations -/

/-- The carry of `a + b`, the borrow of `a - b`, with a carry/borrow in, as bitvector conditions. -/
def carryBV (a b : UInt32) : Bool := a + b < a
def carrycBV (a b ci : UInt32) : Bool := a + b < a || (ci != 0 && a + b == 0xFFFFFFFF)
def borrowBV (a b : UInt32) : Bool := a < b
def borrowcBV (a b ci : UInt32) : Bool := if ci != 0 then a ≤ b else a < b
def mulHiBV (a b : UInt32) : UInt32 := ((a.toUInt64 * b.toUInt64) >>> 32).toUInt32

theorem carry_eq (a b : UInt32) : (addCo a b).2 = carryBV a b := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  simp only [addCo, carryBV, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem carryc_eq (a b ci : UInt32) : (addCi a b (w2b ci)).2 = carrycBV a b ci := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  simp only [addCi, carrycBV, w2b, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
  have hff : (a + b == 0xFFFFFFFF) = decide ((a.toNat + b.toNat) % 2 ^ 32 = 4294967295) := by
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj, UInt32.toNat_add]; rfl
  rw [hff]
  by_cases hc : ci = 0
  · subst hc; rw [Bool.eq_iff_iff]; simp; omega
  · have hc' : (ci != 0) = true := by simpa using hc
    rw [Bool.eq_iff_iff]; simp only [hc', ↓reduceIte, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]; omega

theorem borrow_eq (a b : UInt32) : (subCo a b).2 = borrowBV a b := by
  simp [subCo, borrowBV, UInt32.lt_iff_toNat_lt]

theorem borrowc_eq (a b ci : UInt32) : (subCi a b (w2b ci)).2 = borrowcBV a b ci := by
  simp only [subCi, borrowcBV, w2b]
  by_cases hc : ci = 0
  · subst hc; simp [UInt32.lt_iff_toNat_lt]
  · have hc' : (ci != 0) = true := by simpa using hc
    simp only [hc', ↓reduceIte, UInt32.le_iff_toNat_le]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem mulHi_eq (a b : UInt32) : mulHi a b = mulHiBV a b := by
  have hlt : a.toNat * b.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' a.toNat_lt b.toNat_lt; simpa using this
  apply UInt32.toNat.inj
  simp only [mulHi, mulHiBV, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_mul,
    UInt32.toNat_toUInt64, UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  generalize a.toNat * b.toNat = x at *
  have h1 : x % 2 ^ 64 = x := Nat.mod_eq_of_lt hlt
  have h2 : (UInt64.toNat 32 % 64) = 32 := by decide
  simp only [h1, h2]

/-! ## 2. Terms -/

inductive TOp where
  | lit (v : UInt32)
  | var (a : UInt64)
  | sum
  | sub | mul | mulHi | band | bor | shl | lshr | ite
  | carry | borrow | addc | carryc | subc | borrowc
  | ule | ugt | ult64 | ne64
  | bit (k : Nat)
  | pack
  | shl64lo | shl64hi | lshr64lo | lshr64hi
  | nez64
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The value of an operation on its operands' values; `env` is memory, read by `var`. -/
def TOp.sem (env : UInt64 → UInt32) (op : TOp) (xs : List UInt32) : UInt32 :=
  let a (i : Nat) := xs.getD i 0
  match op with
  | .lit v => v
  | .var addr => env addr
  | .sum => xs.foldr (· + ·) 0
  | .sub => a 0 - a 1
  | .mul => a 0 * a 1
  | .mulHi => mulHiBV (a 0) (a 1)
  | .band => a 0 &&& a 1
  | .bor => a 0 ||| a 1
  | .shl => a 0 <<< (a 1 &&& 31)
  | .lshr => a 0 >>> (a 1 &&& 31)
  | .ite => if a 0 != 0 then a 1 else a 2
  | .carry => b2w (carryBV (a 0) (a 1))
  | .borrow => b2w (borrowBV (a 0) (a 1))
  | .addc => a 0 + a 1 + (if a 2 != 0 then 1 else 0)
  | .carryc => b2w (carrycBV (a 0) (a 1) (a 2))
  | .subc => a 0 - a 1 - (if a 2 != 0 then 1 else 0)
  | .borrowc => b2w (borrowcBV (a 0) (a 1) (a 2))
  | .ule => b2w (a 0 ≤ a 1)
  | .ugt => b2w (a 0 > a 1)
  | .ult64 => b2w (join64 (a 0) (a 1) < join64 (a 2) (a 3))
  | .ne64 => b2w (join64 (a 0) (a 1) != join64 (a 2) (a 3))
  | .bit k => (a 0 >>> k.toUInt32) &&& 1
  | .pack => packWord xs
  | .shl64lo => (lshlrev64 (a 0) (join64 (a 1) (a 2))).toUInt32
  | .shl64hi => (lshlrev64 (a 0) (join64 (a 1) (a 2)) >>> 32).toUInt32
  | .lshr64lo => (lshrrev64 (a 0) (join64 (a 1) (a 2))).toUInt32
  | .lshr64hi => (lshrrev64 (a 0) (join64 (a 1) (a 2)) >>> 32).toUInt32
  | .nez64 => b2w (a 0 != 0 || a 1 != 0)

/-- Operations whose value never depends on memory: everything but `var`. -/
def TOp.pure : TOp → Bool | .var _ => false | _ => true

theorem sem_pure (env env' : UInt64 → UInt32) (o : TOp) (h : o.pure = true) (xs : List UInt32) :
    o.sem env xs = o.sem env' xs := by
  cases o <;> simp_all [TOp.pure, TOp.sem]

/-- A term: an operation on terms, with a structural hash cached at construction (the hash orders
commutative operands and keys the comparison of `Equiv`; the value never depends on it). -/
inductive Tm where
  | mk (h : UInt64) (op : TOp) (args : List Tm)
  deriving Inhabited

namespace Tm

def op : Tm → TOp | mk _ o _ => o
def args : Tm → List Tm | mk _ _ a => a
def hsh : Tm → UInt64 | mk h _ _ => h

def eval (env : UInt64 → UInt32) : Tm → UInt32
  | mk _ o as => o.sem env (as.attach.map fun ⟨t, _⟩ => t.eval env)

@[simp] theorem eval_mk (env : UInt64 → UInt32) (h : UInt64) (o : TOp) (as : List Tm) :
    eval env (mk h o as) = o.sem env (as.map (eval env)) := by
  rw [eval]; congr 1; simp

def node (o : TOp) (as : List Tm) : Tm :=
  mk (mixHash (hash o) (as.foldl (fun acc t => mixHash acc t.hsh) 17)) o as

@[simp] theorem eval_node (env : UInt64 → UInt32) (o : TOp) (as : List Tm) :
    eval env (node o as) = o.sem env (as.map (eval env)) := by simp [node]

def lit (v : UInt32) : Tm := node (.lit v) []
def var (a : UInt64) : Tm := node (.var a) []

@[simp] theorem eval_lit (env : UInt64 → UInt32) (v : UInt32) : eval env (lit v) = v := by simp [lit, TOp.sem]
@[simp] theorem eval_var (env : UInt64 → UInt32) (a : UInt64) : eval env (var a) = env a := by simp [var, TOp.sem]

def litVal? : Tm → Option UInt32
  | mk _ (.lit v) _ => some v
  | _ => none

theorem eval_of_litVal (env : UInt64 → UInt32) (t : Tm) (v : UInt32) (h : t.litVal? = some v) :
    eval env t = v := by
  match t, h with
  | mk _ (.lit w) _, h => simp [litVal?] at h; subst h; simp [TOp.sem]

/-- Fold an operation whose operands are all literals. -/
def fold (o : TOp) (as : List Tm) : Tm :=
  if o.pure then
    match as.mapM litVal? with
    | some vs => lit (o.sem (fun _ => 0) vs)
    | none => node o as
  else node o as

theorem mapM_litVal (env : UInt64 → UInt32) (as : List Tm) (vs : List UInt32) (h : as.mapM litVal? = some vs) :
    as.map (eval env) = vs := by
  induction as generalizing vs with
  | nil => simp at h; subst h; rfl
  | cons t ts ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, rest, hrest, rfl⟩ := h
    simp [eval_of_litVal env t v hv, ih rest hrest]

@[simp] theorem eval_fold (env : UInt64 → UInt32) (o : TOp) (as : List Tm) :
    eval env (fold o as) = o.sem env (as.map (eval env)) := by
  unfold fold
  split
  · rename_i hp
    split
    · rename_i vs hvs
      simp [mapM_litVal env as vs hvs, sem_pure env (fun _ => 0) o hp]
    · simp
  · simp

/-- Insert by hash (ties keep order): the order every commutative operand list is kept in. -/
def insertByHash (t : Tm) : List Tm → List Tm
  | [] => [t]
  | u :: us => if t.hsh ≤ u.hsh then t :: u :: us else u :: insertByHash t us

def sortByHash (ts : List Tm) : List Tm := ts.foldr insertByHash []

theorem add_left_comm32 (a b c : UInt32) : a + (b + c) = b + (a + c) := by
  rw [← UInt32.add_assoc, UInt32.add_comm a b, UInt32.add_assoc]

theorem sum_insert (env : UInt64 → UInt32) (t : Tm) (us : List Tm) :
    ((insertByHash t us).map (eval env)).foldr (· + ·) 0 = eval env t + (us.map (eval env)).foldr (· + ·) 0 := by
  induction us with
  | nil => simp [insertByHash]
  | cons u us ih =>
    simp only [insertByHash]
    split
    · simp
    · simp only [List.map_cons, List.foldr_cons, ih, add_left_comm32]

theorem sum_sort (env : UInt64 → UInt32) (ts : List Tm) :
    ((sortByHash ts).map (eval env)).foldr (· + ·) 0 = (ts.map (eval env)).foldr (· + ·) 0 := by
  induction ts with
  | nil => simp [sortByHash]
  | cons t ts ih =>
    simp only [sortByHash, List.foldr_cons] at ih ⊢
    rw [sum_insert, ih]
    simp


/-! ## 3. Smart constructors -/

/-- Order two commutative operands by hash. -/
def ord (a b : Tm) : Tm × Tm := if b.hsh < a.hsh then (b, a) else (a, b)

theorem ord_comm {α : Type} (f : UInt32 → UInt32 → α) (hc : ∀ x y, f x y = f y x) (env : UInt64 → UInt32) (a b : Tm) :
    f (eval env (ord a b).1) (eval env (ord a b).2) = f (eval env a) (eval env b) := by
  unfold ord; split <;> simp [hc]

def isLit (t : Tm) (v : UInt32) : Bool := t.litVal? == some v

theorem eval_of_isLit (env : UInt64 → UInt32) (t : Tm) (v : UInt32) (h : isLit t v = true) : eval env t = v :=
  eval_of_litVal env t v (by simpa [isLit] using h)

/-- One addend into a running (constant, sorted non-constant terms). -/
def sumStep (acc : UInt32 × List Tm) (t : Tm) : UInt32 × List Tm :=
  match t.litVal? with
  | some v => (acc.1 + v, acc.2)
  | none => (acc.1, insertByHash t acc.2)

def addends (t : Tm) : List Tm := if t.op == .sum then t.args else [t]

theorem sum_addends (env : UInt64 → UInt32) (t : Tm) :
    ((addends t).map (eval env)).foldr (· + ·) 0 = eval env t := by
  match t with
  | mk _ o as =>
    unfold addends; simp only [op, args]
    by_cases ho : o = .sum
    · subst ho; simp [TOp.sem]
    · have : (o == TOp.sum) = false := by simpa using ho
      simp [this]

theorem foldr_append32 (l1 l2 : List UInt32) :
    (l1 ++ l2).foldr (· + ·) 0 = l1.foldr (· + ·) 0 + l2.foldr (· + ·) 0 := by
  induction l1 with
  | nil => simp
  | cons x xs ih => simp [ih, UInt32.add_assoc]

theorem foldr_init32 (l : List UInt32) (c : UInt32) : l.foldr (· + ·) c = c + l.foldr (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, ih, add_left_comm32]

/-- The constant `c` and the ordered non-constant addends, as one term. -/
def finishSum (c : UInt32) (rest : List Tm) : Tm :=
  match (if c == 0 then rest else rest ++ [lit c]) with
  | [] => lit 0
  | [x] => x
  | all => node .sum all

theorem eval_finishSum (env : UInt64 → UInt32) (c : UInt32) (rest : List Tm) :
    eval env (finishSum c rest) = c + (rest.map (eval env)).foldr (· + ·) 0 := by
  have hall : ((if c == 0 then rest else rest ++ [lit c]).map (eval env)).foldr (· + ·) 0 =
      c + (rest.map (eval env)).foldr (· + ·) 0 := by
    by_cases hc : c = 0
    · subst hc; simp
    · have : (c == 0) = false := by simpa using hc
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.map_append, foldr_append32, List.map_cons, List.map_nil,
        List.foldr_cons, List.foldr_nil, eval_lit, UInt32.add_zero, UInt32.add_comm]
  unfold finishSum
  rw [← hall]
  generalize (if c == 0 then rest else rest ++ [lit c]) = all
  match all with
  | [] => simp
  | [x] => simp
  | x :: y :: zs => simp [TOp.sem]

/-- A sum of terms: nested sums flattened, constants added up, the rest ordered by hash. -/
def mkSum (ts : List Tm) : Tm :=
  let acc := (ts.flatMap addends).foldl sumStep (0, [])
  finishSum acc.1 acc.2

theorem sumStep_inv (env : UInt64 → UInt32) (xs : List Tm) (acc : UInt32 × List Tm) :
    (xs.foldl sumStep acc).1 + ((xs.foldl sumStep acc).2.map (eval env)).foldr (· + ·) 0 =
      acc.1 + (acc.2.map (eval env)).foldr (· + ·) 0 + (xs.map (eval env)).foldr (· + ·) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.foldr_cons]
    rw [ih (sumStep acc x)]
    unfold sumStep
    split
    · rename_i v hv
      rw [eval_of_litVal env x v hv]
      simp only [UInt32.add_assoc]; congr 1
      rw [← UInt32.add_assoc, UInt32.add_comm v, UInt32.add_assoc]
    · simp only [sum_insert, UInt32.add_assoc]; congr 1
      rw [← UInt32.add_assoc, ← UInt32.add_assoc, UInt32.add_comm (eval env x)]

theorem foldr_flatMap_addends (env : UInt64 → UInt32) (ts : List Tm) :
    ((ts.flatMap addends).map (eval env)).foldr (· + ·) 0 = (ts.map (eval env)).foldr (· + ·) 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.flatMap_cons, List.map_append, foldr_append32, ih, sum_addends, List.map_cons, List.foldr_cons]

theorem eval_mkSum (env : UInt64 → UInt32) (ts : List Tm) :
    eval env (mkSum ts) = (ts.map (eval env)).foldr (· + ·) 0 := by
  have key := sumStep_inv env (ts.flatMap addends) (0, [])
  simp only [List.map_nil, List.foldr_nil, UInt32.zero_add, UInt32.add_zero, foldr_flatMap_addends] at key
  simp only [mkSum, eval_finishSum, key]

def mkSub (a b : Tm) : Tm := if isLit b 0 then a else fold .sub [a, b]
def mkMul (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else if isLit x 1 then y else if isLit y 1 then x else fold .mul [x, y]
def mkMulHi (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else fold .mulHi [x, y]
def mkAnd (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else if isLit x 0xFFFFFFFF then y else if isLit y 0xFFFFFFFF then x
  else fold .band [x, y]
def mkOr (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 then y else if isLit y 0 then x else fold .bor [x, y]
def mkShl (x a : Tm) : Tm :=
  match a.litVal? with
  | some v => if v &&& 31 == 0 then x else fold .shl [x, a]
  | none => fold .shl [x, a]
def mkLshr (x a : Tm) : Tm :=
  match a.litVal? with
  | some v => if v &&& 31 == 0 then x else fold .lshr [x, a]
  | none => fold .lshr [x, a]
def mkIte (c a b : Tm) : Tm :=
  match c.litVal? with
  | some v => if v != 0 then a else b
  | none => fold .ite [c, a, b]
def mkCarry (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else fold .carry [x, y]
def mkBorrow (a b : Tm) : Tm := if isLit b 0 then lit 0 else fold .borrow [a, b]
def mkAddc (a b c : Tm) : Tm :=
  match c.litVal? with
  | some v => if v != 0 then mkSum [a, b, lit 1] else mkSum [a, b]
  | none => let (x, y) := ord a b; fold .addc [x, y, c]
def mkCarryc (a b c : Tm) : Tm :=
  if isLit c 0 then mkCarry a b else let (x, y) := ord a b; fold .carryc [x, y, c]
def mkSubc (a b c : Tm) : Tm := if isLit c 0 then mkSub a b else fold .subc [a, b, c]
def mkBorrowc (a b c : Tm) : Tm := if isLit c 0 then mkBorrow a b else fold .borrowc [a, b, c]

/-- Terms whose value is `0` or `1`. -/
def isBool (t : Tm) : Bool :=
  match t.op with
  | .carry | .borrow | .carryc | .borrowc | .ule | .ugt | .ult64 | .ne64 | .bit _ | .nez64 => true
  | .lit v => v == 0 || v == 1
  | _ => false

theorem b2w_le (b : Bool) : b2w b = 0 ∨ b2w b = 1 := by cases b <;> simp [b2w]

theorem and1_cases (z : UInt32) : z &&& 1 = 0 ∨ z &&& 1 = 1 := by bv_decide

theorem eval_isBool (env : UInt64 → UInt32) (t : Tm) (h : isBool t = true) : eval env t = 0 ∨ eval env t = 1 := by
  match t with
  | mk _ o as =>
    simp only [isBool, op] at h
    simp only [eval_mk]
    cases o with
    | lit v => simpa [TOp.sem] using h
    | bit k => exact and1_cases _
    | carry | borrow | carryc | borrowc | ule | ugt | ult64 | ne64 | nez64 => exact b2w_le _
    | _ => simp at h

theorem succ_toUInt32 (k : Nat) (_hk : k < 31) : (k + 1).toUInt32 = k.toUInt32 + 1 := by
  apply UInt32.toNat.inj; simp [Nat.toUInt32, UInt32.toNat_add]

theorem bit_packWord (bs : List UInt32) (k : Nat) (hk : k < 32) :
    (packWord bs >>> k.toUInt32) &&& 1 = b2w (w2b (bs.getD k 0)) := by
  induction bs generalizing k with
  | nil =>
    simp only [packWord, List.getD_nil]
    have : w2b 0 = false := rfl
    rw [this]; simp only [b2w]; generalize k.toUInt32 = j; bv_decide
  | cons b bs ih =>
    cases k with
    | zero =>
      have h0 : (0 : Nat).toUInt32 = 0 := rfl
      simp only [packWord, List.getD_cons_zero, h0]
      rcases b2w_le (w2b b) with hb | hb <;> rw [hb] <;> (generalize packWord bs = r) <;> bv_decide
    | succ k =>
      simp only [packWord, List.getD_cons_succ]
      rw [← ih k (by omega), succ_toUInt32 k (by omega)]
      have hk' : k.toUInt32 < 31 := by rw [UInt32.lt_iff_toNat_lt]; simp [Nat.toUInt32]; omega
      generalize k.toUInt32 = j at *; generalize packWord bs = r
      rcases b2w_le (w2b b) with hb | hb <;> rw [hb] <;> bv_decide

def mkPack (bs : List Tm) : Tm := fold .pack bs

/-- Bit `k` of a mask; of a packed mask, its `k`th bit term itself when that is a `0`/`1` term. -/
def mkBit (x : Tm) (k : Nat) : Tm :=
  if x.op == .pack && k < 32 then
    let b := x.args.getD k (lit 0)
    if isBool b then b else fold (.bit k) [x]
  else fold (.bit k) [x]

def mkUle (a b : Tm) : Tm := fold .ule [a, b]
def mkUgt (a b : Tm) : Tm := fold .ugt [a, b]
def mkUlt64 (a0 a1 b0 b1 : Tm) : Tm := fold .ult64 [a0, a1, b0, b1]
def mkNe64 (a0 a1 b0 b1 : Tm) : Tm := fold .ne64 [a0, a1, b0, b1]
def mkNez64 (a b : Tm) : Tm := fold .nez64 [a, b]

/-- A 64-bit shift of a pair by a known count `w < 64`, in 32-bit pieces. -/
def shrPieces (w : UInt32) (lo hi : Tm) : Tm × Tm :=
  if w == 0 then (lo, hi)
  else if w < 32 then (mkOr (mkLshr lo (lit w)) (mkShl hi (lit (32 - w))), mkLshr hi (lit w))
  else if w == 32 then (hi, lit 0)
  else (mkLshr hi (lit (w - 32)), lit 0)

def shlPieces (w : UInt32) (lo hi : Tm) : Tm × Tm :=
  if w == 0 then (lo, hi)
  else if w < 32 then (mkShl lo (lit w), mkOr (mkShl hi (lit w)) (mkLshr lo (lit (32 - w))))
  else if w == 32 then (lit 0, lo)
  else (lit 0, mkShl lo (lit (w - 32)))

def mkLshr64 (c lo hi : Tm) : Tm × Tm :=
  match c.litVal? with
  | some v => shrPieces (v &&& 63) lo hi
  | none => (fold .lshr64lo [c, lo, hi], fold .lshr64hi [c, lo, hi])

def mkShl64 (c lo hi : Tm) : Tm × Tm :=
  match c.litVal? with
  | some v => shlPieces (v &&& 63) lo hi
  | none => (fold .shl64lo [c, lo, hi], fold .shl64hi [c, lo, hi])

instance : Dom Tm where
  lit := lit
  conc := litVal?
  add a b := mkSum [a, b]
  sub := mkSub
  mul := mkMul
  mulHi := mkMulHi
  band := mkAnd
  bor := mkOr
  shl := mkShl
  ite := mkIte
  carry := mkCarry
  borrow := mkBorrow
  addc := mkAddc
  carryc := mkCarryc
  subc := mkSubc
  borrowc := mkBorrowc
  ule := mkUle
  ugt := mkUgt
  ult64 := mkUlt64
  ne64 := mkNe64
  bit := mkBit
  pack := mkPack
  shl64 := mkShl64
  lshr64 := mkLshr64
  nez64 := mkNez64


/-! ## 4. Evaluation laws: each constructor evaluates to the model's operation -/

section Laws
variable (env : UInt64 → UInt32)

theorem carryBV_comm (a b : UInt32) : carryBV a b = carryBV b a := by unfold carryBV; bv_decide
theorem carrycBV_comm (a b c : UInt32) : carrycBV a b c = carrycBV b a c := by unfold carrycBV; bv_decide
theorem mulHiBV_comm (a b : UInt32) : mulHiBV a b = mulHiBV b a := by simp [mulHiBV, UInt64.mul_comm]

theorem eval_add (a b : Tm) : eval env (Dom.add a b) = Dom.add (eval env a) (eval env b) := by
  show eval env (mkSum [a, b]) = eval env a + eval env b
  simp [eval_mkSum]

theorem eval_sub (a b : Tm) : eval env (Dom.sub a b) = Dom.sub (eval env a) (eval env b) := by
  show eval env (mkSub a b) = eval env a - eval env b
  unfold mkSub; split
  · rename_i h; simp [eval_of_isLit env b 0 h]
  · simp [TOp.sem]

theorem eval_mul (a b : Tm) : eval env (Dom.mul a b) = Dom.mul (eval env a) (eval env b) := by
  show eval env (mkMul a b) = mulLo (eval env a) (eval env b)
  have hc := ord_comm (fun x y => mulLo x y) (fun x y => by simp [mulLo, UInt32.mul_comm]) env a b
  try simp only at hc
  rw [← hc]
  unfold mkMul; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [eval_of_isLit env _ 0 h, mulLo]
  · split
    · rename_i _ h; simp [eval_of_isLit env _ 1 h, mulLo]
    · split
      · rename_i _ _ h; simp [eval_of_isLit env _ 1 h, mulLo]
      · simp [TOp.sem, mulLo]

theorem eval_mulHi (a b : Tm) : eval env (Dom.mulHi a b) = Dom.mulHi (eval env a) (eval env b) := by
  show eval env (mkMulHi a b) = mulHi (eval env a) (eval env b)
  rw [mulHi_eq]
  have hc := ord_comm (fun x y => mulHiBV x y) mulHiBV_comm env a b
  try simp only at hc
  rw [← hc]
  unfold mkMulHi; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [eval_of_isLit env _ 0 h, mulHiBV]
  · simp [TOp.sem]

theorem eval_and (a b : Tm) : eval env (Dom.band a b) = Dom.band (eval env a) (eval env b) := by
  show eval env (mkAnd a b) = eval env a &&& eval env b
  have hc := ord_comm (fun x y => x &&& y) (fun x y => UInt32.and_comm x y) env a b
  try simp only at hc
  rw [← hc]
  unfold mkAnd; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [eval_of_isLit env _ 0 h]
  · split
    · rename_i _ h; rw [eval_of_isLit env _ _ h]; generalize eval env y = z; bv_decide
    · split
      · rename_i _ _ h; rw [eval_of_isLit env _ _ h]; generalize eval env x = z; bv_decide
      · simp [TOp.sem]

theorem eval_or (a b : Tm) : eval env (Dom.bor a b) = Dom.bor (eval env a) (eval env b) := by
  show eval env (mkOr a b) = eval env a ||| eval env b
  have hc := ord_comm (fun x y => x ||| y) (fun x y => UInt32.or_comm x y) env a b
  try simp only at hc
  rw [← hc]
  unfold mkOr; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp [eval_of_isLit env _ 0 h]
  · split
    · rename_i _ h; simp [eval_of_isLit env _ 0 h]
    · simp [TOp.sem]

theorem eval_shl (x a : Tm) : eval env (Dom.shl x a) = Dom.shl (eval env x) (eval env a) := by
  show eval env (mkShl x a) = eval env x <<< (eval env a &&& 31)
  unfold mkShl; split
  · rename_i v hv
    rw [eval_of_litVal env a v hv]
    split
    · rename_i h; have : v &&& 31 = 0 := by simpa using h
      rw [this]; generalize eval env x = z; bv_decide
    · simp [TOp.sem, eval_of_litVal env a v hv]
  · simp [TOp.sem]

theorem eval_lshr (x a : Tm) : eval env (mkLshr x a) = eval env x >>> (eval env a &&& 31) := by
  unfold mkLshr; split
  · rename_i v hv
    rw [eval_of_litVal env a v hv]
    split
    · rename_i h; have : v &&& 31 = 0 := by simpa using h
      rw [this]; generalize eval env x = z; bv_decide
    · simp [TOp.sem, eval_of_litVal env a v hv]
  · simp [TOp.sem]

theorem eval_ite (c a b : Tm) : eval env (Dom.ite c a b) = Dom.ite (eval env c) (eval env a) (eval env b) := by
  show eval env (mkIte c a b) = if w2b (eval env c) then eval env a else eval env b
  unfold mkIte; split
  · rename_i v hv; rw [eval_of_litVal env c v hv]; by_cases h : v = 0 <;> simp [h, w2b]
  · simp [TOp.sem, w2b]

theorem eval_carry (a b : Tm) : eval env (Dom.carry a b) = Dom.carry (eval env a) (eval env b) := by
  show eval env (mkCarry a b) = b2w (addCo (eval env a) (eval env b)).2
  rw [carry_eq]
  have hc := ord_comm (fun x y => b2w (carryBV x y)) (fun x y => by rw [carryBV_comm]) env a b
  try simp only at hc
  rw [← hc]
  unfold mkCarry; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [eval_of_isLit env _ 0 h, carryBV, b2w]
  · simp [TOp.sem]

theorem eval_borrow (a b : Tm) : eval env (Dom.borrow a b) = Dom.borrow (eval env a) (eval env b) := by
  show eval env (mkBorrow a b) = b2w (subCo (eval env a) (eval env b)).2
  rw [borrow_eq]; unfold mkBorrow; split
  · rename_i h; simp [eval_of_isLit env _ 0 h, borrowBV, b2w]
  · simp [TOp.sem]

theorem eval_addc (a b c : Tm) : eval env (Dom.addc a b c) = Dom.addc (eval env a) (eval env b) (eval env c) := by
  show eval env (mkAddc a b c) = (addCi (eval env a) (eval env b) (w2b (eval env c))).1
  unfold mkAddc; split
  · rename_i v hv
    rw [eval_of_litVal env c v hv]
    split
    · rename_i h; simp [eval_mkSum, addCi, w2b, h, UInt32.add_assoc]
    · rename_i h; simp at h; subst h; simp [eval_mkSum, addCi, w2b]
  · have hc := ord_comm (fun x y => x + y + (if eval env c != 0 then (1 : UInt32) else 0)) (fun x y => by rw [UInt32.add_comm x]) env a b
    try simp only at hc
    generalize hp : ord a b = p at hc; obtain ⟨x, y⟩ := p
    simp only [eval_fold, List.map_cons, List.map_nil, TOp.sem] at hc ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ, hc, addCi, w2b]
    split <;> simp_all

theorem eval_carryc (a b c : Tm) : eval env (Dom.carryc a b c) = Dom.carryc (eval env a) (eval env b) (eval env c) := by
  show eval env (mkCarryc a b c) = b2w (addCi (eval env a) (eval env b) (w2b (eval env c))).2
  rw [carryc_eq]
  unfold mkCarryc; split
  · rename_i h
    have h0 := eval_of_isLit env _ 0 h
    have := eval_carry env a b
    simp only [Dom.carry] at this
    show eval env (mkCarry a b) = _
    rw [this, carry_eq, h0]; simp [carryBV, carrycBV]
  · have hc := ord_comm (fun x y => b2w (carrycBV x y (eval env c))) (fun x y => by rw [carrycBV_comm]) env a b
    try simp only at hc
    generalize hp : ord a b = p at hc; obtain ⟨x, y⟩ := p
    simp only [eval_fold, List.map_cons, List.map_nil, TOp.sem, List.getD_cons_zero, List.getD_cons_succ] at hc ⊢
    exact hc

theorem eval_subc (a b c : Tm) : eval env (Dom.subc a b c) = Dom.subc (eval env a) (eval env b) (eval env c) := by
  show eval env (mkSubc a b c) = (subCi (eval env a) (eval env b) (w2b (eval env c))).1
  unfold mkSubc; split
  · rename_i h
    have h0 := eval_of_isLit env _ 0 h
    have := eval_sub env a b
    simp only [Dom.sub] at this
    show eval env (mkSub a b) = _
    rw [this, h0]; simp [subCi, w2b]
  · simp [TOp.sem, subCi, w2b]

theorem eval_borrowc (a b c : Tm) : eval env (Dom.borrowc a b c) = Dom.borrowc (eval env a) (eval env b) (eval env c) := by
  show eval env (mkBorrowc a b c) = b2w (subCi (eval env a) (eval env b) (w2b (eval env c))).2
  rw [borrowc_eq]
  unfold mkBorrowc; split
  · rename_i h
    have h0 := eval_of_isLit env _ 0 h
    have := eval_borrow env a b
    simp only [Dom.borrow] at this
    show eval env (mkBorrow a b) = _
    rw [this, borrow_eq, h0]; simp [borrowBV, borrowcBV]
  · simp [TOp.sem]

theorem eval_ule (a b : Tm) : eval env (Dom.ule a b) = Dom.ule (eval env a) (eval env b) := by
  show eval env (mkUle a b) = b2w (eval env a ≤ eval env b); simp [mkUle, TOp.sem]
theorem eval_ugt (a b : Tm) : eval env (Dom.ugt a b) = Dom.ugt (eval env a) (eval env b) := by
  show eval env (mkUgt a b) = b2w (eval env a > eval env b); simp [mkUgt, TOp.sem]
theorem eval_ult64 (a0 a1 b0 b1 : Tm) :
    eval env (Dom.ult64 a0 a1 b0 b1) = Dom.ult64 (eval env a0) (eval env a1) (eval env b0) (eval env b1) := by
  show eval env (mkUlt64 a0 a1 b0 b1) = _; simp [mkUlt64, TOp.sem, Dom.ult64]
theorem eval_ne64 (a0 a1 b0 b1 : Tm) :
    eval env (Dom.ne64 a0 a1 b0 b1) = Dom.ne64 (eval env a0) (eval env a1) (eval env b0) (eval env b1) := by
  show eval env (mkNe64 a0 a1 b0 b1) = _; simp [mkNe64, TOp.sem, Dom.ne64]
theorem eval_nez64 (a b : Tm) : eval env (Dom.nez64 a b) = Dom.nez64 (eval env a) (eval env b) := by
  show eval env (mkNez64 a b) = _; simp [mkNez64, TOp.sem, Dom.nez64]
theorem eval_pack (bs : List Tm) : eval env (Dom.pack bs) = Dom.pack (bs.map (eval env)) := by
  show eval env (mkPack bs) = packWord (bs.map (eval env)); simp [mkPack, TOp.sem]

theorem b2w_w2b_of_bool (v : UInt32) (h : v = 0 ∨ v = 1) : b2w (w2b v) = v := by
  rcases h with rfl | rfl <;> rfl

theorem eval_bit (x : Tm) (k : Nat) : eval env (Dom.bit x k) = Dom.bit (eval env x) k := by
  show eval env (mkBit x k) = (eval env x >>> k.toUInt32) &&& 1
  unfold mkBit; split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hop, hk⟩ := h
    match x, hop with
    | mk hx .pack as, _ =>
      simp only []
      show eval env (if isBool ((mk hx TOp.pack as).args.getD k (lit 0)) = true then (mk hx TOp.pack as).args.getD k (lit 0) else fold (TOp.bit k) [mk hx TOp.pack as]) = _
      split
      · rename_i hb
        simp only [args] at hb ⊢
        rw [eval_mk]; simp only [TOp.sem]
        rw [bit_packWord _ k hk]
        have hget : (as.map (eval env)).getD k 0 = eval env (as.getD k (lit 0)) := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
          cases as[k]? <;> simp
        rw [hget, b2w_w2b_of_bool _ (eval_isBool env _ hb)]
      · simp [TOp.sem]
  · simp [TOp.sem]


theorem shr_pieces_bv (v l h : UInt32) :
    let w := v &&& 63
    let r := join64 l h >>> (v.toUInt64 &&& 63)
    (if w == 0 then (l, h)
      else if w < 32 then ((l >>> (w &&& 31)) ||| (h <<< ((32 - w) &&& 31)), h >>> (w &&& 31))
      else if w == 32 then (h, 0)
      else (h >>> ((w - 32) &&& 31), 0)) = (r.toUInt32, (r >>> 32).toUInt32) := by
  simp only [join64]
  split
  · rename_i h0; simp only [beq_iff_eq] at h0; simp only [Prod.mk.injEq]; constructor <;> bv_decide
  · split
    · rename_i h0 hl; simp only [beq_iff_eq] at h0; simp only [Prod.mk.injEq]; constructor <;> bv_decide
    · split
      · rename_i h0 hl h32; simp only [beq_iff_eq] at h0 h32; simp only [Prod.mk.injEq]; constructor <;> bv_decide
      · rename_i h0 hl h32; simp only [beq_iff_eq] at h0 h32; simp only [Prod.mk.injEq]; constructor <;> bv_decide

theorem shl_pieces_bv (v l h : UInt32) :
    let w := v &&& 63
    let r := join64 l h <<< (v.toUInt64 &&& 63)
    (if w == 0 then (l, h)
      else if w < 32 then (l <<< (w &&& 31), (h <<< (w &&& 31)) ||| (l >>> ((32 - w) &&& 31)))
      else if w == 32 then (0, l)
      else (0, l <<< ((w - 32) &&& 31))) = (r.toUInt32, (r >>> 32).toUInt32) := by
  simp only [join64]
  split
  · rename_i h0; simp only [beq_iff_eq] at h0; simp only [Prod.mk.injEq]; constructor <;> bv_decide
  · split
    · rename_i h0 hl; simp only [beq_iff_eq] at h0; simp only [Prod.mk.injEq]; constructor <;> bv_decide
    · split
      · rename_i h0 hl h32; simp only [beq_iff_eq] at h0 h32; simp only [Prod.mk.injEq]; constructor <;> bv_decide
      · rename_i h0 hl h32; simp only [beq_iff_eq] at h0 h32; simp only [Prod.mk.injEq]; constructor <;> bv_decide

theorem eval_or' (a b : Tm) : eval env (mkOr a b) = eval env a ||| eval env b := eval_or env a b
theorem eval_shl' (x a : Tm) : eval env (mkShl x a) = eval env x <<< (eval env a &&& 31) := eval_shl env x a

theorem eval_shrPieces (w : UInt32) (lo hi : Tm) :
    (eval env (shrPieces w lo hi).1, eval env (shrPieces w lo hi).2) =
      (if w == 0 then (eval env lo, eval env hi)
       else if w < 32 then ((eval env lo >>> (w &&& 31)) ||| (eval env hi <<< ((32 - w) &&& 31)), eval env hi >>> (w &&& 31))
       else if w == 32 then (eval env hi, 0)
       else (eval env hi >>> ((w - 32) &&& 31), 0)) := by
  unfold shrPieces
  split
  · rfl
  · split
    · simp [eval_or', eval_lshr, eval_shl']
    · split
      · simp
      · simp [eval_lshr]

theorem eval_shlPieces (w : UInt32) (lo hi : Tm) :
    (eval env (shlPieces w lo hi).1, eval env (shlPieces w lo hi).2) =
      (if w == 0 then (eval env lo, eval env hi)
       else if w < 32 then (eval env lo <<< (w &&& 31), (eval env hi <<< (w &&& 31)) ||| (eval env lo >>> ((32 - w) &&& 31)))
       else if w == 32 then (0, eval env lo)
       else (0, eval env lo <<< ((w - 32) &&& 31))) := by
  unfold shlPieces
  split
  · rfl
  · split
    · simp [eval_or', eval_lshr, eval_shl']
    · split
      · simp
      · simp [eval_shl']

theorem eval_lshr64 (c lo hi : Tm) :
    (eval env (Dom.lshr64 c lo hi).1, eval env (Dom.lshr64 c lo hi).2) =
      Dom.lshr64 (eval env c) (eval env lo) (eval env hi) := by
  show (eval env (mkLshr64 c lo hi).1, eval env (mkLshr64 c lo hi).2) =
    let r := lshrrev64 (eval env c) (join64 (eval env lo) (eval env hi)); (r.toUInt32, (r >>> 32).toUInt32)
  unfold mkLshr64; split
  · rename_i v hv
    rw [eval_of_litVal env c v hv, eval_shrPieces]
    exact shr_pieces_bv v _ _
  · simp [TOp.sem, lshrrev64, join64]

theorem eval_shl64 (c lo hi : Tm) :
    (eval env (Dom.shl64 c lo hi).1, eval env (Dom.shl64 c lo hi).2) =
      Dom.shl64 (eval env c) (eval env lo) (eval env hi) := by
  show (eval env (mkShl64 c lo hi).1, eval env (mkShl64 c lo hi).2) =
    let r := lshlrev64 (eval env c) (join64 (eval env lo) (eval env hi)); (r.toUInt32, (r >>> 32).toUInt32)
  unfold mkShl64; split
  · rename_i v hv
    rw [eval_of_litVal env c v hv, eval_shlPieces]
    exact shl_pieces_bv v _ _
  · simp [TOp.sem, lshlrev64, join64]

theorem eval_lit' (c : UInt32) : eval env (Dom.lit c : Tm) = Dom.lit c := eval_lit env c

theorem eval_conc (t : Tm) (c : UInt32) (h : Dom.conc t = some c) : eval env t = c := eval_of_litVal env t c h

end Laws

end Tm
end Obend.Hardware.Gpu.Rdna2
