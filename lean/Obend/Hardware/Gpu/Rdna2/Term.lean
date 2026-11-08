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

/-! Structural equality that answers at once for one object at every level: a symbolic run passes one
object along and `shareCommon'` makes equal terms one object, so comparing two equal DAGs costs their
distinct nodes, not their unfolded trees (a hash mismatch answers at once too). -/

mutual
def decEqT (a b : Tm) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    match a, b with
    | mk h1 o1 as1, mk h2 o2 as2 =>
      if hh : h1 = h2 then
        if ho : o1 = o2 then
          match decEqTL as1 as2 with
          | isTrue hl => isTrue (by rw [hh, ho, hl])
          | isFalse hl => isFalse (fun e => by injection e with _ _ e3; exact hl e3)
        else isFalse (fun e => by injection e with _ e2; exact ho e2)
      else isFalse (fun e => by injection e with e1; exact hh e1)
def decEqTL (as bs : List Tm) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match decEqT a b with
    | isTrue h =>
      match decEqTL as bs with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (fun e => by injection e with _ e2; exact h' e2)
    | isFalse h => isFalse (fun e => by injection e with e1; exact h e1)
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
end

instance : DecidableEq Tm := decEqT


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
  let fl := ts.flatMap addends
  -- flattened up to 64 addends; a longer sum keeps its operands (a loop's running sum stays a chain, the
  -- same chain a left fold builds, instead of a list rebuilt at every step)
  let acc := (if fl.length ≤ 64 then fl else ts).foldl sumStep (0, [])
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
  unfold mkSum
  dsimp only
  split
  · have key := sumStep_inv env (ts.flatMap addends) (0, [])
    simp only [List.map_nil, List.foldr_nil, UInt32.zero_add, UInt32.add_zero, foldr_flatMap_addends] at key
    simp only [eval_finishSum, key]
  · have key := sumStep_inv env ts (0, [])
    simp only [List.map_nil, List.foldr_nil, UInt32.zero_add, UInt32.add_zero] at key
    simp only [eval_finishSum, key]

/-- `0 - b`: a literal folded, a negation undone. -/
def mkNeg (b : Tm) : Tm :=
  match b.litVal? with
  | some c => lit (0 - c)
  | none =>
    match b with
    | .mk _ .sub [z, x] => if isLit z 0 then x else fold .sub [lit 0, b]
    | _ => fold .sub [lit 0, b]

/-- `a - b` is the sum `a + (0 - b)`: one form for a compiler's `a + 0xFFFFFFFF` and `a - 1`, and for a
difference however its terms were grouped. -/
def mkSub (a b : Tm) : Tm := if isLit b 0 then a else mkSum [a, mkNeg b]
def mkMul (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else if isLit x 1 then y else if isLit y 1 then x else fold .mul [x, y]
def mkMulHi (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else fold .mulHi [x, y]
def isBool0 (t : Tm) : Bool :=
  match t.op with
  | .carry | .borrow | .carryc | .borrowc | .ule | .ugt | .ult64 | .ne64 | .bit _ | .nez64 => true
  | .lit v => v == 0 || v == 1
  | _ => false

/-- A term whose value is `0` or `1`: a comparison or carry, a bit, `0`/`1`, or one level of `ite`, `&`
or `|` over those (a lane's bit of a combined mask, `select` of a compare). -/
def isBool (t : Tm) : Bool :=
  isBool0 t ||
  match t.op, t.args with
  | .ite, [_, a, b] | .band, [a, b] | .bor, [a, b] => isBool0 a && isBool0 b
  | _, _ => false

/-- Two levels of `ite`, `&` and `|` over 0/1 terms (a 64-bit compare built from dword compares). -/
def isBool2 (t : Tm) : Bool :=
  isBool t ||
  match t.op, t.args with
  | .ite, [_, a, b] | .band, [a, b] | .bor, [a, b] => isBool a && isBool b
  | _, _ => false

def mkAnd0 (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else if isLit x 0xFFFFFFFF then y else if isLit y 0xFFFFFFFF then x
  else fold .band [x, y]
def mkOr0 (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 then y else if isLit y 0 then x else fold .bor [x, y]

/-- `1 & b` of a 0/1 term is `b` (a compare masked to its low bit). -/
def mkAnd (a b : Tm) : Tm :=
  if isLit a 1 && isBool2 b then b else if isLit b 1 && isBool2 a then a else mkAnd0 a b

/-- `y` is `ite y' 0 1` of a 0/1 term `y'` equal to `x`: the two are complements. -/
def isNotOf (y x : Tm) : Bool :=
  match y with
  | .mk _ .ite [y', z, o] => isLit z 0 && isLit o 1 && y' == x && isBool2 x
  | _ => false

/-- `x | ¬x` of a 0/1 term is `1` (a `≤` the compiler wrote as `= ∨ <`, met by `<` as `≠`). -/
def mkOr (a b : Tm) : Tm :=
  if isNotOf a b || isNotOf b a then lit 1 else mkOr0 a b

def mkShl (x a : Tm) : Tm :=
  match a.litVal? with
  | some v => if v &&& 31 == 0 then x else fold .shl [x, a]
  | none => fold .shl [x, a]
def mkLshr (x a : Tm) : Tm :=
  match a.litVal? with
  | some v => if v &&& 31 == 0 then x else fold .lshr [x, a]
  | none => fold .lshr [x, a]
/-- A condition with its `≠ 0` wrappers removed: `ite` tests `c ≠ 0`, and `(x, 0) ≠ (0, 0)` or a select
`ite c k 0` with `k ≠ 0` is nonzero exactly when `x` or `c` is (the compare a source's `select` puts on a
boolean the compiler keeps as a lane mask); a disjunction of conditions, or the maximum of two words, is
nonzero exactly when the `|` of its parts is. -/
def condOf : Nat → Tm → Tm
  | 0, c => c
  | n + 1, c =>
    match c with
    | .mk _ .ne64 [x, z1, z2, z3] => if isLit z1 0 && isLit z2 0 && isLit z3 0 then condOf n x else c
    | .mk _ .ite [c0, t, e] =>
      if (t.litVal?.any (· != 0)) && isLit e 0 then condOf n c0
      -- `max(t, e) ≠ 0` is `t ≠ 0 ∨ e ≠ 0` (a 64-bit `≠ 0` a compiler tests on the max of its halves)
      else if c0.op == .ugt && c0.args == [t, e] then mkOr (condOf n t) (condOf n e)
      else c
    | .mk _ .bor [p, q] => mkOr (condOf n p) (condOf n q)
    | _ => c

/-- `x` out of `ys`, its first structurally equal occurrence. -/
def removeOne (x : Tm) : List Tm → Option (List Tm)
  | [] => none
  | y :: ys => if x = y then some ys else (removeOne x ys).map (y :: ·)

/-- The addends two sums share (as multisets), and what remains of each. -/
def splitCommon : List Tm → List Tm → List Tm × List Tm × List Tm
  | [], ys => ([], [], ys)
  | x :: xs, ys =>
    match removeOne x ys with
    | some ys' => let r := splitCommon xs ys'; (x :: r.1, r.2.1, r.2.2)
    | none => let r := splitCommon xs ys; (r.1, x :: r.2.1, r.2.2)

/-- A select of two values: `c ≠ 0` with its wrappers removed (`condOf`), equal branches one value, and
the addends both branches share moved out of the select (`ite c (x + z) (y + z)` is `ite c x y + z`, the
form a compiler gives an add hoisted past a `select`). -/
def mkIte (c0 a b : Tm) : Tm :=
  let c := condOf 8 c0
  match c.litVal? with
  | some v => if v != 0 then a else b
  | none =>
    if a = b then a else
    -- a select of `1`/`0` on a 0/1 condition is the condition (a carry the compiler materialised)
    if isLit a 1 && isLit b 0 && isBool2 c then c else
    let r := splitCommon (addends a) (addends b)
    if r.1.isEmpty then fold .ite [c, a, b] else mkSum (fold .ite [c, mkSum r.2.1, mkSum r.2.2] :: r.1)
theorem b2w_le (b : Bool) : b2w b = 0 ∨ b2w b = 1 := by cases b <;> simp [b2w]

theorem and1_cases (z : UInt32) : z &&& 1 = 0 ∨ z &&& 1 = 1 := by bv_decide

def mkNe64' (a0 a1 b0 b1 : Tm) : Tm := fold .ne64 [a0, a1, b0, b1]
/-- `x != 0` of a 0/1 select `ite c 1 0` is `c`: the compare of a `select` the compiler removes. -/
def mkNe64Z (a0 a1 b0 b1 : Tm) : Tm :=
  if isLit a1 0 && isLit b0 0 && isLit b1 0 then
    match a0 with
    | .mk _ .ite [c, t, e] => if isLit t 1 && isLit e 0 && isBool2 c then c else mkNe64' a0 a1 b0 b1
    | _ => mkNe64' a0 a1 b0 b1
  else mkNe64' a0 a1 b0 b1
/-- `a ≠ b` of two pairs is symmetric: a literal zero pair second, else the pairs ordered by hash. -/
def mkNe64 (a0 a1 b0 b1 : Tm) : Tm :=
  if (isLit a0 0 && isLit a1 0) || (!(isLit b0 0 && isLit b1 0) && mixHash b0.hsh b1.hsh < mixHash a0.hsh a1.hsh)
  then mkNe64Z b0 b1 a0 a1 else mkNe64Z a0 a1 b0 b1
def mkCarry (a b : Tm) : Tm :=
  let (x, y) := ord a b
  if isLit x 0 || isLit y 0 then lit 0 else fold .carry [x, y]
/-- `ys` without `xs` when `xs` is a subsequence of it (structurally equal terms). A sum's addends are
ordered by hash, so the addends of a sub-sum appear in order; where they do not, the rule just does not
fire. -/
def removeSub : List Tm → List Tm → Option (List Tm)
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xs, y :: ys => if x = y then removeSub xs ys else (removeSub (x :: xs) ys).map (y :: ·)

/-- `a > b`. When `b` is a sum with the addends of `a` among its own, `b = a + r` and `a > a + r` is the
carry of `a + r` (`carryBV a r = a + r < a`): the form a compiler gives `lo < a` for the low half of a
64-bit add, whatever `a` is a sum of. -/
def mkUgt' (a b : Tm) : Tm :=
  -- `0 > b` and `a > 0xFFFFFFFF` never hold
  if isLit a 0 || isLit b 0xFFFFFFFF then lit 0 else
  -- `0xFFFFFFFF > b` is `b ≠ 0xFFFFFFFF`, `a > 0` is `a ≠ 0`: one form for the compiler's compares
  if isLit a 0xFFFFFFFF then mkNe64 b (lit 0) (lit 0xFFFFFFFF) (lit 0) else
  if isLit b 0 then mkNe64 a (lit 0) (lit 0) (lit 0) else
  if b.op == .sum then
    match removeSub (addends a) b.args with
    | some rest => mkCarry a (mkSum rest)
    | none =>
      -- a long sum keeps `a` whole among its operands
      match removeSub [a] b.args with
      | some rest => mkCarry a (mkSum rest)
      | none => fold .ugt [a, b]
  else fold .ugt [a, b]

/-- `a > a` never holds (a compiler's compare of a value with itself). -/
def mkUgt (a b : Tm) : Tm := if a == b then lit 0 else mkUgt' a b
/-- The borrow of `a - b` is `b > a` (`borrowBV a b = a < b`): one form for it and for a compare. -/
def mkBorrow (a b : Tm) : Tm := if isLit b 0 then lit 0 else mkUgt b a
def mkAddc (a b c : Tm) : Tm :=
  match c.litVal? with
  | some v => if v != 0 then mkSum [a, b, lit 1] else mkSum [a, b]
  | none =>
    -- one form for `a + b + c` however the compiler grouped `a + b`: `0 + (a + b) + c`, the sum normalised
    -- (a 0/1 carry is an addend: the form a compiler's `hi + hi' + scc` takes)
    if isBool c then mkSum [a, b, c] else fold .addc [lit 0, mkSum [a, b], c]
def mkCarryc (a b c : Tm) : Tm :=
  if isLit c 0 then mkCarry a b else let (x, y) := ord a b; fold .carryc [x, y, c]
/-- `a - b - c` subtracts the borrow from the difference `a - b`: the form a compiler gives the high half
of a 64-bit subtract (`(a - b) - borrow`). -/
def mkSubc (a b c : Tm) : Tm :=
  if isLit c 0 then mkSub a b else if isLit b 0 then fold .subc [a, b, c] else fold .subc [mkSub a b, lit 0, c]
def mkBorrowc (a b c : Tm) : Tm := if isLit c 0 then mkBorrow a b else fold .borrowc [a, b, c]

/-- Terms whose value is `0` or `1`. -/
theorem eval_isBool0 (env : UInt64 → UInt32) (t : Tm) (h : isBool0 t = true) : eval env t = 0 ∨ eval env t = 1 := by
  match t with
  | mk _ o as =>
    simp only [isBool0, op] at h
    simp only [eval_mk]
    cases o with
    | lit v => simpa [TOp.sem] using h
    | bit k => exact and1_cases _
    | carry | borrow | carryc | borrowc | ule | ugt | ult64 | ne64 | nez64 => exact b2w_le _
    | _ => simp at h

theorem eval_isBool (env : UInt64 → UInt32) (t : Tm) (h : isBool t = true) : eval env t = 0 ∨ eval env t = 1 := by
  unfold isBool at h
  rcases Bool.or_eq_true_iff.mp h with h0 | h1
  · exact eval_isBool0 env t h0
  · obtain ⟨hx, o, as⟩ := t
    simp only [op, args] at h1
    split at h1
    · simp only [Bool.and_eq_true] at h1
      obtain ⟨ha, hb⟩ := h1
      simp only [eval_mk, List.map, TOp.sem]
      split
      · exact eval_isBool0 env _ ha
      · exact eval_isBool0 env _ hb
    all_goals first
      | (simp at h1; done)
      | (simp only [Bool.and_eq_true] at h1
         obtain ⟨ha, hb⟩ := h1
         simp only [eval_mk, List.map, TOp.sem]
         rcases eval_isBool0 env _ ha with h | h <;> rcases eval_isBool0 env _ hb with h' | h' <;>
           simp [h, h'])

theorem eval_isBool2 (env : UInt64 → UInt32) (t : Tm) (h : isBool2 t = true) : eval env t = 0 ∨ eval env t = 1 := by
  unfold isBool2 at h
  rcases Bool.or_eq_true_iff.mp h with h0 | h1
  · exact eval_isBool env t h0
  · obtain ⟨hx, o, as⟩ := t
    simp only [op, args] at h1
    split at h1
    · simp only [Bool.and_eq_true] at h1
      obtain ⟨ha, hb⟩ := h1
      simp only [eval_mk, List.map, TOp.sem]
      split
      · exact eval_isBool env _ ha
      · exact eval_isBool env _ hb
    all_goals first
      | (simp at h1; done)
      | (simp only [Bool.and_eq_true] at h1
         obtain ⟨ha, hb⟩ := h1
         simp only [eval_mk, List.map, TOp.sem]
         rcases eval_isBool env _ ha with h | h <;> rcases eval_isBool env _ hb with h' | h' <;>
           simp [h, h'])

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

/-- Bit `k` of a mask, pushed through `&`, `|` and `0xFFFFFFFF - x` (bitwise not) to the packed lane
bits, so a lane's bit of a mask combined by scalar mask instructions is that lane's own term. -/
def mkBitF : Nat → Tm → Nat → Tm
  | 0, x, k => mkBit x k
  | f + 1, x, k =>
    match x.op, x.args with
    | .band, [a, b] => mkAnd (mkBitF f a k) (mkBitF f b k)
    | .bor, [a, b] => mkOr (mkBitF f a k) (mkBitF f b k)
    | .sub, [a, c] => if isLit a 0xFFFFFFFF then mkSub (lit 1) (mkBitF f c k) else mkBit x k
    | _, _ => mkBit x k

def mkUle (a b : Tm) : Tm := fold .ule [a, b]
def mkUlt64 (a0 a1 b0 b1 : Tm) : Tm := fold .ult64 [a0, a1, b0, b1]
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
  bit x k := mkBitF 8 x k
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

theorem eval_mkNeg (b : Tm) : eval env (mkNeg b) = 0 - eval env b := by
  unfold mkNeg
  split
  · rename_i c hc; rw [eval_of_litVal env b c hc, eval_lit]
  · split
    · split
      · rename_i hz
        simp only [eval_mk, List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, eval_of_isLit env _ _ hz]
        bv_decide
      · simp [TOp.sem]
    · simp [TOp.sem]

theorem eval_sub (a b : Tm) : eval env (Dom.sub a b) = Dom.sub (eval env a) (eval env b) := by
  show eval env (mkSub a b) = eval env a - eval env b
  unfold mkSub; split
  · rename_i h; simp [eval_of_isLit env b 0 h]
  · rw [eval_mkSum]
    simp only [List.map, List.foldr, eval_mkNeg, UInt32.add_zero]
    generalize eval env a = x; generalize eval env b = y; bv_decide

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

theorem eval_and0 (a b : Tm) : eval env (mkAnd0 a b) = eval env a &&& eval env b := by
  have hc := ord_comm (fun x y => x &&& y) (fun x y => UInt32.and_comm x y) env a b
  try simp only at hc
  rw [← hc]
  unfold mkAnd0; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> simp [eval_of_isLit env _ 0 h]
  · split
    · rename_i _ h; rw [eval_of_isLit env _ _ h]; generalize eval env y = z; bv_decide
    · split
      · rename_i _ _ h; rw [eval_of_isLit env _ _ h]; generalize eval env x = z; bv_decide
      · simp [TOp.sem]

theorem eval_or0 (a b : Tm) : eval env (mkOr0 a b) = eval env a ||| eval env b := by
  have hc := ord_comm (fun x y => x ||| y) (fun x y => UInt32.or_comm x y) env a b
  try simp only at hc
  rw [← hc]
  unfold mkOr0; generalize ord a b = p; obtain ⟨x, y⟩ := p; simp only
  split
  · rename_i h; simp [eval_of_isLit env _ 0 h]
  · split
    · rename_i _ h; simp [eval_of_isLit env _ 0 h]
    · simp [TOp.sem]

theorem eval_and (a b : Tm) : eval env (Dom.band a b) = Dom.band (eval env a) (eval env b) := by
  show eval env (mkAnd a b) = eval env a &&& eval env b
  unfold mkAnd
  split
  · rename_i h; simp only [Bool.and_eq_true] at h
    rw [eval_of_isLit env _ _ h.1]
    rcases eval_isBool2 env b h.2 with e | e <;> rw [e] <;> decide
  · split
    · rename_i _ h; simp only [Bool.and_eq_true] at h
      rw [eval_of_isLit env _ _ h.1]
      rcases eval_isBool2 env a h.2 with e | e <;> rw [e] <;> decide
    · exact eval_and0 env a b

theorem isNotOf_or (y x : Tm) (h : isNotOf y x = true) : eval env y ||| eval env x = 1 := by
  unfold isNotOf at h
  split at h
  · rename_i y' z o
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hz, ho⟩, he⟩, hb⟩ := h
    subst he
    rw [eval_mk]
    simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, eval_of_isLit env _ _ hz,
      eval_of_isLit env _ _ ho]
    rcases eval_isBool2 env y' hb with e | e <;> rw [e] <;> decide
  · simp at h

theorem eval_or (a b : Tm) : eval env (Dom.bor a b) = Dom.bor (eval env a) (eval env b) := by
  show eval env (mkOr a b) = eval env a ||| eval env b
  unfold mkOr
  split
  · rename_i h
    rw [eval_lit]
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact (isNotOf_or env a b h).symm
    · rw [UInt32.or_comm]; exact (isNotOf_or env b a h).symm
  · exact eval_or0 env a b

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

theorem eval_mkOr0 (x y : Tm) : eval env (mkOr x y) = eval env x ||| eval env y := eval_or env x y

theorem condOf_nz : ∀ (n : Nat) (c : Tm), (eval env (condOf n c) != 0) = (eval env c != 0)
  | 0, c => rfl
  | n + 1, c => by
    unfold condOf
    split
    · rename_i h x z1 z2 z3
      split
      · rename_i hz
        simp only [Bool.and_eq_true] at hz
        obtain ⟨⟨h1, h2⟩, h3⟩ := hz
        rw [condOf_nz n x, eval_mk]
        simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, eval_of_isLit env _ _ h1,
          eval_of_isLit env _ _ h2, eval_of_isLit env _ _ h3]
        generalize eval env x = v
        have hj : join64 v 0 = join64 0 0 ↔ v = 0 := by unfold join64; bv_decide
        by_cases hv : v = 0
        · subst hv; decide
        · have h1 : (join64 v 0 != join64 0 0) = true := by simpa [bne_iff_ne] using fun h => hv (hj.mp h)
          have h2 : (v != 0) = true := by simpa using hv
          rw [h1, h2]; decide
      · rfl
    · rename_i h c0 t e
      split
      · rename_i hz
        simp only [Bool.and_eq_true, Option.any_eq_true] at hz
        obtain ⟨⟨k, hk, hk0⟩, he⟩ := hz
        rw [condOf_nz n c0, eval_mk]
        simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, eval_of_litVal env t k hk,
          eval_of_isLit env _ _ he]
        by_cases hc : eval env c0 = 0
        · simp [hc]
        · have : (eval env c0 != 0) = true := by simpa using hc
          simp only [this, ite_true]; simpa using hk0
      · split
        · rename_i hu
          rw [eval_mkOr0, eval_mk]
          have hp := condOf_nz n t; have hq := condOf_nz n e
          have hc : eval env c0 = b2w (eval env t > eval env e) := by
            simp only [Bool.and_eq_true, beq_iff_eq] at hu
            obtain ⟨ho, ha⟩ := hu
            match c0, ho, ha with
            | .mk _ .ugt [x, y], _, ha =>
              simp only [args, List.cons.injEq, and_true] at ha; obtain ⟨rfl, rfl⟩ := ha
              simp [TOp.sem]
          simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, hc]
          revert hp hq
          generalize eval env (condOf n t) = x
          generalize eval env (condOf n e) = y
          generalize eval env t = a
          generalize eval env e = b
          simp only [bne, b2w]
          bv_decide
        · rfl
    · rename_i h p q
      rw [eval_mkOr0, eval_mk]
      have hp := condOf_nz n p; have hq := condOf_nz n q
      simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ]
      revert hp hq
      generalize eval env (condOf n p) = x
      generalize eval env (condOf n q) = y
      generalize eval env p = a
      generalize eval env q = b
      simp only [bne]
      bv_decide
    · rfl

theorem removeOne_sum (x : Tm) : ∀ (ys r : List Tm), removeOne x ys = some r →
    (ys.map (eval env)).foldr (· + ·) 0 = eval env x + (r.map (eval env)).foldr (· + ·) 0
  | [], r, h => by simp [removeOne] at h
  | y :: ys, r, h => by
    unfold removeOne at h
    split at h
    · rename_i hx; subst hx; simp only [Option.some.injEq] at h; subst h; simp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r', h', rfl⟩ := h
      rw [List.map_cons, List.foldr_cons, removeOne_sum x ys r' h', List.map_cons, List.foldr_cons]
      generalize eval env x = a; generalize eval env y = b; generalize List.foldr _ _ _ = c
      bv_decide

theorem splitCommon_sum : ∀ (xs ys : List Tm),
    (xs.map (eval env)).foldr (· + ·) 0 = ((splitCommon xs ys).1.map (eval env)).foldr (· + ·) 0
        + ((splitCommon xs ys).2.1.map (eval env)).foldr (· + ·) 0 ∧
    (ys.map (eval env)).foldr (· + ·) 0 = ((splitCommon xs ys).1.map (eval env)).foldr (· + ·) 0
        + ((splitCommon xs ys).2.2.map (eval env)).foldr (· + ·) 0
  | [], ys => by simp [splitCommon]
  | x :: xs, ys => by
    unfold splitCommon
    split
    · rename_i ys' h
      obtain ⟨h1, h2⟩ := splitCommon_sum xs ys'
      simp only [List.map_cons, List.foldr_cons]
      rw [removeOne_sum env x ys ys' h, h1, h2]
      refine ⟨?_, ?_⟩ <;>
      · generalize eval env x = a; generalize List.foldr _ _ _ = b; generalize List.foldr _ _ _ = c
        try generalize List.foldr _ _ _ = d
        bv_decide
    · obtain ⟨h1, h2⟩ := splitCommon_sum xs ys
      simp only [List.map_cons, List.foldr_cons]
      rw [h1, h2]
      refine ⟨?_, rfl⟩
      generalize eval env x = a; generalize List.foldr _ _ _ = b; generalize List.foldr _ _ _ = c
      bv_decide

theorem eval_ite (c a b : Tm) : eval env (Dom.ite c a b) = Dom.ite (eval env c) (eval env a) (eval env b) := by
  show eval env (mkIte c a b) = if w2b (eval env c) then eval env a else eval env b
  have hw : w2b (eval env c) = (eval env (condOf 8 c) != 0) := by rw [condOf_nz]; rfl
  rw [hw]; unfold mkIte
  generalize condOf 8 c = d
  cases hv : d.litVal? with
  | some v => simp only [hv]; rw [eval_of_litVal env d v hv]; by_cases h : v = 0 <;> simp [h]
  | none =>
    simp only [hv]
    by_cases hab : a = b
    · subst hab; simp
    · simp only [hab, ite_false]
      split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨h1, h0⟩, hc⟩ := hb
        rw [eval_of_isLit env _ _ h1, eval_of_isLit env _ _ h0]
        rcases eval_isBool2 env d hc with e | e <;> simp [e]
      split
      · simp [TOp.sem]
      · obtain ⟨h1, h2⟩ := splitCommon_sum env (addends a) (addends b)
        rw [sum_addends] at h1 h2
        rw [eval_mkSum]
        simp only [List.map, eval_fold, TOp.sem, List.getD_cons_zero, List.getD_cons_succ,
          eval_mkSum]
        rw [h1, h2]
        generalize (eval env d != 0) = q
        rw [List.foldr_cons]
        generalize List.foldr (fun x1 x2 => x1 + x2) 0 (List.map (eval env) (splitCommon a.addends b.addends).fst) = cs
        generalize List.foldr (fun x1 x2 => x1 + x2) 0 (List.map (eval env) (splitCommon a.addends b.addends).snd.fst) = x
        generalize List.foldr (fun x1 x2 => x1 + x2) 0 (List.map (eval env) (splitCommon a.addends b.addends).snd.snd) = y
        cases q <;> simp [UInt32.add_comm]

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

theorem removeSub_sum : ∀ (xs ys r : List Tm), removeSub xs ys = some r →
    (ys.map (eval env)).foldr (· + ·) 0 =
      (xs.map (eval env)).foldr (· + ·) 0 + (r.map (eval env)).foldr (· + ·) 0
  | [], ys, r, h => by simp only [removeSub, Option.some.injEq] at h; subst h; simp
  | _ :: _, [], r, h => by simp [removeSub] at h
  | x :: xs, y :: ys, r, h => by
    unfold removeSub at h
    split at h
    · rename_i he
      subst he
      simp only [List.map_cons, List.foldr_cons]
      rw [removeSub_sum xs ys r h, UInt32.add_assoc]
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      have := removeSub_sum (x :: xs) ys r' hr'
      simp only [List.map_cons, List.foldr_cons] at this ⊢
      rw [this]
      generalize eval env x = a; generalize eval env y = b
      generalize List.foldr (fun x1 x2 => x1 + x2) 0 (List.map (eval env) xs) = c
      generalize List.foldr (fun x1 x2 => x1 + x2) 0 (List.map (eval env) r') = d
      bv_decide

theorem eval_mkNe64' (a0 a1 b0 b1 : Tm) :
    eval env (mkNe64' a0 a1 b0 b1) = Dom.ne64 (eval env a0) (eval env a1) (eval env b0) (eval env b1) := by
  simp [mkNe64', TOp.sem, Dom.ne64]
theorem ne64_sel (c : UInt32) (h : c = 0 ∨ c = 1) :
    c = Dom.ne64 (if c != 0 then (1 : UInt32) else 0) 0 0 0 := by
  rcases h with rfl | rfl <;> decide
theorem eval_mkNe64Z (a0 a1 b0 b1 : Tm) :
    eval env (mkNe64Z a0 a1 b0 b1) = Dom.ne64 (eval env a0) (eval env a1) (eval env b0) (eval env b1) := by
  unfold mkNe64Z
  split
  · rename_i hz
    simp only [Bool.and_eq_true] at hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    split
    · rename_i h c t e
      split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨ht, he⟩, hc⟩ := hb
        rw [eval_of_isLit env _ _ h1, eval_of_isLit env _ _ h2, eval_of_isLit env _ _ h3, eval_mk]
        simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ]
        rw [eval_of_isLit env _ _ ht, eval_of_isLit env _ _ he]
        exact ne64_sel _ (eval_isBool2 env c hc)
      · exact eval_mkNe64' env _ _ _ _
    · exact eval_mkNe64' env _ _ _ _
  · exact eval_mkNe64' env _ _ _ _
theorem ne64_symm (a0 a1 b0 b1 : UInt32) : Dom.ne64 b0 b1 a0 a1 = Dom.ne64 a0 a1 b0 b1 := by
  simp [Dom.ne64, bne_comm]
theorem eval_ne64 (a0 a1 b0 b1 : Tm) :
    eval env (Dom.ne64 a0 a1 b0 b1) = Dom.ne64 (eval env a0) (eval env a1) (eval env b0) (eval env b1) := by
  show eval env (mkNe64 a0 a1 b0 b1) = _
  unfold mkNe64; split
  · rw [eval_mkNe64Z, ne64_symm]
  · exact eval_mkNe64Z env _ _ _ _
theorem eval_mkUgt' (a b : Tm) : eval env (mkUgt' a b) = b2w (eval env a > eval env b) := by
  unfold mkUgt'
  split
  · rename_i hl
    rcases Bool.or_eq_true_iff.mp hl with h | h
    · rw [eval_of_isLit env _ _ h]; simp [b2w]
    · rw [eval_of_isLit env _ _ h]
      have : ¬ (eval env a > 0xFFFFFFFF) := by
        intro hc; have := UInt32.le_iff_toNat_le.mpr (show (eval env a).toNat ≤ (0xFFFFFFFF : UInt32).toNat by
          have := (eval env a).toNat_lt; simp at this ⊢; omega)
        exact absurd hc (UInt32.not_lt.mpr this)
      simp [b2w, this]
  split
  · rename_i h
    have e := eval_ne64 env b (lit 0) (lit 0xFFFFFFFF) (lit 0)
    simp only [Dom.ne64] at e
    show eval env (mkNe64 b (lit 0) (lit 0xFFFFFFFF) (lit 0)) = _
    rw [e, eval_of_isLit env _ _ h]
    simp only [eval_lit, join64, b2w]
    generalize eval env b = v
    have hj : (v.toUInt64 ||| (0 : UInt32).toUInt64 <<< 32 != (0xFFFFFFFF : UInt32).toUInt64 ||| (0 : UInt32).toUInt64 <<< 32)
        = decide ((0xFFFFFFFF : UInt32) > v) := by
      rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; bv_decide
    rw [hj]
  split
  · rename_i h
    have e := eval_ne64 env a (lit 0) (lit 0) (lit 0)
    simp only [Dom.ne64] at e
    show eval env (mkNe64 a (lit 0) (lit 0) (lit 0)) = _
    rw [e, eval_of_isLit env _ _ h]
    simp only [eval_lit, join64, b2w]
    generalize eval env a = v
    have hj : (v.toUInt64 ||| (0 : UInt32).toUInt64 <<< 32 != (0 : UInt32).toUInt64 ||| (0 : UInt32).toUInt64 <<< 32)
        = decide (v > (0 : UInt32)) := by
      rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; bv_decide
    rw [hj]
  split
  · rename_i hs
    split
    · rename_i rest hr
      have hc := eval_carry env a (mkSum rest)
      simp only [Dom.carry] at hc
      rw [hc, carry_eq, eval_mkSum]
      have hb : eval env b = (b.args.map (eval env)).foldr (· + ·) 0 := by
        rw [← sum_addends env b]; simp [addends, hs]
      rw [hb, removeSub_sum env _ _ _ hr, sum_addends]
      simp only [carryBV, gt_iff_lt]
    · split
      · rename_i rest hr
        have hc := eval_carry env a (mkSum rest)
        simp only [Dom.carry] at hc
        rw [hc, carry_eq, eval_mkSum]
        have hb : eval env b = (b.args.map (eval env)).foldr (· + ·) 0 := by
          rw [← sum_addends env b]; simp [addends, hs]
        rw [hb, removeSub_sum env _ _ _ hr]
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, UInt32.add_zero, carryBV, gt_iff_lt]
      · simp [TOp.sem]
  · simp [TOp.sem]

theorem eval_mkUgt (a b : Tm) : eval env (mkUgt a b) = b2w (eval env a > eval env b) := by
  unfold mkUgt
  split
  · rename_i h; rw [eq_of_beq h]; simp [b2w]
  · exact eval_mkUgt' env a b

theorem eval_borrow (a b : Tm) : eval env (Dom.borrow a b) = Dom.borrow (eval env a) (eval env b) := by
  show eval env (mkBorrow a b) = b2w (subCo (eval env a) (eval env b)).2
  rw [borrow_eq]; unfold mkBorrow; split
  · rename_i h; simp [eval_of_isLit env _ 0 h, borrowBV, b2w]
  · rw [eval_mkUgt]; simp [borrowBV]

theorem eval_addc (a b c : Tm) : eval env (Dom.addc a b c) = Dom.addc (eval env a) (eval env b) (eval env c) := by
  show eval env (mkAddc a b c) = (addCi (eval env a) (eval env b) (w2b (eval env c))).1
  unfold mkAddc; split
  · rename_i v hv
    rw [eval_of_litVal env c v hv]
    split
    · rename_i h; simp [eval_mkSum, addCi, w2b, h, UInt32.add_assoc]
    · rename_i h; simp at h; subst h; simp [eval_mkSum, addCi, w2b]
  · split
    · rename_i hb
      rcases eval_isBool env c hb with h | h <;> simp [eval_mkSum, addCi, w2b, h, UInt32.add_assoc]
    · simp only [eval_fold, List.map_cons, List.map_nil, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, eval_lit,
        eval_mkSum, List.foldr_cons, List.foldr_nil, UInt32.add_zero, UInt32.zero_add, addCi, w2b]
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
  · split
    · simp [TOp.sem, subCi, w2b]
    · have := eval_sub env a b
      simp only [Dom.sub] at this
      rw [eval_fold]
      simp only [List.map, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, eval_lit, subCi, w2b]
      show (eval env (mkSub a b)) - 0 - _ = _
      rw [this]; simp

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
  exact eval_mkUgt env a b
theorem eval_ult64 (a0 a1 b0 b1 : Tm) :
    eval env (Dom.ult64 a0 a1 b0 b1) = Dom.ult64 (eval env a0) (eval env a1) (eval env b0) (eval env b1) := by
  show eval env (mkUlt64 a0 a1 b0 b1) = _; simp [mkUlt64, TOp.sem, Dom.ult64]
theorem eval_nez64 (a b : Tm) : eval env (Dom.nez64 a b) = Dom.nez64 (eval env a) (eval env b) := by
  show eval env (mkNez64 a b) = _; simp [mkNez64, TOp.sem, Dom.nez64]
theorem eval_pack (bs : List Tm) : eval env (Dom.pack bs) = Dom.pack (bs.map (eval env)) := by
  show eval env (mkPack bs) = packWord (bs.map (eval env)); simp [mkPack, TOp.sem]

theorem b2w_w2b_of_bool (v : UInt32) (h : v = 0 ∨ v = 1) : b2w (w2b v) = v := by
  rcases h with rfl | rfl <;> rfl

theorem eval_mkBit (x : Tm) (k : Nat) : eval env (mkBit x k) = (eval env x >>> k.toUInt32) &&& 1 := by
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


theorem bit_band_bv (a b j : UInt32) : ((a &&& b) >>> j) &&& 1 = ((a >>> j) &&& 1) &&& ((b >>> j) &&& 1) := by
  bv_decide
theorem bit_bor_bv (a b j : UInt32) : ((a ||| b) >>> j) &&& 1 = ((a >>> j) &&& 1) ||| ((b >>> j) &&& 1) := by
  bv_decide
theorem bit_not_bv (c j : UInt32) : ((0xFFFFFFFF - c) >>> j) &&& 1 = 1 - ((c >>> j) &&& 1) := by
  bv_decide

theorem eval_mkAnd (a b : Tm) : eval env (mkAnd a b) = eval env a &&& eval env b := eval_and env a b
theorem eval_mkSub (a b : Tm) : eval env (mkSub a b) = eval env a - eval env b := eval_sub env a b
theorem eval_mkOr (a b : Tm) : eval env (mkOr a b) = eval env a ||| eval env b := eval_or env a b

theorem eval_mkBitF (f : Nat) (x : Tm) (k : Nat) :
    eval env (mkBitF f x k) = (eval env x >>> k.toUInt32) &&& 1 := by
  induction f generalizing x with
  | zero => exact eval_mkBit env x k
  | succ f ih =>
    obtain ⟨hx, o, as⟩ := x
    simp only [mkBitF, op, args]
    split
    · rename_i a b
      rw [eval_mkAnd, ih, ih, eval_mk]; simp only [TOp.sem, List.map]; exact (bit_band_bv _ _ _).symm
    · rename_i a b
      rw [eval_mkOr, ih, ih, eval_mk]; simp only [TOp.sem, List.map]; exact (bit_bor_bv _ _ _).symm
    · rename_i a c
      split
      · rename_i hl
        rw [eval_mkSub, eval_lit, ih, eval_mk]; simp only [TOp.sem, List.map]
        rw [eval_of_isLit env a _ hl]; exact (bit_not_bv _ _).symm
      · exact eval_mkBit env _ k
    · exact eval_mkBit env _ k

theorem eval_bit (x : Tm) (k : Nat) : eval env (Dom.bit x k) = Dom.bit (eval env x) k :=
  eval_mkBitF env 8 x k

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
