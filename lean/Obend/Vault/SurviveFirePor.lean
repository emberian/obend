module
public import Obend.Digest.Cshake256
public import Obend.Vault.ChunkedWorld
public import Obend.Vault.Lsafe
import all Obend.Vault.Lsafe

public section
/-!
Systematic byte-field erasure coding, constructive threshold interpolation, and two-level
Merkle retrievability proofs. World recovery is bound to the manifest produced by
`makeFireManifest`; the collision alternative contains unequal cSHAKE messages.
The challenge bound counts the full finite sample space, without a random-oracle assumption.
Custody receipts judge conserved two-account transfers and cumulative mandate depletion; each
receipt commits to the 256-bit vault and mandate identifiers it was issued under.
-/
namespace Obend.Vault.SurviveFirePor
set_option autoImplicit false

abbrev GF256 := BitVec 8

def gfAdd (a b : GF256) : GF256 := a ^^^ b

def xtime (a : GF256) : GF256 :=
  (a <<< 1) ^^^ (if a.getLsbD 7 then 0x1b else 0)

def mulBits : Nat → GF256 → GF256 → GF256
  | 0, _, _ => 0
  | n + 1, a, b =>
    (if b.getLsbD 0 then a else 0) ^^^ mulBits n (xtime a) (b >>> 1)

def gfMul (a b : GF256) : GF256 := mulBits 8 a b

/-- Binary exponentiation; the recursion counts the exponent's remaining bits. -/
def powBits : Nat → GF256 → Nat → GF256
  | 0, _, _ => 1
  | fuel + 1, a, n =>
    let r := powBits fuel (gfMul a a) (n / 2)
    if n % 2 = 0 then r else gfMul a r

def gfPow (a : GF256) (n : Nat) : GF256 := powBits (n.log2 + 1) a n

def gfInv (a : GF256) : GF256 := powBits 8 a 254

theorem gfAdd_comm (a b : GF256) : gfAdd a b = gfAdd b a := BitVec.xor_comm a b

theorem gfAdd_assoc (a b c : GF256) : gfAdd (gfAdd a b) c = gfAdd a (gfAdd b c) :=
  BitVec.xor_assoc a b c

@[simp] theorem gfAdd_self_zero (a : GF256) : gfAdd a a = 0 := BitVec.xor_self (x := a)

@[simp] theorem gfAdd_zero (a : GF256) : gfAdd a 0 = a := BitVec.xor_zero (x := a)

private theorem shift1_xor (a b : GF256) : (a ^^^ b) <<< 1 = (a <<< 1) ^^^ (b <<< 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor]
  cases (decide (i < 8) && !decide (i < 1)) <;>
    cases a.getLsbD (i - 1) <;> cases b.getLsbD (i - 1) <;> rfl

private theorem ushift1_xor (a b : GF256) : (a ^^^ b) >>> 1 = (a >>> 1) ^^^ (b >>> 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp [BitVec.getLsbD_xor]

private theorem xtime_zero : xtime 0 = 0 := rfl

private theorem xtime_add (a b : GF256) : xtime (a ^^^ b) = xtime a ^^^ xtime b := by
  have h7 : (a ^^^ b).getLsbD 7 = (a.getLsbD 7 ^^ b.getLsbD 7) := BitVec.getLsbD_xor
  unfold xtime
  rw [shift1_xor, h7]
  apply BitVec.eq_of_getLsbD_eq; intro i _
  have hz : (0#8).getLsbD i = false := BitVec.getLsbD_zero
  cases a.getLsbD 7 <;> cases b.getLsbD 7 <;> dsimp <;>
    simp only [BitVec.getLsbD_xor, hz] <;>
    cases (a <<< 1).getLsbD i <;> cases (b <<< 1).getLsbD i <;> cases (0x1b : GF256).getLsbD i <;> rfl

private theorem mulBits_zero_right (n : Nat) (a : GF256) : mulBits n a 0 = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change (if (0 : GF256).getLsbD 0 then a else 0) ^^^ mulBits n (xtime a) ((0 : GF256) >>> 1) = 0
    have h0 : (0 : GF256).getLsbD 0 = false := rfl
    have h1 : ((0 : GF256) >>> 1) = 0 := rfl
    simp only [h0, h1, ih, Bool.false_eq_true, ite_false]
    exact BitVec.xor_zero (x := (0 : GF256))

private theorem mulBits_zero_left (n : Nat) (b : GF256) : mulBits n 0 b = 0 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [mulBits, xtime_zero, ih]
    cases b.getLsbD 0 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      exact BitVec.xor_zero (x := (0 : GF256))

@[simp] theorem gfMul_zero (a : GF256) : gfMul a 0 = 0 := mulBits_zero_right 8 a

@[simp] theorem gfMul_one (a : GF256) : gfMul a 1 = a := by
  change (if (1 : GF256).getLsbD 0 then a else 0) ^^^ mulBits 7 (xtime a) ((1 : GF256) >>> 1) = a
  have h0 : (1 : GF256).getLsbD 0 = true := rfl
  have h1 : ((1 : GF256) >>> 1) = 0 := rfl
  simp only [h0, h1, mulBits_zero_right, ite_true]
  exact BitVec.xor_zero (x := a)

private theorem mulBits_add_right (n : Nat) (a b c : GF256) :
    mulBits n a (b ^^^ c) = mulBits n a b ^^^ mulBits n a c := by
  induction n generalizing a b c with
  | zero => exact (BitVec.xor_self (x := (0 : GF256))).symm
  | succ n ih =>
    have h0 : (b ^^^ c).getLsbD 0 = (b.getLsbD 0 ^^ c.getLsbD 0) := BitVec.getLsbD_xor
    simp only [mulBits, h0, ushift1_xor, ih]
    apply BitVec.eq_of_getLsbD_eq; intro i _
    have hz : (0#8).getLsbD i = false := BitVec.getLsbD_zero
    cases b.getLsbD 0 <;> cases c.getLsbD 0 <;> dsimp <;>
      simp only [BitVec.getLsbD_xor, hz] <;>
      cases a.getLsbD i <;> cases (mulBits n (xtime a) (b >>> 1)).getLsbD i <;>
      cases (mulBits n (xtime a) (c >>> 1)).getLsbD i <;> rfl

private theorem mulBits_add_left (n : Nat) (a b c : GF256) :
    mulBits n (a ^^^ b) c = mulBits n a c ^^^ mulBits n b c := by
  induction n generalizing a b c with
  | zero => exact (BitVec.xor_self (x := (0 : GF256))).symm
  | succ n ih =>
    simp only [mulBits, xtime_add, ih]
    apply BitVec.eq_of_getLsbD_eq; intro i _
    have hz : (0#8).getLsbD i = false := BitVec.getLsbD_zero
    cases c.getLsbD 0 <;> dsimp <;>
      simp only [BitVec.getLsbD_xor, hz] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;>
      cases (mulBits n (xtime a) (c >>> 1)).getLsbD i <;>
      cases (mulBits n (xtime b) (c >>> 1)).getLsbD i <;> rfl

theorem gfMul_add_distrib (a b c : GF256) :
    gfMul a (gfAdd b c) = gfAdd (gfMul a b) (gfMul a c) := mulBits_add_right 8 a b c

private def decompAux : Nat → GF256 → GF256
  | 0, _ => 0
  | k + 1, x => (if x.getLsbD k then (1#8 <<< k) else 0) ^^^ decompAux k x

private theorem decompAux8_fin :
    ∀ i : Fin (2 ^ 8), decompAux 8 (BitVec.ofFin i) = BitVec.ofFin i := by
  decide +kernel

private theorem decompAux8_eq (x : GF256) : decompAux 8 x = x := decompAux8_fin x.toFin

private theorem linear_on_decomp (f g : GF256 → GF256)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfx : ∀ u v, f (u ^^^ v) = f u ^^^ f v)
    (hgx : ∀ u v, g (u ^^^ v) = g u ^^^ g v)
    (hb : ∀ k : Fin 8, f (1#8 <<< k.val) = g (1#8 <<< k.val)) :
    ∀ (n : Nat) (_ : n ≤ 8) (x : GF256), f (decompAux n x) = g (decompAux n x)
  | 0, _, _ => hf0.trans hg0.symm
  | k + 1, hk, x => by
    simp only [decompAux, hfx, hgx, linear_on_decomp f g hf0 hg0 hfx hgx hb k (Nat.le_of_lt hk) x]
    cases x.getLsbD k with
    | false => dsimp; change f 0 ^^^ _ = g 0 ^^^ _; rw [hf0, hg0]
    | true => dsimp; rw [hb ⟨k, hk⟩]

private theorem eq_of_linear8 (f g : GF256 → GF256)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfx : ∀ u v, f (u ^^^ v) = f u ^^^ f v)
    (hgx : ∀ u v, g (u ^^^ v) = g u ^^^ g v)
    (hb : ∀ k : Fin 8, f (1#8 <<< k.val) = g (1#8 <<< k.val)) (x : GF256) :
    f x = g x := by
  rw [← decompAux8_eq x]
  exact linear_on_decomp f g hf0 hg0 hfx hgx hb 8 (Nat.le_refl 8) x

private theorem mul_comm_basis : ∀ i j : Fin 8,
    gfMul (1#8 <<< i.val) (1#8 <<< j.val) = gfMul (1#8 <<< j.val) (1#8 <<< i.val) := by
  decide +kernel

theorem gfMul_comm (a b : GF256) : gfMul a b = gfMul b a := by
  apply eq_of_linear8 (fun x => gfMul x b) (fun x => gfMul b x)
    (mulBits_zero_left 8 b) (gfMul_zero b)
    (fun u v => mulBits_add_left 8 u v b) (fun u v => mulBits_add_right 8 b u v)
  intro i
  exact eq_of_linear8 (fun y => gfMul (1#8 <<< i.val) y) (fun y => gfMul y (1#8 <<< i.val))
    (gfMul_zero _) (mulBits_zero_left 8 _)
    (fun u v => mulBits_add_right 8 _ u v) (fun u v => mulBits_add_left 8 u v _)
    (fun j => mul_comm_basis i j) b

private theorem mul_xtime_basis : ∀ i j : Fin 8,
    gfMul (1#8 <<< i.val) (xtime (1#8 <<< j.val)) = xtime (gfMul (1#8 <<< i.val) (1#8 <<< j.val)) := by
  decide +kernel

theorem gfMul_xtime (a b : GF256) : gfMul a (xtime b) = xtime (gfMul a b) := by
  apply eq_of_linear8 (fun x => gfMul x (xtime b)) (fun x => xtime (gfMul x b))
    (mulBits_zero_left 8 _) (by change xtime (mulBits 8 0 b) = 0; rw [mulBits_zero_left 8 b, xtime_zero])
    (fun u v => mulBits_add_left 8 u v _)
    (fun u v => by change xtime (mulBits 8 (u ^^^ v) b) = _; rw [mulBits_add_left 8 u v b, xtime_add]; rfl)
  intro i
  exact eq_of_linear8 (fun y => gfMul (1#8 <<< i.val) (xtime y)) (fun y => xtime (gfMul (1#8 <<< i.val) y))
    (by rw [xtime_zero, gfMul_zero]) (by rw [gfMul_zero, xtime_zero])
    (fun u v => by rw [xtime_add]; exact mulBits_add_right 8 _ _ _)
    (fun u v => by change xtime (mulBits 8 _ (u ^^^ v)) = _; rw [mulBits_add_right 8, xtime_add]; rfl)
    (fun j => mul_xtime_basis i j) b

theorem gfMul_mulBits (a b c : GF256) (n : Nat) :
    gfMul a (mulBits n b c) = mulBits n (gfMul a b) c := by
  induction n generalizing b c with
  | zero => exact gfMul_zero a
  | succ n ih =>
    change gfMul a (gfAdd _ _) = gfAdd _ _
    rw [gfMul_add_distrib, ih, gfMul_xtime]
    cases h : c.getLsbD 0 <;> simp only [Bool.false_eq_true, ite_false, ite_true, gfMul_zero]

theorem gfMul_assoc (a b c : GF256) : gfMul (gfMul a b) c = gfMul a (gfMul b c) :=
  (gfMul_mulBits a b c 8).symm

private theorem gfMul_inv_fin : ∀ i : Fin (2 ^ 8),
    BitVec.ofFin i ≠ 0 → gfMul (BitVec.ofFin i) (gfInv (BitVec.ofFin i)) = 1 := by
  decide +kernel

theorem gfMul_inv_cancel (a : GF256) (ha : a ≠ 0) : gfMul a (gfInv a) = 1 :=
  gfMul_inv_fin a.toFin ha

@[simp] theorem gfAdd_zero_left (a : GF256) : gfAdd 0 a = a := by
  rw [gfAdd_comm, gfAdd_zero]

@[simp] theorem gfMul_zero_left (a : GF256) : gfMul 0 a = 0 := by
  rw [gfMul_comm, gfMul_zero]

@[simp] theorem gfMul_one_left (a : GF256) : gfMul 1 a = a := by
  rw [gfMul_comm, gfMul_one]

theorem gfAdd_cancel (a b : GF256) : gfAdd a (gfAdd a b) = b := by
  rw [← gfAdd_assoc, gfAdd_self_zero, gfAdd_zero_left]

theorem gfAdd_ne_zero {a b : GF256} (h : a ≠ b) : gfAdd a b ≠ 0 := by
  intro he
  have := congrArg (gfAdd a) he
  rw [gfAdd_cancel, gfAdd_zero] at this
  exact h this.symm

theorem gfMul_add_left (a b c : GF256) :
    gfMul (gfAdd a b) c = gfAdd (gfMul a c) (gfMul b c) := by
  rw [gfMul_comm, gfMul_add_distrib, gfMul_comm c a, gfMul_comm c b]

theorem gfMul_cancel_inv (a b : GF256) (ha : a ≠ 0) :
    gfMul (gfMul a b) (gfInv a) = b := by
  rw [gfMul_comm a b, gfMul_assoc, gfMul_inv_cancel a ha, gfMul_one]

theorem gfMul_eq_zero_iff (a b : GF256) : gfMul a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have hc := gfMul_cancel_inv a b ha
      rw [h, gfMul_zero_left] at hc
      exact hc.symm
  · rintro (rfl | rfl)
    · exact gfMul_zero_left b
    · exact gfMul_zero a

/-- Coefficients are stored in increasing degree order, including trailing zeros. -/
def evalPolyGF256 : List GF256 → GF256 → GF256
  | [], _ => 0
  | c :: cs, x => gfAdd c (gfMul x (evalPolyGF256 cs x))

/-- Synthetic division by X+a. The remainder is evaluation at a. -/
def quotientAt : List GF256 → GF256 → List GF256
  | [], _ => []
  | _ :: [], _ => []
  | _ :: c :: cs, a => evalPolyGF256 (c :: cs) a :: quotientAt (c :: cs) a

/-- Add y to (X+a)Q, retaining the exact coefficient-vector length. -/
def liftAt (a y : GF256) : List GF256 → List GF256
  | [] => [y]
  | q :: qs => gfAdd y (gfMul a q) :: liftAt a q qs

theorem quotientAt_length (cs : List GF256) (a : GF256) :
    (quotientAt cs a).length = cs.length - 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases cs with
    | nil => rfl
    | cons d ds => simp only [quotientAt, List.length_cons] at *; omega

theorem liftAt_eval_quotient (c : GF256) (cs : List GF256) (a : GF256) :
    liftAt a (evalPolyGF256 (c :: cs) a) (quotientAt (c :: cs) a) = c :: cs := by
  induction cs generalizing c with
  | nil => simp only [quotientAt, evalPolyGF256, liftAt, gfMul_zero, gfAdd_zero]
  | cons d ds ih =>
    simp only [quotientAt, liftAt, evalPolyGF256]
    rw [gfAdd_assoc, gfAdd_self_zero, gfAdd_zero]
    exact congrArg (List.cons c) (ih d)

theorem liftAt_eval (a y x : GF256) (qs : List GF256) :
    evalPolyGF256 (liftAt a y qs) x =
      gfAdd y (gfMul (gfAdd x a) (evalPolyGF256 qs x)) := by
  induction qs generalizing y with
  | nil => simp only [liftAt, evalPolyGF256, gfMul_zero]
  | cons q qs ih =>
    simp only [liftAt, evalPolyGF256, ih, gfMul_add_distrib, gfMul_add_left]
    have hc : gfMul x (gfMul a (evalPolyGF256 qs x)) =
        gfMul a (gfMul x (evalPolyGF256 qs x)) := by
      rw [← gfMul_assoc, gfMul_comm x a, gfMul_assoc]
    rw [hc]
    simp only [gfAdd]
    ac_rfl

theorem evalPoly_division (c : GF256) (cs : List GF256) (a x : GF256) :
    gfAdd (evalPolyGF256 (c :: cs) x) (evalPolyGF256 (c :: cs) a) =
      gfMul (gfAdd x a) (evalPolyGF256 (quotientAt (c :: cs) a) x) := by
  have he := liftAt_eval a (evalPolyGF256 (c :: cs) a) x (quotientAt (c :: cs) a)
  rw [liftAt_eval_quotient] at he
  rw [he, gfAdd_comm, gfAdd_cancel]

/-- Divided-difference interpolation. This computes the unique Lagrange polynomial
without a matrix inversion, and preserves all k coefficient slots. -/
def lagrangeInterpolatePoly : List GF256 → (GF256 → GF256) → List GF256
  | [], _ => []
  | a :: xs, f => liftAt a (f a)
      (lagrangeInterpolatePoly xs (fun x => gfMul (gfAdd (f x) (f a)) (gfInv (gfAdd x a))))

def lagrangeEvalAt (xs : List GF256) (f : GF256 → GF256) (x : GF256) : GF256 :=
  evalPolyGF256 (lagrangeInterpolatePoly xs f) x

theorem lagrangeInterpolate_congr (xs : List GF256) (f g : GF256 → GF256)
    (h : ∀ x ∈ xs, f x = g x) : lagrangeInterpolatePoly xs f = lagrangeInterpolatePoly xs g := by
  induction xs generalizing f g with
  | nil => rfl
  | cons a xs ih =>
    simp only [lagrangeInterpolatePoly]
    rw [h a (by simp)]
    congr 1
    apply ih
    intro x hx
    rw [h x (by simp [hx])]

/-- Every k distinct samples recover every coefficient of a degree-less-than-k
polynomial. No success predicate or reconstruction equation is assumed. -/
theorem lagrangeInterpolate_exact (xs coeffs : List GF256) (distinct : xs.Nodup)
    (hlen : coeffs.length = xs.length) :
    lagrangeInterpolatePoly xs (evalPolyGF256 coeffs) = coeffs := by
  induction xs generalizing coeffs with
  | nil => have hc : coeffs = [] := List.length_eq_zero_iff.mp hlen; subst hc; rfl
  | cons a xs ih =>
    cases coeffs with
    | nil => simp at hlen
    | cons c cs =>
      obtain ⟨ha, hxs⟩ := List.nodup_cons.mp distinct
      simp only [lagrangeInterpolatePoly]
      have he : lagrangeInterpolatePoly xs
          (fun x => gfMul (gfAdd (evalPolyGF256 (c :: cs) x)
            (evalPolyGF256 (c :: cs) a)) (gfInv (gfAdd x a))) =
          lagrangeInterpolatePoly xs (evalPolyGF256 (quotientAt (c :: cs) a)) := by
        apply lagrangeInterpolate_congr
        intro x hx
        rw [evalPoly_division, gfMul_cancel_inv]
        exact gfAdd_ne_zero (fun h => ha (h ▸ hx))
      rw [he, ih _ hxs (by rw [quotientAt_length]; simp only [List.length_cons] at hlen ⊢; omega)]
      exact liftAt_eval_quotient c cs a

theorem lagrangeEvalAt_exact (xs cs : List GF256) (h : xs.Nodup)
    (hl : cs.length = xs.length) (x : GF256) :
    lagrangeEvalAt xs (evalPolyGF256 cs) x = evalPolyGF256 cs x := by
  rw [lagrangeEvalAt, lagrangeInterpolate_exact xs cs h hl]

theorem liftAt_length (a y : GF256) (qs : List GF256) :
    (liftAt a y qs).length = qs.length + 1 := by
  induction qs generalizing y with
  | nil => rfl
  | cons q qs ih => simp only [liftAt, List.length_cons, ih]

theorem lagrangeInterpolate_length (xs : List GF256) (f : GF256 → GF256) :
    (lagrangeInterpolatePoly xs f).length = xs.length := by
  induction xs generalizing f with
  | nil => rfl
  | cons a xs ih => simp only [lagrangeInterpolatePoly, liftAt_length, ih, List.length_cons]

theorem gfMul_inv_middle (a b : GF256) (ha : a ≠ 0) :
    gfMul a (gfMul b (gfInv a)) = b := by
  rw [← gfMul_assoc, gfMul_cancel_inv a b ha]

/-- Interpolation agrees with arbitrary data at every selected abscissa. -/
theorem lagrangeInterpolate_samples (xs : List GF256) (f : GF256 → GF256)
    (hn : xs.Nodup) (x : GF256) (hx : x ∈ xs) :
    lagrangeEvalAt xs f x = f x := by
  induction xs generalizing f with
  | nil => cases hx
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    change evalPolyGF256 (liftAt a (f a) _) x = f x
    rw [liftAt_eval]
    rcases List.mem_cons.mp hx with he | he
    · subst x
      rw [gfAdd_self_zero, gfMul_zero_left, gfAdd_zero]
    · rw [show evalPolyGF256 (lagrangeInterpolatePoly xs _) x = _ from ih _ ht he]
      rw [gfMul_inv_middle _ _ (gfAdd_ne_zero (a := x) (b := a) (fun h => ha (h ▸ he)))]
      rw [gfAdd_comm (f x), gfAdd_cancel]

/-- A 32-byte secret, with one polynomial per byte and one abscissa per custodian. -/
abbrev Secret32 := Fin 32 → GF256
abbrev SharingPolynomial := Fin 32 → List GF256

def shamirShare (polys : SharingPolynomial) (x : GF256) : Secret32 :=
  fun i => evalPolyGF256 (polys i) x

def shamirReconstruct (xs : List GF256) (shares : GF256 → Secret32) : Secret32 :=
  fun i => lagrangeEvalAt xs (fun x => shares x i) 0

theorem shamirReconstruct_exact (xs : List GF256) (polys : SharingPolynomial)
    (hd : xs.Nodup) (hl : ∀ i, (polys i).length = xs.length) :
    shamirReconstruct xs (shamirShare polys) = shamirShare polys 0 := by
  funext i
  exact lagrangeEvalAt_exact xs (polys i) hd (hl i) 0

/-- Supply a chosen secret at zero, keeping every compromised observation fixed. -/
def secretSamples (observed : GF256 → GF256) (secret : GF256) (x : GF256) : GF256 :=
  if x = 0 then secret else observed x

def secretToLastShare (xs : List GF256) (observed : GF256 → GF256)
    (last secret : GF256) : GF256 :=
  lagrangeEvalAt (0 :: xs) (secretSamples observed secret) last

def lastShareToSecret (xs : List GF256) (observed : GF256 → GF256)
    (last y : GF256) : GF256 :=
  lagrangeEvalAt (last :: xs) (fun x => if x = last then y else observed x) 0

/-- The two interpolation coordinate systems are inverse, with no choice or randomness oracle. -/
theorem interposer_t_minus_1_information_theoretic_secrecy
    (xs : List GF256) (observed : GF256 → GF256) (last : GF256)
    (hd : xs.Nodup) (hz : 0 ∉ xs) (hl : last ∉ 0 :: xs) :
    (∀ s, lastShareToSecret xs observed last (secretToLastShare xs observed last s) = s) ∧
    (∀ y, secretToLastShare xs observed last (lastShareToSecret xs observed last y) = y) := by
  have hn0 : (0 :: xs).Nodup := List.nodup_cons.mpr ⟨hz, hd⟩
  have hnl : (last :: xs).Nodup := List.nodup_cons.mpr ⟨fun h => hl (by simp [h]), hd⟩
  constructor
  · intro s
    let p := lagrangeInterpolatePoly (0 :: xs) (secretSamples observed s)
    have hp : ∀ x ∈ last :: xs,
        (if x = last then secretToLastShare xs observed last s else observed x) =
          evalPolyGF256 p x := by
      intro x hx
      by_cases he : x = last
      · subst x; simp only [ite_true]; rfl
      · have hm : x ∈ xs := (List.mem_cons.mp hx).resolve_left he
        have hx0 : x ≠ 0 := fun e => hz (e ▸ hm)
        have hs := lagrangeInterpolate_samples (0 :: xs) (secretSamples observed s)
          hn0 x (List.mem_cons_of_mem _ hm)
        simpa only [lagrangeEvalAt, secretSamples, ite_eq_right hx0, ite_eq_right he] using hs.symm
    unfold lastShareToSecret lagrangeEvalAt
    rw [lagrangeInterpolate_congr _ _ _ hp,
      lagrangeInterpolate_exact _ p hnl (by simp only [p, lagrangeInterpolate_length, List.length_cons])]
    exact lagrangeInterpolate_samples (0 :: xs) (secretSamples observed s) hn0 0 (by simp)
  · intro y
    let f := fun x => if x = last then y else observed x
    let p := lagrangeInterpolatePoly (last :: xs) f
    have hp : ∀ x ∈ 0 :: xs,
        secretSamples observed (lastShareToSecret xs observed last y) x = evalPolyGF256 p x := by
      intro x hx
      by_cases he : x = 0
      · subst x; rfl
      · have hm : x ∈ xs := (List.mem_cons.mp hx).resolve_left he
        have hxl : x ≠ last := fun e => hl (List.mem_cons_of_mem _ (e ▸ hm))
        have hs := lagrangeInterpolate_samples (last :: xs) f hnl x (List.mem_cons_of_mem _ hm)
        simpa only [lagrangeEvalAt, secretSamples, f, ite_eq_right he, ite_eq_right hxl] using hs.symm
    unfold secretToLastShare lagrangeEvalAt
    rw [lagrangeInterpolate_congr _ _ _ hp,
      lagrangeInterpolate_exact _ p hn0 (by simp only [p, lagrangeInterpolate_length, List.length_cons])]
    have hs := lagrangeInterpolate_samples (last :: xs) f hnl last (by simp)
    simpa only [f, lagrangeEvalAt, ite_true] using hs

/-- Full-width cSHAKE commitments, including a size proof in their carrier. -/
abbrev Digest256 := { b : ByteArray // b.size = 32 }

instance : DecidableEq Digest256 := fun a b =>
  if h : a.val = b.val then isTrue (Subtype.ext h)
  else isFalse (fun e => h (congrArg Subtype.val e))

instance : BEq Digest256 := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Digest256 where
  eq_of_beq := of_decide_eq_true
  rfl := by intro a; exact decide_eq_true rfl

def hash256 (domain : String) (b : ByteArray) : Digest256 :=
  ⟨Lsafe.cshakeHasher.hash domain b, Lsafe.cshakeHasher.size_eq domain b⟩

structure CshakeCollision where
  domain : String
  collision : Lsafe.HashCollision Lsafe.cshakeHasher domain

open ChunkedWorld

def cDigest256 : FastCodec Digest256 :=
  cMap (fun d => d.val.data.toList)
    (fun bs => if h : bs.length = 32 then some ⟨⟨bs.toArray⟩, by simpa [ByteArray.size] using h⟩ else none)
    (by
      intro d
      have h : d.val.data.toList.length = 32 := by
        simpa only [Array.length_toList, ByteArray.size] using d.property
      simp only [h, dite_true, Array.toArray_toList]) cBytes

/-- Canonical world bytes include every page, tombstone and non-store field. -/
def cWorld : FastCodec World :=
  cMap (fun w => (w.store.pages, w.store.tombs, metaOf w))
    (fun (ps, ts, m) => some (withMeta ps ts m))
    (fun w => congrArg some (withMeta_metaOf w))
    (cPair (cList cPage) (cPair (cList cPage) cNonStoreMeta))

/-- Byte payload plus a sibling path. The position is supplied by the verifier. -/
structure MerkleOpening where
  bytes : ByteArray
  siblings : List ByteArray
  deriving DecidableEq

def merkleLeaf (bytes : ByteArray) : Digest256 := hash256 "obend.por.leaf.v1" bytes

def verifyMerkleOpening (root : Digest256) (depth index : Nat) (p : MerkleOpening) : Bool :=
  decide (index < 2 ^ depth) && decide (p.siblings.length = depth) &&
    p.siblings.all (fun b => decide (b.size = 32)) &&
    decide (hash256 "obend.por.root.v1"
      (Lsafe.climb Lsafe.cshakeHasher index (merkleLeaf p.bytes).val p.siblings) = root)

theorem verifyMerkleOpening_parts (root : Digest256) (depth index : Nat) (p : MerkleOpening)
    (h : verifyMerkleOpening root depth index p = true) :
    index < 2 ^ depth ∧ p.siblings.length = depth ∧
      (∀ b ∈ p.siblings, b.size = 32) ∧
      hash256 "obend.por.root.v1"
        (Lsafe.climb Lsafe.cshakeHasher index (merkleLeaf p.bytes).val p.siblings) = root := by
  simp only [verifyMerkleOpening, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Opening soundness is computational: the alternative contains explicit unequal messages. -/
def merkleOpening_binding (root : Digest256) (depth index : Nat) (a b : MerkleOpening)
    (ha : verifyMerkleOpening root depth index a = true)
    (hb : verifyMerkleOpening root depth index b = true) : PSum (a.bytes = b.bytes) CshakeCollision :=
  if he : a.bytes = b.bytes then .inl he else
  if hc : Lsafe.climb Lsafe.cshakeHasher index (merkleLeaf a.bytes).val a.siblings =
      Lsafe.climb Lsafe.cshakeHasher index (merkleLeaf b.bytes).val b.siblings then
    if hh : (merkleLeaf a.bytes).val = (merkleLeaf b.bytes).val then
      .inr ⟨"obend.por.leaf.v1", ⟨a.bytes, b.bytes, he, hh⟩⟩
    else
      .inr ⟨Lsafe.merkleTag, Lsafe.climbCollision Lsafe.cshakeHasher index
        (merkleLeaf a.bytes).val (merkleLeaf b.bytes).val a.siblings b.siblings
        (merkleLeaf a.bytes).property (merkleLeaf b.bytes).property
        (verifyMerkleOpening_parts root depth index a ha).2.2.1
        (verifyMerkleOpening_parts root depth index b hb).2.2.1
        ((verifyMerkleOpening_parts root depth index a ha).2.1.trans
          (verifyMerkleOpening_parts root depth index b hb).2.1.symm) hh hc⟩
  else .inr ⟨"obend.por.root.v1", ⟨_, _, hc,
    congrArg Subtype.val ((verifyMerkleOpening_parts root depth index a ha).2.2.2.trans
      (verifyMerkleOpening_parts root depth index b hb).2.2.2.symm)⟩⟩

structure ShardHeader where
  shardIndex : Nat
  xCoord : GF256
  payloadSize : Nat
  payloadDigest : Digest256
  blockDepth : Nat
  blockRoot : Digest256
  deriving DecidableEq

def cGF256 : FastCodec GF256 :=
  cMap (fun x => x.toNat.toUInt8) (fun b => some (BitVec.ofNat 8 b.toNat))
    (by intro x; congr 1; apply BitVec.eq_of_toNat_eq; simp only [UInt8.toNat_ofNat',
      BitVec.toNat_ofNat]; omega) cUInt8

def cShardHeader : FastCodec ShardHeader :=
  cMap (fun s => (s.shardIndex, s.xCoord, s.payloadSize, s.payloadDigest, s.blockDepth, s.blockRoot))
    (fun (i, x, n, h, d, r) => some ⟨i, x, n, h, d, r⟩)
    (by intro s; cases s; rfl)
    (cPair cNat (cPair cGF256 (cPair cNat (cPair cDigest256 (cPair cNat cDigest256)))))

structure PorResponse where
  header : ShardHeader
  shardSiblings : List ByteArray
  block : MerkleOpening
  deriving DecidableEq

/-- Both inclusion proofs are required. A shard digest alone is not a retrievability response. -/
def verifyPorResponse (root : Digest256) (shardDepth shardIndex blockIndex : Nat)
    (p : PorResponse) : Bool :=
  decide (p.header.shardIndex = shardIndex) && decide (blockIndex < p.header.payloadSize) &&
    verifyMerkleOpening root shardDepth shardIndex
      ⟨cShardHeader.encodeArray p.header, p.shardSiblings⟩ &&
    verifyMerkleOpening p.header.blockRoot p.header.blockDepth blockIndex p.block

theorem header_encoding_injective (a b : ShardHeader)
    (h : cShardHeader.encodeArray a = cShardHeader.encodeArray b) : a = b := by
  have he := congrArg (fun ba => cShardHeader.decodeExact ba.data.toList) h
  rw [FastCodec.encodeArray_eq, FastCodec.encodeArray_eq,
    FastCodec.decodeExact_enc, FastCodec.decodeExact_enc] at he
  exact Option.some.inj he

/-- Every accepted response equals the authentic challenged block, or gives a collision
at one of the two Merkle levels. The authentic opening is independent of the response. -/
def verifyPorChallenge_sound_or_collision (root : Digest256) (depth i j : Nat)
    (response authentic : PorResponse)
    (hr : verifyPorResponse root depth i j response = true)
    (ha : verifyPorResponse root depth i j authentic = true) :
    PSum (response.header = authentic.header ∧ response.block.bytes = authentic.block.bytes)
      CshakeCollision := by
  have rp := hr
  have ap := ha
  simp only [verifyPorResponse, Bool.and_eq_true] at rp ap
  match merkleOpening_binding root depth i
      ⟨cShardHeader.encodeArray response.header, response.shardSiblings⟩
      ⟨cShardHeader.encodeArray authentic.header, authentic.shardSiblings⟩ rp.1.2 ap.1.2 with
  | .inr collision => exact .inr collision
  | .inl he =>
    have hh := header_encoding_injective _ _ he
    have hb : verifyMerkleOpening response.header.blockRoot response.header.blockDepth j authentic.block = true :=
      hh.symm ▸ ap.2
    match merkleOpening_binding response.header.blockRoot response.header.blockDepth j
        response.block authentic.block rp.2 hb with
    | .inr collision => exact .inr collision
    | .inl he => exact .inl ⟨hh, he⟩

/-- Deterministic transcript-derived coordinates. The counting bound below does not
assert that this deterministic map is a uniform random oracle. -/
def derivePorChallenge (root seed : Digest256) (epoch n blocks : Nat) : Nat × Nat :=
  let bytes := (hash256 "obend.por.challenge.v1"
    ((cPair cDigest256 (cPair cDigest256 cNat)).encodeArray (root, seed, epoch))).val.data.toList
  (Obend.Digest.HashBytes.ofBE (bytes.take 16) % n,
   Obend.Digest.HashBytes.ofBE (bytes.drop 16) % blocks)

/-- The finite sample space of q independent coordinates, with repetitions allowed. -/
def challengeTuples (positions : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | q + 1 => positions.flatMap fun i => (challengeTuples positions q).map (i :: ·)

theorem challengeTuples_length (positions : List Nat) (q : Nat) :
    (challengeTuples positions q).length = positions.length ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [challengeTuples, List.length_flatMap, List.length_map, ih]
    simp only [List.map_const', List.sum_replicate_nat, Nat.pow_succ, Nat.mul_comm]

/-- Exact counting, hence also an upper bound: a deleted shard removes one position. -/
theorem lazyHost_evasion_bound (n : Nat) (dropped : List Nat)
    (hd : dropped.Nodup) (hr : ∀ i ∈ dropped, i < n) (q : Nat) :
    let survivors := (List.range n).filter (fun i => !dropped.contains i)
    survivors.length = n - dropped.length ∧
      (challengeTuples survivors q).length = (n - dropped.length) ^ q ∧
      (challengeTuples (List.range n) q).length = n ^ q := by
  dsimp only
  have hsub : dropped ⊆ List.range n := fun i hi => List.mem_range.mpr (hr i hi)
  have heq : ((List.range n).filter (fun i => dropped.contains i)).Perm dropped := by
    apply (List.perm_ext_iff_of_nodup (List.Pairwise.filter _ (List.nodup_range (n := n))) hd).mpr
    intro i
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have partition (l : List Nat) : (l.filter (fun i => dropped.contains i)).length +
      (l.filter (fun i => !dropped.contains i)).length = l.length := by
    induction l with
    | nil => rfl
    | cons x xs ih => cases hx : dropped.contains x <;> simp only [List.filter_cons, hx, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, List.length_cons] <;> omega
  have hlen := partition (List.range n)
  have hs : ((List.range n).filter (fun i => !dropped.contains i)).length = n - dropped.length := by
    have hp := heq.length_eq
    simp only [List.length_range] at hlen
    omega
  exact ⟨hs, by rw [challengeTuples_length, hs], by rw [challengeTuples_length, List.length_range]⟩

def byteGF (b : UInt8) : GF256 := BitVec.ofNat 8 b.toNat

def gfByte (b : GF256) : UInt8 := b.toNat.toUInt8

@[simp] theorem byteGF_gfByte (b : GF256) : byteGF (gfByte b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [byteGF, gfByte, BitVec.toNat_ofNat, UInt8.toNat_ofNat']
  have := b.isLt
  omega

@[simp] theorem gfByte_byteGF (b : UInt8) : gfByte (byteGF b) = b := by
  apply UInt8.toNat_inj.mp
  simp only [byteGF, gfByte, BitVec.toNat_ofNat, UInt8.toNat_ofNat']
  have := b.toNat_lt
  omega

def systematicPoints (k : Nat) : List GF256 := (List.range k).map (BitVec.ofNat 8)

theorem systematicPoints_length (k : Nat) : (systematicPoints k).length = k := by
  simp only [systematicPoints, List.length_map, List.length_range]

theorem systematicPoints_nodup (k : Nat) (hk : k ≤ 256) : (systematicPoints k).Nodup := by
  unfold systematicPoints
  rw [List.Nodup, List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := k))
  intro a b ha hb hab he
  have hea := congrArg BitVec.toNat he
  have hla := List.mem_range.mp ha
  have hlb := List.mem_range.mp hb
  simp only [BitVec.toNat_ofNat] at hea
  apply hab
  omega

/-- Each stripe consists of k consecutive encrypted message bytes. Padding is zero. -/
def stripeSamples (bytes : List UInt8) (k column : Nat) (x : GF256) : GF256 :=
  byteGF (bytes.getD (column * k + x.toNat) 0)

def stripePolynomial (bytes : List UInt8) (k column : Nat) : List GF256 :=
  lagrangeInterpolatePoly (systematicPoints k) (stripeSamples bytes k column)

def shardWidth (len k : Nat) : Nat := (len + k - 1) / k

def encodeShardBytes (bytes : List UInt8) (k : Nat) (x : GF256) : ByteArray :=
  ⟨((List.range (shardWidth bytes.length k)).map fun col =>
    gfByte (evalPolyGF256 (stripePolynomial bytes k col) x)).toArray⟩

/-- Recover in original message order, dropping the equal-size shard padding. -/
def recoverShardBytes (k len : Nat) (xs : List GF256) (shards : GF256 → ByteArray) : List UInt8 :=
  (List.range len).map fun i => gfByte (lagrangeEvalAt xs
    (fun x => byteGF ((shards x).data.toList.getD (i / k) 0)) (BitVec.ofNat 8 (i % k)))

theorem shardWidth_bound (len k i : Nat) (hk : 0 < k) (hi : i < len) :
    i / k < shardWidth len k := by
  unfold shardWidth
  apply (Nat.le_div_iff_mul_le hk).mpr
  have hd := Nat.div_mul_le_self i k
  rw [Nat.succ_mul]
  omega

theorem encodeShardBytes_at (bytes : List UInt8) (k col : Nat) (x : GF256)
    (hc : col < shardWidth bytes.length k) :
    byteGF ((encodeShardBytes bytes k x).data.toList.getD col 0) =
      evalPolyGF256 (stripePolynomial bytes k col) x := by
  simp only [encodeShardBytes, List.toList_toArray]
  have hi : col < ((List.range (shardWidth bytes.length k)).map fun col =>
      gfByte (evalPolyGF256 (stripePolynomial bytes k col) x)).length := by
    simpa only [List.length_map, List.length_range] using hc
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem_map, List.getElem_range, byteGF_gfByte]

/-- Any k distinct evaluation shards recover the original bytes, with no erasure pattern fixed. -/
theorem recoverShardBytes_exact (bytes : List UInt8) (k : Nat) (xs : List GF256)
    (hk : 0 < k) (hmax : k ≤ 256) (hx : xs.Nodup) (hlen : xs.length = k) :
    recoverShardBytes k bytes.length xs (encodeShardBytes bytes k) = bytes := by
  apply List.ext_getElem
  · simp only [recoverShardBytes, List.length_map, List.length_range]
  · intro i hi hj
    simp only [recoverShardBytes, List.getElem_map, List.getElem_range]
    have hc := shardWidth_bound bytes.length k i hk hj
    have hs : (fun x => byteGF ((encodeShardBytes bytes k x).data.toList.getD (i / k) 0)) =
        evalPolyGF256 (stripePolynomial bytes k (i / k)) := by
      funext x; exact encodeShardBytes_at bytes k (i / k) x hc
    rw [hs, lagrangeEvalAt_exact xs _ hx (by
      rw [stripePolynomial, lagrangeInterpolate_length, systematicPoints_length, hlen])]
    have hm : BitVec.ofNat 8 (i % k) ∈ systematicPoints k := by
      exact List.mem_map.mpr ⟨i % k, List.mem_range.mpr (Nat.mod_lt i hk), rfl⟩
    rw [show evalPolyGF256 (stripePolynomial bytes k (i / k)) (BitVec.ofNat 8 (i % k)) =
        stripeSamples bytes k (i / k) (BitVec.ofNat 8 (i % k)) from
      lagrangeInterpolate_samples _ _ (systematicPoints_nodup k hmax) _ hm]
    have hn : (BitVec.ofNat 8 (i % k)).toNat = i % k := by
      simp only [BitVec.toNat_ofNat]
      have := Nat.mod_lt i hk
      omega
    simp only [stripeSamples, hn, gfByte_byteGF]
    have he : i / k * k + i % k = i := by simpa only [Nat.mul_comm] using Nat.div_add_mod i k
    rw [he]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- cSHAKE keystream blocks absorb the 32-byte root, snapshot salt and block counter. -/
def keystreamByte (root salt : Digest256) (offset : Nat) : UInt8 :=
  ((hash256 "obend.fire.stream.v1"
    ((cPair cDigest256 (cPair cDigest256 cNat)).encodeArray (root, salt, offset / 32))).val.data.toList).getD
      (offset % 32) 0

def cryptFrom (root salt : Digest256) : Nat → List UInt8 → List UInt8
  | _, [] => []
  | offset, b :: bs => (b ^^^ keystreamByte root salt offset) :: cryptFrom root salt (offset + 1) bs

theorem cryptFrom_involution (root salt : Digest256) (offset : Nat) (bytes : List UInt8) :
    cryptFrom root salt offset (cryptFrom root salt offset bytes) = bytes := by
  induction bytes generalizing offset with
  | nil => rfl
  | cons b bs ih =>
    simp only [cryptFrom, ih]
    congr 1
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
    cases b.toBitVec.getLsbD i <;> cases (keystreamByte root salt offset).toBitVec.getLsbD i <;> rfl

theorem cryptFrom_length (root salt : Digest256) (offset : Nat) (bytes : List UInt8) :
    (cryptFrom root salt offset bytes).length = bytes.length := by
  induction bytes generalizing offset with
  | nil => rfl
  | cons b bs ih => simp only [cryptFrom, List.length_cons, ih]

/-- The encrypted stream includes a prefix-free length header around canonical world bytes. -/
def encryptWorld (root salt : Digest256) (w : World) : List UInt8 :=
  cryptFrom root salt 0 (cBytes.enc (cWorld.enc w))

def decryptWorld (root salt : Digest256) (bytes : List UInt8) : Option World := do
  let payload ← cBytes.decodeExact (cryptFrom root salt 0 bytes)
  cWorld.decodeExact payload

theorem decryptWorld_encryptWorld (root salt : Digest256) (w : World) :
    decryptWorld root salt (encryptWorld root salt w) = some w := by
  simp only [decryptWorld, encryptWorld, cryptFrom_involution, FastCodec.decodeExact_enc,
    bind, Option.bind]

/-- The byte decoder's end-to-end equation for authentic shards; Merkle admission is separate. -/
def decodeWorldShards (root salt : Digest256) (k len : Nat)
    (xs : List GF256) (shards : GF256 → ByteArray) : Option World :=
  decryptWorld root salt (recoverShardBytes k len xs shards)

theorem resurrectWorldFromAuthenticShards_exact (root salt : Digest256) (w : World)
    (k : Nat) (xs : List GF256) (hk : 0 < k) (hmax : k ≤ 256)
    (hx : xs.Nodup) (hlen : xs.length = k) :
    decodeWorldShards root salt k (encryptWorld root salt w).length xs
      (encodeShardBytes (encryptWorld root salt w) k) = some w := by
  rw [decodeWorldShards, recoverShardBytes_exact _ k xs hk hmax hx hlen,
    decryptWorld_encryptWorld]

/-- A vault transfer consumes a mandate allowance and conserves the two escrow balances. -/
structure CustodyBalances where
  source : Nat
  destination : Nat
  allowance : Nat
  deriving DecidableEq, Repr

/-- Custody of one vault under one mandate: both identifiers are full-width and fixed for the
whole receipt chain. -/
structure CustodyState where
  vaultId : Digest256
  mandateId : Digest256
  balances : CustodyBalances
  epoch : Nat
  receiptHead : Digest256
  deriving DecidableEq

structure VaultTransitionReceipt where
  vaultId : Digest256
  mandateId : Digest256
  previous : Digest256
  epoch : Nat
  amount : Nat
  after : CustodyBalances
  commitment : Digest256
  deriving DecidableEq

def cCustodyBalances : FastCodec CustodyBalances :=
  cMap (fun b => (b.source, b.destination, b.allowance))
    (fun (s, d, a) => some ⟨s, d, a⟩) (by intro b; cases b; rfl)
    (cPair cNat (cPair cNat cNat))

/-- Everything a receipt commits to: vault, mandate, chain link, epoch, amount, resulting balances. -/
abbrev TransitionPayload := Digest256 × Digest256 × Digest256 × Nat × Nat × CustodyBalances

def VaultTransitionReceipt.payload (r : VaultTransitionReceipt) : TransitionPayload :=
  (r.vaultId, r.mandateId, r.previous, r.epoch, r.amount, r.after)

/-- Each identifier and digest is length-framed by `cDigest256`; naturals are self-delimiting. -/
def cTransitionPayload : FastCodec TransitionPayload :=
  cPair cDigest256 (cPair cDigest256 (cPair cDigest256 (cPair cNat (cPair cNat cCustodyBalances))))

def transitionTag : String := "obend.custody.transition.v2"

def transitionCommitment (r : VaultTransitionReceipt) : Digest256 :=
  hash256 transitionTag (cTransitionPayload.encodeArray r.payload)

/-- Equal transition commitments carry the same vault, mandate, chain link, epoch, amount and
balances, or the two payload encodings are an explicit cSHAKE collision. -/
def transitionCommitment_binding (a b : VaultTransitionReceipt)
    (h : transitionCommitment a = transitionCommitment b) :
    PSum (a.payload = b.payload) CshakeCollision :=
  if he : cTransitionPayload.encodeArray a.payload = cTransitionPayload.encodeArray b.payload then
    .inl (by
      have hd := congrArg (fun ba => cTransitionPayload.decodeExact ba.data.toList) he
      rw [FastCodec.encodeArray_eq, FastCodec.encodeArray_eq,
        FastCodec.decodeExact_enc, FastCodec.decodeExact_enc] at hd
      exact Option.some.inj hd)
  else .inr ⟨transitionTag, ⟨_, _, he, congrArg Subtype.val h⟩⟩

/-- Independent transfer semantics, with ordinary integer conservation equations. -/
def ValidVaultTransition (before : CustodyBalances) (amount : Nat) (after : CustodyBalances) : Prop :=
  after.source + amount = before.source ∧ after.destination = before.destination + amount ∧
    after.allowance + amount = before.allowance

instance (before after : CustodyBalances) (amount : Nat) :
    Decidable (ValidVaultTransition before amount after) := inferInstanceAs
    (Decidable (after.source + amount = before.source ∧
      after.destination = before.destination + amount ∧ after.allowance + amount = before.allowance))

/-- Compute the proposed transfer independently, then compare the entire result and receipt chain. -/
def checkKernelTransitionReceipt (state : CustodyState) (r : VaultTransitionReceipt) : Bool :=
  decide (r.amount ≤ state.balances.source) && decide (r.amount ≤ state.balances.allowance) &&
    decide (r.after = ⟨state.balances.source - r.amount,
      state.balances.destination + r.amount, state.balances.allowance - r.amount⟩) &&
    decide (r.previous = state.receiptHead) && decide (r.epoch = state.epoch + 1) &&
    decide (r.commitment = transitionCommitment r) &&
    decide (r.vaultId = state.vaultId) && decide (r.mandateId = state.mandateId)

theorem checkKernelTransitionReceipt_sound (state : CustodyState) (r : VaultTransitionReceipt)
    (h : checkKernelTransitionReceipt state r = true) :
    ValidVaultTransition state.balances r.amount r.after ∧ r.previous = state.receiptHead ∧
      r.epoch = state.epoch + 1 ∧ r.commitment = transitionCommitment r ∧
      r.vaultId = state.vaultId ∧ r.mandateId = state.mandateId := by
  simp only [checkKernelTransitionReceipt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, ha⟩, he⟩, hp⟩, ht⟩, hc⟩, hv⟩, hm⟩ := h
  refine ⟨?_, hp, ht, hc, hv, hm⟩
  unfold ValidVaultTransition
  rw [he]
  exact ⟨Nat.sub_add_cancel hs, rfl, Nat.sub_add_cancel ha⟩

/-- A receipt issued under another vault or another mandate is refused, whatever else it says. -/
theorem checkKernelTransitionReceipt_refuses_foreign (state : CustodyState)
    (r : VaultTransitionReceipt) (h : r.vaultId ≠ state.vaultId ∨ r.mandateId ≠ state.mandateId) :
    checkKernelTransitionReceipt state r = false := by
  cases hc : checkKernelTransitionReceipt state r with
  | false => rfl
  | true =>
    obtain ⟨_, _, _, _, hv, hm⟩ := checkKernelTransitionReceipt_sound state r hc
    exact absurd h (by simp [hv, hm])

/-- **Receipt binding over `(vaultId, mandateId, …)`.** One receipt commitment accepted by two
custody states names one vault, one mandate, one chain position and one transfer, or exhibits an
explicit cSHAKE collision. A receipt cannot be replayed into a different vault or mandate. -/
def acceptedReceipt_binding (sa sb : CustodyState) (a b : VaultTransitionReceipt)
    (ha : checkKernelTransitionReceipt sa a = true) (hb : checkKernelTransitionReceipt sb b = true)
    (h : a.commitment = b.commitment) :
    PSum (a = b ∧ sa.vaultId = sb.vaultId ∧ sa.mandateId = sb.mandateId ∧
      sa.receiptHead = sb.receiptHead ∧ sa.epoch = sb.epoch) CshakeCollision :=
  have pa := checkKernelTransitionReceipt_sound sa a ha
  have pb := checkKernelTransitionReceipt_sound sb b hb
  match transitionCommitment_binding a b (pa.2.2.2.1 ▸ pb.2.2.2.1 ▸ h) with
  | .inr collision => .inr collision
  | .inl hp => .inl (by
      simp only [VaultTransitionReceipt.payload, Prod.mk.injEq] at hp
      obtain ⟨hv, hm, hprev, he, hamt, haft⟩ := hp
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · cases a; cases b
        dsimp only at hv hm hprev he hamt haft h
        subst hv hm hprev he hamt haft h; rfl
      · rw [← pa.2.2.2.2.1, ← pb.2.2.2.2.1, hv]
      · rw [← pa.2.2.2.2.2, ← pb.2.2.2.2.2, hm]
      · rw [← pa.2.1, ← pb.2.1, hprev]
      · have h1 := pa.2.2.1; have h2 := pb.2.2.1; omega)

/-- Enclave quotes, including forged quotes after key compromise, do not grant admission. -/
structure CustodyTurn where
  receipt : VaultTransitionReceipt
  enclaveQuotes : List Digest256
  deriving DecidableEq

def admitCustodyTurn (state : CustodyState) (turn : CustodyTurn) : Option CustodyState :=
  if checkKernelTransitionReceipt state turn.receipt then
    some ⟨state.vaultId, state.mandateId, turn.receipt.after, turn.receipt.epoch,
      turn.receipt.commitment⟩ else none

inductive ValidCustodyTrace : CustodyState → List CustodyTurn → CustodyState → Prop where
  | nil (state) : ValidCustodyTrace state [] state
  | cons {state next final turn turns}
      (step : admitCustodyTurn state turn = some next)
      (tail : ValidCustodyTrace next turns final) : ValidCustodyTrace state (turn :: turns) final

def invalidTransitionCount (state : CustodyState) : List CustodyTurn → Nat
  | [] => 0
  | turn :: turns =>
    (if ValidVaultTransition state.balances turn.receipt.amount turn.receipt.after then 0 else 1) +
      invalidTransitionCount ⟨state.vaultId, state.mandateId, turn.receipt.after,
        turn.receipt.epoch, turn.receipt.commitment⟩ turns

/-- Across arbitrary accumulated states and arbitrary quotes, every admitted transfer is valid. -/
theorem enclave_compromise_admits_zero_invalid_transitions
    (state final : CustodyState) (turns : List CustodyTurn)
    (h : ValidCustodyTrace state turns final) :
    invalidTransitionCount state turns = 0 ∧
      final.balances.source + final.balances.destination =
        state.balances.source + state.balances.destination ∧
      final.balances.allowance ≤ state.balances.allowance := by
  induction h with
  | nil => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | @cons state next final turn turns step tail ih =>
    unfold admitCustodyTurn at step
    split at step
    · rename_i hc
      cases step
      obtain ⟨⟨hs, hd, ha⟩, _, _, _⟩ := checkKernelTransitionReceipt_sound state turn.receipt hc
      have hv : ValidVaultTransition state.balances turn.receipt.amount turn.receipt.after := ⟨hs, hd, ha⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [invalidTransitionCount, ite_eq_left hv, Nat.zero_add]
        exact ih.1
      · dsimp only at ih
        omega
      · dsimp only at ih
        omega
    · contradiction

/-- Across any accumulated custody trace the vault and mandate never change, and every admitted
receipt in the trace was issued under exactly that vault and that mandate. -/
theorem validCustodyTrace_binds_vault_and_mandate (state final : CustodyState)
    (turns : List CustodyTurn) (h : ValidCustodyTrace state turns final) :
    final.vaultId = state.vaultId ∧ final.mandateId = state.mandateId ∧
      ∀ turn ∈ turns, turn.receipt.vaultId = state.vaultId ∧
        turn.receipt.mandateId = state.mandateId := by
  induction h with
  | nil => exact ⟨rfl, rfl, fun _ hm => nomatch hm⟩
  | @cons state next final turn turns step tail ih =>
    unfold admitCustodyTurn at step
    split at step
    · rename_i hc
      cases step
      obtain ⟨_, _, _, _, hv, hm⟩ := checkKernelTransitionReceipt_sound state turn.receipt hc
      refine ⟨ih.1, ih.2.1, ?_⟩
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht'
      · exact ⟨hv, hm⟩
      · exact ih.2.2 t ht'
    · contradiction

def treeLeaves (messages : List ByteArray) : List ByteArray := messages.map (fun b => (merkleLeaf b).val)

def treeRoot (depth : Nat) (messages : List ByteArray) : Digest256 :=
  hash256 "obend.por.root.v1" (Lsafe.rootOf Lsafe.cshakeHasher depth (treeLeaves messages))

def treeOpening (depth : Nat) (messages : List ByteArray) (index : Nat) : MerkleOpening :=
  ⟨messages.getD index ByteArray.empty, Lsafe.pathOf Lsafe.cshakeHasher depth (treeLeaves messages) index⟩

theorem treeOpening_verified (depth : Nat) (messages : List ByteArray) (index : Nat)
    (hl : messages.length = 2 ^ depth) (hi : index < messages.length) :
    verifyMerkleOpening (treeRoot depth messages) depth index (treeOpening depth messages index) = true := by
  have hleaflen : (treeLeaves messages).length = 2 ^ depth := by
    simp only [treeLeaves, List.length_map, hl]
  have hall : ∀ b ∈ treeLeaves messages, b.size = 32 := by
    intro b hb
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb
    exact (merkleLeaf m).property
  have hlidx : index < (treeLeaves messages).length := by
    simp only [treeLeaves, List.length_map]; exact hi
  have he : (treeLeaves messages).getD index ByteArray.empty =
      (merkleLeaf (messages.getD index ByteArray.empty)).val := by
    rw [Lsafe.getD_of_lt hlidx, Lsafe.getD_of_lt hi]
    simp only [treeLeaves, List.getElem_map]
  have hc := Lsafe.climb_pathOf Lsafe.cshakeHasher depth (treeLeaves messages) index hleaflen (hl ▸ hi)
  rw [he] at hc
  have hs := Lsafe.pathOf_size Lsafe.cshakeHasher depth (treeLeaves messages) index hleaflen (hl ▸ hi) hall
  exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
    ⟨(Bool.and_eq_true _ _).mpr ⟨decide_eq_true (hl ▸ hi), decide_eq_true (Lsafe.pathOf_length _ _ _ _)⟩,
      List.all_eq_true.mpr (fun b hb => decide_eq_true (hs b hb))⟩,
    decide_eq_true (congrArg (hash256 "obend.por.root.v1") hc)⟩

/-- Byte-block trees are padded to the next power of two. Empty padding is never challenged. -/
def blockMessages (bytes : ByteArray) (depth : Nat) : List ByteArray :=
  (List.range (2 ^ depth)).map fun i =>
    if h : i < bytes.size then ⟨#[bytes[i]'h]⟩ else ByteArray.empty

def makeShardHeader (bytes : ByteArray) (x : GF256) : ShardHeader :=
  let depth := bytes.size.log2 + 1
  ⟨x.toNat, x, bytes.size, hash256 "obend.fire.payload.v1" bytes, depth,
    treeRoot depth (blockMessages bytes depth)⟩

structure ShardData where
  header : ShardHeader
  bytes : ByteArray
  siblings : List ByteArray
  deriving DecidableEq

def verifyShardData (root : Digest256) (x : GF256) (s : ShardData) : Bool :=
  decide (s.header.xCoord = x) && decide (s.header.shardIndex = x.toNat) &&
    decide (s.header.payloadSize = s.bytes.size) &&
    decide (s.header.payloadDigest = hash256 "obend.fire.payload.v1" s.bytes) &&
    verifyMerkleOpening root 8 x.toNat ⟨cShardHeader.encodeArray s.header, s.siblings⟩

def shardData_binding (root : Digest256) (x : GF256) (a b : ShardData)
    (ha : verifyShardData root x a = true) (hb : verifyShardData root x b = true) :
    PSum (a.bytes = b.bytes) CshakeCollision := by
  have pa := ha
  have pb := hb
  simp only [verifyShardData, Bool.and_eq_true, decide_eq_true_eq] at pa pb
  match merkleOpening_binding root 8 x.toNat
      ⟨cShardHeader.encodeArray a.header, a.siblings⟩
      ⟨cShardHeader.encodeArray b.header, b.siblings⟩ pa.2 pb.2 with
  | .inr c => exact .inr c
  | .inl he =>
    have hh := header_encoding_injective a.header b.header he
    if eqBytes : a.bytes = b.bytes then exact .inl eqBytes
    else
      exact .inr ⟨"obend.fire.payload.v1", ⟨a.bytes, b.bytes, eqBytes,
        congrArg Subtype.val (pa.1.2.symm.trans ((congrArg ShardHeader.payloadDigest hh).trans pb.1.2))⟩⟩

/-- The n actual shards occupy the first n leaves; the remaining leaves are domain-framed padding. -/
def fireMessages (bytes : List UInt8) (k n : Nat) : List ByteArray :=
  (List.range 256).map fun i => if i < n then
    cShardHeader.encodeArray (makeShardHeader (encodeShardBytes bytes k (BitVec.ofNat 8 i)) (BitVec.ofNat 8 i))
    else ByteArray.empty

def shardTreeRoot (bytes : List UInt8) (k n : Nat) : Digest256 := treeRoot 8 (fireMessages bytes k n)

def authenticatedShard (bytes : List UInt8) (k n : Nat) (x : GF256) : ShardData :=
  let payload := encodeShardBytes bytes k x
  ⟨makeShardHeader payload x, payload,
    (treeOpening 8 (fireMessages bytes k n) x.toNat).siblings⟩

theorem authenticatedShard_verified (bytes : List UInt8) (k n : Nat) (x : GF256)
    (hx : x.toNat < n) :
    verifyShardData (shardTreeRoot bytes k n) x (authenticatedShard bytes k n x) = true := by
  have hl : (fireMessages bytes k n).length = 2 ^ 8 := by
    simp only [fireMessages, List.length_map, List.length_range]
  have hi : x.toNat < (fireMessages bytes k n).length := by
    rw [hl]; exact x.isLt
  have hop := treeOpening_verified 8 (fireMessages bytes k n) x.toNat hl hi
  have hm : (fireMessages bytes k n).getD x.toNat ByteArray.empty =
      cShardHeader.encodeArray (makeShardHeader (encodeShardBytes bytes k x) x) := by
    rw [Lsafe.getD_of_lt hi]
    simp only [fireMessages, List.getElem_map, List.getElem_range, ite_eq_left hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change verifyMerkleOpening (shardTreeRoot bytes k n) 8 x.toNat
    ⟨(fireMessages bytes k n).getD x.toNat ByteArray.empty, _⟩ = true at hop
  rw [hm] at hop
  simp only [verifyShardData, authenticatedShard, makeShardHeader, decide_true, Bool.true_and]
  exact hop

structure FireManifest where
  k : Nat
  n : Nat
  ciphertextLength : Nat
  salt : Digest256
  shardTreeRoot : Digest256
  deriving DecidableEq

def makeFireManifest (root salt : Digest256) (w : World) (k n : Nat) : FireManifest :=
  let bytes := encryptWorld root salt w
  ⟨k, n, bytes.length, salt, shardTreeRoot bytes k n⟩

def selectedShards_binding (root : Digest256) (xs : List GF256) (a b : GF256 → ShardData)
    (ha : ∀ x ∈ xs, verifyShardData root x (a x) = true)
    (hb : ∀ x ∈ xs, verifyShardData root x (b x) = true) :
    PSum (∀ x ∈ xs, (a x).bytes = (b x).bytes) CshakeCollision :=
  match xs with
  | [] => .inl (fun _ h => nomatch h)
  | x :: xs => by
    match shardData_binding root x (a x) (b x) (ha x (by simp)) (hb x (by simp)) with
    | .inr c => exact .inr c
    | .inl he =>
      match selectedShards_binding root xs a b (fun y hy => ha y (List.mem_cons_of_mem _ hy))
          (fun y hy => hb y (List.mem_cons_of_mem _ hy)) with
      | .inr c => exact .inr c
      | .inl ht =>
        exact .inl (fun y hy => by rcases List.mem_cons.mp hy with rfl | hy; exact he; exact ht y hy)

def resurrectWorldFromShards (root : Digest256) (m : FireManifest) (xs : List GF256)
    (shards : GF256 → ShardData) : Option World :=
  if 0 < m.k ∧ m.k ≤ m.n ∧ m.n ≤ 255 ∧ xs.length = m.k ∧ xs.Nodup ∧
      (∀ x ∈ xs, x.toNat < m.n ∧ verifyShardData m.shardTreeRoot x (shards x) = true) then
    decodeWorldShards root m.salt m.k m.ciphertextLength xs (fun x => (shards x).bytes)
  else none

/-- Arbitrary verified k-of-n subsets recover the exact world, or explicitly exhibit a collision. -/
def resurrectFromAnyKShards_exact (root salt : Digest256) (w : World) (k n : Nat)
    (xs : List GF256) (supplied : GF256 → ShardData)
    (hk : 0 < k) (hkn : k ≤ n) (hn : n ≤ 255) (hlen : xs.length = k) (hd : xs.Nodup)
    (hvalid : ∀ x ∈ xs, x.toNat < n ∧
      verifyShardData (makeFireManifest root salt w k n).shardTreeRoot x (supplied x) = true) :
    PSum (resurrectWorldFromShards root (makeFireManifest root salt w k n) xs supplied = some w)
      CshakeCollision := by
  let bytes := encryptWorld root salt w
  match selectedShards_binding (shardTreeRoot bytes k n) xs supplied (authenticatedShard bytes k n)
      (fun x hx => (hvalid x hx).2)
      (fun x hx => authenticatedShard_verified bytes k n x (hvalid x hx).1) with
  | .inr c => exact .inr c
  | .inl he =>
    apply PSum.inl
    let m := makeFireManifest root salt w k n
    have hguard : 0 < m.k ∧ m.k ≤ m.n ∧ m.n ≤ 255 ∧ xs.length = m.k ∧ xs.Nodup ∧
        (∀ x ∈ xs, x.toNat < m.n ∧ verifyShardData m.shardTreeRoot x (supplied x) = true) :=
      ⟨hk, hkn, hn, hlen, hd, hvalid⟩
    unfold resurrectWorldFromShards
    rw [ite_eq_left hguard]
    have hr : recoverShardBytes k bytes.length xs (fun x => (supplied x).bytes) =
        recoverShardBytes k bytes.length xs (encodeShardBytes bytes k) := by
      unfold recoverShardBytes
      apply List.map_congr_left
      intro i _
      congr 1
      unfold lagrangeEvalAt
      congr 1
      apply lagrangeInterpolate_congr
      intro x hx
      dsimp only
      rw [he x hx]
      rfl
    change decodeWorldShards root salt k bytes.length xs (fun x => (supplied x).bytes) = some w
    unfold decodeWorldShards
    rw [hr, recoverShardBytes_exact bytes k xs hk (by omega) hd hlen]
    exact decryptWorld_encryptWorld root salt w

/-- Construct a receipt by executing the transfer and then committing its complete payload. -/
def makeTransitionReceipt (s : CustodyState) (amount : Nat) : VaultTransitionReceipt :=
  let r : VaultTransitionReceipt := ⟨s.vaultId, s.mandateId, s.receiptHead, s.epoch + 1, amount,
    ⟨s.balances.source - amount, s.balances.destination + amount, s.balances.allowance - amount⟩,
    s.receiptHead⟩
  { r with commitment := transitionCommitment r }

theorem checkKernelTransitionReceipt_complete (s : CustodyState) (amount : Nat)
    (hs : amount ≤ s.balances.source) (ha : amount ≤ s.balances.allowance) :
    checkKernelTransitionReceipt s (makeTransitionReceipt s amount) = true := by
  simp only [checkKernelTransitionReceipt, makeTransitionReceipt, transitionCommitment,
    VaultTransitionReceipt.payload, hs, ha, decide_true, Bool.and_self]

/-- Array indexing gives a linear pass in the payload size for fixed k. -/
def encodeShardBytesExec (bytes : List UInt8) (k : Nat) (x : GF256) : ByteArray :=
  let data := bytes.toArray
  ⟨((List.range (shardWidth bytes.length k)).map fun col => gfByte
    (evalPolyGF256 (lagrangeInterpolatePoly (systematicPoints k)
      (fun y => byteGF (data[col * k + y.toNat]?.getD 0))) x)).toArray⟩

@[csimp] theorem encodeShardBytes_eq_exec : @encodeShardBytes = @encodeShardBytesExec := by
  funext bytes k x
  have h (col : Nat) : stripeSamples bytes k col =
      (fun y => byteGF (bytes[col * k + y.toNat]?.getD 0)) := by
    funext y
    simp only [stripeSamples, List.getD_eq_getElem?_getD]
  simp only [encodeShardBytes, encodeShardBytesExec, stripePolynomial, h, List.getElem?_toArray]

/-- Custody configuration carries actual randomness for each polynomial coefficient. -/
structure ThresholdSecretCustody where
  threshold : Nat
  providers : Nat
  thresholdPositive : 0 < threshold
  thresholdBound : threshold ≤ providers
  providersBound : providers ≤ 255
  secret : Secret32
  randomness : Fin 32 → List GF256
  randomnessLength : ∀ i, (randomness i).length = threshold - 1

def ThresholdSecretCustody.polynomials (c : ThresholdSecretCustody) : SharingPolynomial :=
  fun i => c.secret i :: c.randomness i

theorem thresholdCustody_reconstruct (c : ThresholdSecretCustody) (xs : List GF256)
    (hd : xs.Nodup) (hl : xs.length = c.threshold) :
    shamirReconstruct xs (shamirShare c.polynomials) = c.secret := by
  rw [shamirReconstruct_exact xs c.polynomials hd (fun i => by
    simp only [ThresholdSecretCustody.polynomials, List.length_cons, c.randomnessLength, hl]
    have := c.thresholdPositive
    omega)]
  funext i
  simp only [shamirShare, ThresholdSecretCustody.polynomials, evalPolyGF256,
    gfMul_zero_left, gfAdd_zero]

/-- Recovery reads unboxed arrays directly, rather than walking a shard prefix per byte. -/
def recoverShardBytesExec (k len : Nat) (xs : List GF256) (shards : GF256 → ByteArray) : List UInt8 :=
  (List.range len).map fun i => gfByte (lagrangeEvalAt xs
    (fun x => byteGF ((shards x).data[i / k]?.getD 0)) (BitVec.ofNat 8 (i % k)))

@[csimp] theorem recoverShardBytes_eq_exec : @recoverShardBytes = @recoverShardBytesExec := by
  funext k len xs shards
  simp only [recoverShardBytes, recoverShardBytesExec, List.getD_eq_getElem?_getD, Array.getElem?_toList]

def secretToLastShare32 (xs : List GF256) (observed : GF256 → Secret32)
    (last : GF256) (s : Secret32) : Secret32 :=
  fun i => secretToLastShare xs (fun x => observed x i) last (s i)

def lastShareToSecret32 (xs : List GF256) (observed : GF256 → Secret32)
    (last : GF256) (y : Secret32) : Secret32 :=
  fun i => lastShareToSecret xs (fun x => observed x i) last (y i)

theorem interposer_secret32_bijection (xs : List GF256) (observed : GF256 → Secret32)
    (last : GF256) (hd : xs.Nodup) (hz : 0 ∉ xs) (hl : last ∉ 0 :: xs) :
    (∀ s, lastShareToSecret32 xs observed last (secretToLastShare32 xs observed last s) = s) ∧
    (∀ y, secretToLastShare32 xs observed last (lastShareToSecret32 xs observed last y) = y) := by
  constructor
  · intro s; funext i
    exact (interposer_t_minus_1_information_theoretic_secrecy xs (fun x => observed x i) last hd hz hl).1 (s i)
  · intro y; funext i
    exact (interposer_t_minus_1_information_theoretic_secrecy xs (fun x => observed x i) last hd hz hl).2 (y i)

/-- The counted product space contains exactly the tuples with the indicated coordinates. -/
theorem challengeTuples_mem (positions tuple : List Nat) (q : Nat) :
    tuple ∈ challengeTuples positions q ↔ tuple.length = q ∧ ∀ i ∈ tuple, i ∈ positions := by
  induction q generalizing tuple with
  | zero =>
    simp only [challengeTuples, List.mem_cons, List.not_mem_nil, or_false, List.length_eq_zero_iff]
    constructor
    · intro h; subst tuple; exact ⟨rfl, fun _ h => nomatch h⟩
    · intro h; exact h.1
  | succ q ih =>
    constructor
    · intro hm
      obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp hm
      obtain ⟨rest, hr, he⟩ := List.mem_map.mp ht
      subst tuple
      have facts := ih rest |>.mp hr
      refine ⟨by simp only [List.length_cons, facts.1], ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact facts.2 j hj
    · intro ht
      cases tuple with
      | nil => simp only [List.length_nil] at ht; omega
      | cons i rest =>
        apply List.mem_flatMap.mpr
        refine ⟨i, ht.2 i (by simp), List.mem_map.mpr ⟨rest, ?_, rfl⟩⟩
        apply (ih rest).mpr
        exact ⟨by simpa only [List.length_cons, Nat.add_right_cancel_iff] using ht.1,
          fun j hj => ht.2 j (List.mem_cons_of_mem _ hj)⟩

def makePorResponse (bytes : List UInt8) (k n : Nat) (x : GF256) (blockIndex : Nat) : PorResponse :=
  let s := authenticatedShard bytes k n x
  ⟨s.header, s.siblings,
    treeOpening s.header.blockDepth (blockMessages s.bytes s.header.blockDepth) blockIndex⟩

theorem verifyPorResponse_complete (bytes : List UInt8) (k n : Nat) (x : GF256) (j : Nat)
    (hx : x.toNat < n) (hj : j < (encodeShardBytes bytes k x).size) :
    verifyPorResponse (shardTreeRoot bytes k n) 8 x.toNat j (makePorResponse bytes k n x j) = true := by
  have hs := authenticatedShard_verified bytes k n x hx
  simp only [verifyShardData, Bool.and_eq_true] at hs
  let payload := encodeShardBytes bytes k x
  let depth := payload.size.log2 + 1
  have hl : (blockMessages payload depth).length = 2 ^ depth := by
    simp only [blockMessages, List.length_map, List.length_range]
  have hi : j < (blockMessages payload depth).length := by
    rw [hl]
    exact Nat.lt_trans hj Nat.lt_log2_self
  have hb := treeOpening_verified depth (blockMessages payload depth) j hl hi
  exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
    ⟨(Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl, decide_eq_true hj⟩, hs.2⟩, hb⟩

theorem makePorResponse_block (bytes : List UInt8) (k n : Nat) (x : GF256) (j : Nat)
    (hj : j < (encodeShardBytes bytes k x).size) :
    (makePorResponse bytes k n x j).block.bytes = ⟨#[(encodeShardBytes bytes k x)[j]'hj]⟩ := by
  let payload := encodeShardBytes bytes k x
  let depth := payload.size.log2 + 1
  change (blockMessages payload depth).getD j ByteArray.empty = _
  have hi : j < (blockMessages payload depth).length := by
    simp only [blockMessages, List.length_map, List.length_range]
    exact Nat.lt_trans hj Nat.lt_log2_self
  rw [Lsafe.getD_of_lt hi]
  simp only [blockMessages, List.getElem_map, List.getElem_range]
  rw [dite_eq_left (show j < payload.size from hj)]

/-- Bind a hostile response directly to an encoded byte, without assuming an authentic
response's acceptance as an extra premise. -/
def verifyEncodedPorChallenge_sound_or_collision (bytes : List UInt8) (k n : Nat)
    (x : GF256) (j : Nat) (response : PorResponse) (hx : x.toNat < n)
    (hj : j < (encodeShardBytes bytes k x).size)
    (h : verifyPorResponse (shardTreeRoot bytes k n) 8 x.toNat j response = true) :
    PSum (response.block.bytes = ⟨#[(encodeShardBytes bytes k x)[j]'hj]⟩) CshakeCollision :=
  match verifyPorChallenge_sound_or_collision (shardTreeRoot bytes k n) 8 x.toNat j response
      (makePorResponse bytes k n x j) h (verifyPorResponse_complete bytes k n x j hx hj) with
  | .inr c => .inr c
  | .inl he => .inl (he.2.trans (makePorResponse_block bytes k n x j hj))

end Obend.Vault.SurviveFirePor
