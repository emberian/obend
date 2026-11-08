module
public import Std
@[expose] public section

namespace Obend.Hardware.Gpu.Ntt.Sum

/-- A finite natural sum, with no implicit reduction or ordering assumption. -/
def sum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => sum n f + f n

@[simp] theorem zero (f : Nat → Nat) : sum 0 f = 0 := rfl
@[simp] theorem succ (n : Nat) (f : Nat → Nat) : sum (n+1) f = sum n f + f n := rfl

theorem cong (n : Nat) (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ,succ,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem cong_mod (m n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i % m = g i % m) : sum n f % m = sum n g % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sum n f + f n) % m = (sum n g + g n) % m
    conv => lhs; rw [Nat.add_mod]
    conv => rhs; rw [Nat.add_mod]
    rw [ih (fun i hi => h i (by omega)),h n (by omega)]

@[simp] theorem sum_zero (n : Nat) : sum n (fun _ => 0) = 0 := by
  induction n <;> simp_all

theorem add (n : Nat) (f g : Nat → Nat) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    sum n (fun i => f i * c) = sum n f * c := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih,Nat.add_mul]

theorem mul_left (n : Nat) (f : Nat → Nat) (c : Nat) :
    sum n (fun i => c * f i) = c * sum n f := by
  simpa only [Nat.mul_comm c] using mul_right n f c

theorem swap (m n : Nat) (f : Nat → Nat → Nat) :
    sum m (fun i => sum n (f i)) = sum n (fun j => sum m (fun i => f i j)) := by
  induction m with
  | zero => simp
  | succ m ih => simp only [succ,ih,add]

theorem append (m n : Nat) (f : Nat → Nat) :
    sum (m+n) f = sum m f + sum n (fun i => f (m+i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    change sum (m+n+1) f = sum m f + (sum n (fun i => f (m+i)) + f (m+n))
    rw [succ,ih,Nat.add_assoc]

/-- Quotient/remainder decomposition of the whole summation domain. -/
theorem blocks (m n : Nat) (f : Nat → Nat) :
    sum (m*n) f = sum m (fun i => sum n (fun j => f (i*n+j))) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul,append,ih,succ]

theorem map_mod (m n : Nat) (f : Nat → Nat) :
    sum n (fun i => f i % m) % m = sum n f % m :=
  cong_mod m n _ _ (by intro i hi; simp)

theorem list_range (n : Nat) (f : Nat → Nat) :
    (List.range n |>.map f).sum = sum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ,ih]

/-- Left-fold reduction is the same modular sum for every initial accumulator. -/
theorem foldl_mod (xs : List Nat) (m acc : Nat) :
    xs.foldl (fun a x => (a+x)%m) acc % m = (acc + xs.sum)%m := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.sum_cons]
    rw [ih]
    rw [Nat.mod_add_mod,Nat.add_assoc]

end Obend.Hardware.Gpu.Ntt.Sum
