/-
The first programs lowered from Lean to Core4 (`obend lower NAME`, `tests/lower/run-lower.py`).
Plain Lean: no imports beyond `Init`, so the tool elaborates this file in-process.
-/

def double (n : Nat) : Nat := n + n

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

structure Point where
  x : Nat
  y : Nat

def Point.norm1 (p : Point) : Nat := p.x + p.y

def Point.swap (p : Point) : Point := { x := p.y, y := p.x }

def pointNorm (n : Nat) : Nat := (Point.swap { x := n, y := 2 * n }).norm1

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

def Shape.area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h

def shapeArea (n : Nat) : Nat := Shape.area (.circle n) + Shape.area (.rect n (n + 1))

def addLit (n : Nat) : Nat := Nat.add n 1000000000000

def sumTo (n : Nat) : Nat := Nat.rec 0 (fun k acc => acc + k + 1) n

def small (n : Nat) : Nat := if n < 3 then 1 else n - 3

def isEven (n : Nat) : Bool := n % 2 == 0

/-- In the fragment, untyped: well-founded recursion on a `Nat` measure, which 4.35 compiles to
`WellFounded.Nat.fix` (structural recursion on a fuel through `Nat.rec`). -/
def halvings (n : Nat) : Nat := if h : n = 0 then 0 else halvings (n / 2) + 1
termination_by n
decreasing_by omega

/-- A proposition with no fields, and a recursor on its (erased) proof: Lean's kernel reduces it (K);
Core4 runs its lowering; the source semantics is stuck (`lower_complete_fails`). -/
structure Witness : Prop

noncomputable def kTooth (n : Nat) : Nat := Witness.rec (motive := fun _ => Nat) n Witness.mk

/-- The kernel reduces it (the recursor of a field-less proposition is K-like). -/
theorem kTooth_three : kTooth 3 = 3 := rfl

/-- Well-founded recursion on a lexicographic measure: in, through its unfolding equation (`ack.eq_def`,
proved by `WellFounded.fix_eq`); its kernel value goes through `Acc.rec`, which is out. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def ackTwo (n : Nat) : Nat := ack 2 n

/-- Out of the fragment: `WellFounded.fix` used directly, whose value is `Acc.rec` on a proof. -/
def countDown (n : Nat) : Nat :=
  WellFounded.fix (measure id).wf (fun n ih => if h : n = 0 then 0 else ih (n - 1) (by
    show n - 1 < n; omega) + 1) n

/-- Out of the fragment: a string. -/
def greeting (n : Nat) : String := toString n
