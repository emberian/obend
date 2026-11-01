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

/-- Out of the fragment: well-founded recursion (`WellFounded.fix`, `Acc.rec`). -/
def halvings (n : Nat) : Nat := if h : n = 0 then 0 else halvings (n / 2) + 1
termination_by n
decreasing_by omega

/-- Out of the fragment: a string. -/
def greeting (n : Nat) : String := toString n

/-- Out of the fragment: eliminating a `Prop` inductive (`And.rec`) into `Type` (`Nat`). -/
def propElim (n : Nat) : Nat := @And.rec True True (fun _ => Nat) (fun _ _ => n) ⟨trivial, trivial⟩
