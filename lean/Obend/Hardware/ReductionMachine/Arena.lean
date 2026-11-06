module
/-
# Obend.Hardware.ReductionMachine.Arena — applying a rewrite outcome to an arena

`reduceActivePair` answers an `ActivePair` with an `INetRewriteOutcome`; this module says what an
outcome does to the net it fires in. An `Arena` is node memory indexed by id (kind, label,
immediate) and a link table giving, for every port, the port across its wire; `Arena.inet? i` is
node `i` as the rule engine reads it, its auxiliary fields taken from the table. `Arena.Step` fires
one active pair (two nodes whose principal ports face each other): it removes the pair and applies
the outcome of `reduceActivePair`:

* `annihilate w1 w2`: wires `w1` and `w2`;
* `erase ps`: one fresh eraser facing each port of `ps`;
* `commute spawned splices`: places the copies (their auxiliary ports wired as their fields say)
  and wires each splice;
* `betaNat64`: no arena reading (an affine `slope * x + offset` step is not an interaction rule);
  `Arena.apply` answers `none` and the pair does not fire.

Ports of a node outside the arena are free ports (the root of a net). Fresh ids are allocated from
`next`. A wire whose ends are both auxiliary ports of the fired pair (a loop at the pair) is not
resolved: `apply` wires the outside ports it is given, and callers rule loops out.
-/
public import Obend.Hardware.ReductionMachine
@[expose] public section

namespace Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-- `f` with `p` sent to `q`. -/
def upd (f : PortRef → PortRef) (p q : PortRef) : PortRef → PortRef :=
  fun x => if x = p then q else f x

theorem upd_apply (f : PortRef → PortRef) (p q x : PortRef) :
    upd f p q x = if x = p then q else f x := rfl

/-- Node memory and the link table. -/
structure Arena where
  node : Nat → Option (INetNodeKind × Nat × Nat)
  link : PortRef → PortRef
  next : Nat

namespace Arena

/-- Node `i` as `reduceActivePair` reads it. -/
def inet? (A : Arena) (i : Nat) : Option INetNode :=
  (A.node i).map fun k => ⟨i, k.1, k.2.1, k.2.2, A.link ⟨i, 1⟩, A.link ⟨i, 2⟩⟩

/-- Wire `p` and `q`. -/
def connect (A : Arena) (p q : PortRef) : Arena :=
  { A with link := upd (upd A.link p q) q p }

/-- Free node `i`'s memory. -/
def drop (A : Arena) (i : Nat) : Arena :=
  { A with node := fun k => if k = i then none else A.node k }

/-- Write node `n`: its kind, label and immediate, and its auxiliary fields into the link table. -/
def place (A : Arena) (n : INetNode) : Arena :=
  { A with
    node := fun k => if k = n.id then some (n.kind, n.label, n.immVal) else A.node k
    link := upd (upd A.link ⟨n.id, 1⟩ n.aux1) ⟨n.id, 2⟩ n.aux2 }

/-- Wire each splice, in order. -/
def splice (A : Arena) : List (PortRef × PortRef) → Arena
  | [] => A
  | w :: ws => (A.connect w.1 w.2).splice ws

/-- One fresh eraser facing each port. -/
def erasers (A : Arena) : List PortRef → Arena
  | [] => A
  | p :: ps => ({ A.place (mkEraNode A.next) with next := A.next + 1 }.connect ⟨A.next, 0⟩ p).erasers ps

/-- Apply the outcome of firing `l ~ r`. -/
def apply (A : Arena) (l r : INetNode) : INetRewriteOutcome → Option Arena
  | .annihilate w1 w2 => some (((A.drop l.id).drop r.id |>.connect w1.1 w1.2).connect w2.1 w2.2)
  | .erase ps => some (((A.drop l.id).drop r.id).erasers ps)
  | .commute spawned splices =>
    some ({ spawned.foldl place ((A.drop l.id).drop r.id) with next := A.next + spawned.length }.splice splices)
  | .betaNat64 _ => none

/-- Fire one active pair: two nodes whose principal ports face each other, rewritten by the outcome
`reduceActivePair` gives them. -/
inductive Step : Arena → Arena → Prop where
  | fire {A A' : Arena} {i j : Nat} {l r : INetNode} :
      i ≠ j → A.inet? i = some l → A.inet? j = some r →
      A.link ⟨i, 0⟩ = ⟨j, 0⟩ → A.link ⟨j, 0⟩ = ⟨i, 0⟩ →
      A.apply l r (reduceActivePair ⟨l, r⟩ A.next) = some A' → Step A A'

/-! ### What the operations do to memory and links -/

@[simp] theorem connect_node (A : Arena) (p q : PortRef) : (A.connect p q).node = A.node := rfl
@[simp] theorem connect_next (A : Arena) (p q : PortRef) : (A.connect p q).next = A.next := rfl
theorem connect_link (A : Arena) (p q x : PortRef) :
    (A.connect p q).link x = if x = q then p else if x = p then q else A.link x := rfl

@[simp] theorem drop_link (A : Arena) (i : Nat) : (A.drop i).link = A.link := rfl
@[simp] theorem drop_next (A : Arena) (i : Nat) : (A.drop i).next = A.next := rfl
theorem drop_node (A : Arena) (i k : Nat) : (A.drop i).node k = if k = i then none else A.node k := rfl

@[simp] theorem place_next (A : Arena) (n : INetNode) : (A.place n).next = A.next := rfl
theorem place_node (A : Arena) (n : INetNode) (k : Nat) :
    (A.place n).node k = if k = n.id then some (n.kind, n.label, n.immVal) else A.node k := rfl
theorem place_link (A : Arena) (n : INetNode) (x : PortRef) :
    (A.place n).link x = if x = ⟨n.id, 2⟩ then n.aux2 else if x = ⟨n.id, 1⟩ then n.aux1 else A.link x := rfl

end Arena
end Obend.Hardware.ReductionMachine
