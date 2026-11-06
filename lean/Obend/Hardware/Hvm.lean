module
/-
# Obend.Hardware.Hvm — a Leaf book lowered to HVM2 interaction nets, with its soundness theorem

Rung 2 of `HARDWARE.md`. HVM2 (HigherOrderCO, `github.com/HigherOrderCO/HVM2`, crate `hvm` 2.0.22,
paper `paper/HVM2.typst`) is a parallel evaluator for interaction combinators with a Rust, a C and
a CUDA runtime; its input is a textual book of named nets. Three modules:

* `Hvm.Model`: HVM2's net language (the eight node kinds, U24 numbers and `Numb::operate` of
  `src/hvm.rs`), its interaction rules as a relation `Step` (LINK, CALL, VOID, ERAS, ANNI, COMM,
  OPER, SWIT, and the copy of a reference to a safe definition), an executable head-redex reducer
  `run`, and the emitter `emitHvm` in the syntax `hvm run` reads (`src/ast.rs`);
* `Hvm.Net`: the expression language `FExp` (U24 literals, variables, HVM2's operators, a strict
  `let`, a switch with inline branches `ifz`, a switch with λ-lifted branches `ifzL`, a call of a
  named definition), its compilation to redexes `comp` and to definition nets `defNet`, and the net
  theorem `comp_reduces`: under `Good` and `BookOk` (every lifted branch and every called
  definition in the book as `defNet` compiles it), an expression whose value at some fuel is `v`
  (`evalF`, HVM2's wrapping arithmetic, `none` an erased value) reduces under `Step` to the one
  redex `nul v ~ K`; `callDef`, the same for a reference meeting its arguments (CALL on variables
  above every variable of the configuration); `main_reduces`, a whole run from `@main`;
* `Hvm.Lower`: the translation `toS` of a Leaf term to one `FExp` per slot of its sort, the exact
  evaluation `evalE` (bridged to `evalF` by `evalE_evalF`), the soundness of the translation against
  Core4's reference reduction `trSound` (by induction on fuel, the fixpoints' recursion carried in
  the environment invariant `EnvOk` as `FunOk`), the observation probes `HSort.observe`, the book
  `lowerBookToHvm` and the theorem `lowerBookToHvm_sound`.

## What `lowerBookToHvm_sound` says

For a book `B` that `lowerBookToHvm` accepts, a member `m` it lowered to `d` (arity `k`, result sort
`d.sort`), arguments `x :: rest` (`k` naturals), and a fuel at which every result slot's exact
evaluation answers (`evalE`, every intermediate value the Core4 value and below `2^24`):

1. the model reduces `@main = r & @m ~ (#x (… r))` against the lowered book to the normal form whose
   root is the tuple of the slot values (a number for one slot) and whose bag is empty;
2. `evalBookAt B m (.nat x)` is a term `r` such that every observation `d.sort.observe` names (the
   scalar; each field of a record; a sum's tag as its label, and its payload's scalar or fields)
   holds: its probe, applied to `r` after the remaining arguments, halts under Core4's reference
   reduction with that ground observation.

So the net's normal form decodes, slot by slot, to what `evalBookAt` evaluates to.

## The fragment

`lowerMember` lowers `dataPinSpecialize (evalBook B m)`, the code `evalBookAt` folds, of the shape
`λself. λx₁ … λxₖ. body` (`k ≥ 1`: a method's curried result is its arity). In `body`, `toS` accepts:

* naturals below `2^24` and Booleans; the variables in scope; `ifZero`, `ifBool`; `app (lam b) a`
  (a let, its value's slots let-bound); the primitives `add multiply subtract divide modulo equal
  less lessEqual conjunction` at their Core4 sorts (truncated subtraction, floor division and `%`
  derived over HVM2's wrapping operators, the divisor never zero, since the Rust runtime panics on
  one and eager evaluation runs a guarded quotient's untaken branch);
* **records of scalars**, unboxed: a record is one slot per field inside a body (`record` literals,
  `get` selects a slot after evaluating all of them) and a `CON` tuple at the member's result;
* **sums whose arms carry a scalar or a record of scalars**: a tag slot and the widest payload's
  slots (`inject`; `case` a chain of switches on the tag, each arm's body with its payload bound);
* **recursion**: `fix (λrec. λsup. λx. body) i` applied to one argument (of any sort above; several
  arguments as a record), the recursive calls `rec a` in `body`, `sup` unread, a scalar result: one
  HVM2 definition per fixpoint, its parameters the whole enclosing environment and the argument's
  slots, each call a `REF`; every switch whose branches call is λ-lifted to two definitions, so the
  untaken branch is a reference voided before it is expanded (HVM2 evaluates eagerly). `Nat.rec`
  as `Obend.Lower.lowerT` lowers it (`natRecSpec`) is of this shape;
* **λ as a value only as a method's curried result**: `λx. λy. body` is a member of arity 2, its
  closure observed by applying it (the probes' `.arg` steps). A λ passed as an argument, stored in a
  record or sum, returned from a branch, or applied as anything but a let or a recursive call is
  refused: a duplicated higher-order λ is exactly what HVM2's single duplicator cannot share soundly
  (`HVM2.typst`, §Limitations).

Refused by name: `self` reads the folder did not resolve, labels, the object forms (`mix`,
`specification`, `prototype`, `reflect`, `metadata`, `project`, `extend`), activities (`perform`,
`done`), `split`, holes, the bitwise, shift, signed and fixed-point primitives, recursion returning a
record or a sum, `fix` not of the shape above, nested records, sums inside records.

## Where the model departs from HVM2, by name

* **LINK is the paper's global substitution** (`B[x ← A]`), not the atomic substitution map of
  `src/hvm.rs`; the paper argues the two agree (§Substitution Map).
* **Schedules.** `Step` lets any redex fire, in either orientation. The theorem exhibits one
  reduction to the normal form; that HVM2's own schedule reaches the same normal form is the strong
  confluence the paper claims, not proved here.
* **Numbers.** Only U24 and the operators; I24, F24 and the casts are not modelled. A zero divisor
  gives `0` for `/` and the dividend for `%` (the C runtime on arm64; the Rust runtime panics).
* **CALL** takes any injective renaming fresh for the configuration (HVM2 allocates fresh
  locations); `REF ~ DUP` copies a reference to a safe definition and is stuck otherwise (HVM2 exits);
  the `REF ~ ROOT` start is not modelled: a run starts from `@main`'s net.

## The reduction machine's nets, and what a proved map needs

`Obend.Hardware.ReductionMachine` represents an interaction net as an arena of `INetNode`s (kinds
`era con dup sup app lam nat64`, a label, an immediate, two auxiliary `PortRef`s, the principal port
implicit) and rewrites an `ActivePair` by `reduceActivePair` into an *outcome* (`annihilate`,
`commute`, `erase`, `betaNat64`), not into a new arena. The two are **not** one model, and today they
are related only node by node:

* **Same combinators, on `CON`/`DUP`/`ERA`**: `inetOfHvm` sends `CON` to `con` (label 0), `DUP` to
  `dup` (label 1), `ERA` to `era`. Annihilation agrees (`inetOfHvm_annihilate`: the outcome wires the
  auxiliary ports pairwise, as ANNI does) and erasure agrees (`inetOfHvm_erase`: the outcome erases
  both auxiliary ports, as ERAS does).
* **Commutation disagrees.** `commuteSpawnedNodes` gives the third spawned node the auxiliary port
  `l.aux1` while the first spawned node's `aux1` already points at that node's slot 1
  (`inet_commute_ports_twice`): a slot is claimed by two wires, which no port graph has. HVM2's COMM
  (Lafont's commutation) faces each spawned node's principal port with one original auxiliary port.
* **No counterpart**: `NUM`, `REF`, `OPR`, `SWI` have none in `INetNodeKind`; a `nat64` meeting a
  combinator falls through to the label test (annihilate or commute) where HVM2 copies or erases the
  number; `lam`/`app`/`betaNat64` (an affine `slope * x + offset` step) are not interaction-combinator
  rules; and annihilation there is decided by label alone, so a `con` and a `sup` of one label
  annihilate.

`inetOfHvm_sound` (an arena step simulating `Step`) is therefore not stated: it needs (1) an arena
semantics, applying an outcome to an arena, which `ReductionMachine` does not define; (2) a
flattening of an `HTree` configuration into an arena (trees to nodes, variables to wires); (3)
Lafont's commutation in `commuteSpawnedNodes`; (4) node kinds for `NUM`, `REF`, `OPR`, `SWI` with
OPER, SWIT and CALL (or a lowering of numbers and switches to pure combinators, which HVM2 does not
use). With those, the statement would be: flattening commutes with one step, up to renaming.
-/
public import Obend.Hardware.Hvm.Model
public import Obend.Hardware.Hvm.Net
public import Obend.Hardware.Hvm.Lower
public import Obend.Hardware.ReductionMachine
@[expose] public section
namespace Obend.Hardware.Hvm
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-- The reduction machine's kind and label for an HVM2 node, where it has one. -/
def inetKindOf : HTree → Option (INetNodeKind × Nat)
  | .con _ _ => some (.con, 0)
  | .dup _ _ => some (.dup, 1)
  | .era => some (.era, 0)
  | _ => none

/-- An HVM2 node as an `INetNode`, its auxiliary ports at the given references. -/
def inetOfHvm (id : Nat) (t : HTree) (a1 a2 : PortRef) : Option INetNode :=
  (inetKindOf t).map fun kl => ⟨id, kl.1, kl.2, 0, a1, a2⟩

/-- **Annihilation agrees**: two `CON` (or two `DUP`) nodes annihilate in both models, the auxiliary
ports wired pairwise. -/
theorem inetOfHvm_annihilate (id1 id2 next : Nat) (a1 a2 b1 b2 : PortRef) (A1 A2 B1 B2 : HTree) :
    (∀ l r, inetOfHvm id1 (.con A1 A2) a1 a2 = some l → inetOfHvm id2 (.con B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .annihilate (a1, b1) (a2, b2)) ∧
    localRule (.con A1 A2) (.con B1 B2) = some [(A1, B1), (A2, B2)] ∧
    (∀ l r, inetOfHvm id1 (.dup A1 A2) a1 a2 = some l → inetOfHvm id2 (.dup B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .annihilate (a1, b1) (a2, b2)) ∧
    localRule (.dup A1 A2) (.dup B1 B2) = some [(A1, B1), (A2, B2)] := by
  refine ⟨fun l r hl hr => ?_, rfl, fun l r hl hr => ?_, rfl⟩ <;>
    simp only [inetOfHvm, inetKindOf, Option.map_some, Option.some.injEq] at hl hr <;>
    subst hl hr <;> simp [reduceActivePair]

/-- **Erasure agrees**: an eraser meeting `CON` or `DUP` erases both auxiliary ports. -/
theorem inetOfHvm_erase (id1 id2 next : Nat) (a1 a2 b1 b2 : PortRef) (B1 B2 : HTree) :
    (∀ l r, inetOfHvm id1 .era a1 a2 = some l → inetOfHvm id2 (.con B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .erase [b1, b2]) ∧
    localRule .era (.con B1 B2) = some [(.era, B1), (.era, B2)] := by
  refine ⟨fun l r hl hr => ?_, rfl⟩
  simp only [inetOfHvm, inetKindOf, Option.map_some, Option.some.injEq] at hl hr
  subst hl hr; simp [reduceActivePair]

/-- **Commutation disagrees**: the first node `commuteSpawnedNodes` spawns points its `aux1` at slot 1
of the third, and the third's own `aux1` is the old node's `aux1`: slot 1 of the third node is on two
wires. -/
theorem inet_commute_ports_twice (l r : INetNode) (next : Nat) :
    ((commuteSpawnedNodes l r next)[0]?).map (·.aux1) = some ⟨next + 2, 1⟩ ∧
    ((commuteSpawnedNodes l r next)[2]?).map (·.id) = some (next + 2) ∧
    ((commuteSpawnedNodes l r next)[2]?).map (·.aux1) = some l.aux1 := by
  simp [commuteSpawnedNodes]
