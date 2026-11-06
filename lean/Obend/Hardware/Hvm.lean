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

## The reduction machine's nets

`Hvm.Inet` maps the model to `Obend.Hardware.ReductionMachine`'s arena (`ReductionMachine.Arena`:
node memory and a link table, `Arena.Step` firing an active pair by `reduceActivePair`'s outcome) for
the combinator fragment, `CON` (`con`, label 0), `DUP` (`dup`, label 1) and `ERA` (`era`).
`Repr A ρ c` says the arena is the configuration; `inetOfHvm_sound`: every VOID, ERAS, ANNI and COMM
step of a represented configuration is one `Arena.Step` to an arena representing the result (after
HVM2's LINK of the bare wires ANNI leaves), when the fired pair's children share no variable. The
machine's commutation is Lafont's (`commuteSpawnedNodes`, `commuteSplices`, `commute_wellformed`).
`NUM`, `REF`, `OPR`, `SWI` are not mapped; `Hvm.Inet`'s header says what each would need.
-/
public import Obend.Hardware.Hvm.Model
public import Obend.Hardware.Hvm.Net
public import Obend.Hardware.Hvm.Lower
public import Obend.Hardware.Hvm.Inet
