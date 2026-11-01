# Report: lane Lower, a verified lowering of a Lean fragment to Core4 (Claude Opus, 2026-11-01)

Placed by the root from the lane's closing report. Commits `8895193..8d65784` on `0c61836`: fragment,
semantics, lowering with `lower_checks`, `lower_sound` with teeth, the tool with programs and the
book. hbox at `8d65784`: tiers 1 and 2 green, census 45,336 constants with none on `sorryAx` or an
axiom; every suite green including the new `tests/lower/run-lower.py` 76/76. No new `Term`
constructor. Files under `Obend/Lower/` are `module`s; the reader and tool `public import Lean`.

## Design
As Lean4Lean reads `Expr` into `VExpr`, `Fragment.read` reads a closed kernel term into `LExpr`
(Lean-lite): one node per kernel form the fragment reduces, types and proofs erased to `erased` (λ□'s
box, decided as Dima 2025 decides it), binders annotated with their lowered Core4 type. The reader
is the trust boundary. `SStep` is weak-head call-by-name, the kernel's `whnf` rule for rule. `lowerT`:
erased to `{}`; definitions inlined; structures to records with `split`/`get`; non-recursive
inductives to `inject`/`case` with a `split` per arm; `Nat` to `nat`, literal operations to `binary`,
`Nat.succ` to `+1`; `Bool.rec` to `ifBool`; `Nat.rec` to `fix (λself.λ_.λk. ifZero k z (s p (self p))) {}`;
`let` to `(λx.b) v`. The simulation is up to `Obend.Equiv.Ahead`.

| `SStep` | Lean4Lean |
|---|---|
| beta, appFun | `whnfCore` app, `IsDefEq.beta` |
| zeta | `whnfCore` letE |
| delta | `unfoldDefinition`, `IsDefEq.delta` (levels erased) |
| succFold, succArg | `reduceNat` |
| binLit, binLeft, binRight | `reduceBinNatOp`, call-by-value, left first |
| natRec*, boolRec*, splitRecord, casesInject | `inductiveReduceRec`, `toCtorIfLit`, `IsDefEq.iota` |
| projRecord, projTarget | `whnfCore` proj / `projReduce` |

The kernel is lazier in two places not met on closed terminating `Nat` terms: a literal operation
with non-literal arguments falls back to δ, and `Nat.succ e` stays a whnf.

## Proved
`lower_step` (each source step is a δ-stutter that strictly shrinks the term, or a positive Core4 run
to the lowered next step up to `Ahead`); `lower_sound` (`lower_sound_nat`, `lower_sound_bool` exactly as
briefed; `lower_sound_inject` for constructors, with the payload up to same runs); `lower_value`;
teeth: dropping `Nat.rec`'s minor premise refuted (8 becomes 7), `Nat.sub` as `add` refuted (`5 - 3`
becomes 8); `lower_checks` (every simply typed fragment term, `LTyped`, lowers to a term `checkAgainst`
accepts at its type, through `PartialTyping` and completeness); `lean_to_book` (if `e n` reduces to
`m`, the emitted Leaf book's member at `n` halts with `m`: `lower_sound_nat`, `late_binding`,
`book_sound` composed); the `lower@1` judge with a planted bad certificate refused. `lower_complete`
(the converse) is not stated.

## The fragment
In: `fun`, application, `let`, `Nat` literals, `Nat.succ`, the seven literal operations, `Nat.rec`,
`Bool`/`Bool.rec`, structures without indices (universe-polymorphic library ones included; `Decidable`
is a structure in 4.35), non-recursive inductives without indices, every definition unfolded at use
(matchers, `ite`/`dite`, instances, `brecOn`/`below`/`PProd`, `WellFounded.Nat.fix`, so well-founded
recursion on a `Nat` measure is in), erased proofs and types. Out: other well-founded recursion
(`Acc.rec` needs the erased proof), indexed/recursive/mutual/nested inductives, `Eq.rec`, `Quot`,
strings, axioms, `opaque`, `partial`. Typed subset: a recursor whose motive computes a type by
recursion (`Nat.below`) lowers and runs but the checker refuses it (`fib`, `halvings`).

## Programs
Nine lowered programs agree with `#eval` on the demand machine at every tested argument: `double`,
`fib`, `pointNorm`, `shapeArea`, `addLit`, `sumTo`, `small`, `isEven`, `halvings`; all but `fib` and
`halvings` pass the checker. `double` emitted as a Leaf book gives 42 from book and machine. `ack`
and `greeting` are refused by the reader as outside the fragment.

## Lean4Lean at Lean 4.35 (probed on hbox, HEAD `67f63b0`, pinned 4.33.0-rc2, needs Batteries)
`Lean4Lean.Theory` builds at 4.35 with Batteries v4.35.0 (22 modules). The kernel port does not:
`reduceBool`/`reduceNat` removed in 4.35, a `List` lemma changed, the kernel form of `Nat.div` fails
its primitive check; 110 of 128 jobs after two patches. Cost of the dependency: Batteries (we have
none) and plain non-module files (tier-2 plain file like BendTT). Decisive: the theory has 9 `sorry`s,
including `VInductDecl.WF` and `VEnv.addInduct`; it has no inductive types yet. A connection theorem
can cover β, ζ, δ and the literal operations today; ι waits on upstream.

## The chain to silicon
| link | status |
|---|---|
| Lean `Expr` → Lean-lite | trusted reader |
| Lean-lite's reduction vs Lean's kernel (Lean4Lean) | rule table, not proved |
| Lean-lite → Core4 (`lower_sound`, `lower_checks`) | proved |
| Core4 → Leaf book (`lean_to_book`) | proved |
| book → BendTT `Eval` | stated (REPORT-LEAF §5) |
| book or Core4 term → hardware | absent for this chain |

`Hardware/Compiler.lean`'s `compileTerm_sound` relates RTL to `evalTermHw`, an independent 64-bit
evaluator over a subset with no `fix` and no records, untied to `Evaluates`; `compileBookToRtl` has
no theorem; `hardware/HardwareVerify.lean`'s `chip_computes_demand` covers objects whose fields are
literals or `self` references. A lowered program uses functions, records and `fix`: outside both.

## Decision (taken by the root under standing approval)
Structural recursion is typed by lowering a recursive definition from its unfolding equation
(`f.eq_def`, as Dima 2025 does) to a `fix` with a simple type, adding a recursive-δ rule to the
source semantics (option A); Core4's `Ty` is not extended with a type for the `below` tower.
