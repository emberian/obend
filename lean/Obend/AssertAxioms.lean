module
/-
# `#assert_axioms_tree` — the axiom census as a check that can fail, and the statement census

`#assert_axioms_tree` checks every constant declared in one of this package's modules (roots
`Theory`, `Compiler`, `Kernel`, `Assurance`, `Pred`, `Effects`, `Selvage`, `Host`, `Obend`) that
the importing module can see. It fails on any constant resting on `sorryAx` or on a declared
axiom, and on any package `axiom` declaration; only Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) pass silently. The compiler trust (`native_decide`'s auxiliary
`…._native…` axioms) is admitted only as a counted exception, reported per directory in the verdict:
`native_decide` is a deliberate tool in this tree (the `*_compiled` facts), each such theorem
re-run by `#assert_compiled` (`Obend/AssertCompiled.lean`). `Obend/Census.lean` runs it over the
whole library. Its importer must see the bodies: under a plain `module` import a non-exposed
theorem arrives as an axiom and is refused, so the census is a non-`module` file (or `import all`).

The verdict carries no totals. Headline counts ("N constants, 0 sorryAx") were retired on
2026-11-04 (`review/DECISIONS-20261031.md`): they averaged real metatheory with fixtures and told
the reader nothing. What the census prints instead is a classification per directory
(`theoremCensus` below, rendered by `Obend/Census.lean`): how many theorems quantify over
something, how many are closed statements (a fixture that should be an `example`), how many
`example`s and `#tooth` commands the directory's files hold.

Lean v4.30 precomputes each imported declaration's axioms at olean export, so
the census is a lookup per constant, not a walk.
-/

public import Lean
@[expose] public section

namespace Obend.AssertAxioms

open Lean Elab Command

/-- The axioms a kernel-checked theorem may rest on. -/
meta def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The compiler trust `native_decide` adds; counted (not refused) by
`#assert_axioms_tree`. Since Lean v4.30 each
`native_decide` proof is an auxiliary axiom `<theorem>._native.native_decide.ax_…`
(`Lean.Meta.nativeEqTrue`); v4.35 removed the older global axioms
`Lean.ofReduceBool` and `Lean.trustCompiler`, so the `_native` component is the
whole compiled-trust set. -/
meta def isCompilerTrust (axiomName : Name) : Bool :=
  axiomName.components.any (· == `_native)

/-- A `computed_fields` override: the compiled implementation Lean generates for
an inductive with a `computed_field` (`Noun.mug`, N-MUG). It is a definition
named `…._override` whose only non-standard axiom is `lcProof`, the compiler's
own placeholder. Kernel-checked statements never reach it: a theorem about the
inductive or its field depends on the kernel-side definitions, which carry no
`lcProof` (a theorem that did reach it would be an offender). Like
`native_decide`, this is compiler trust, counted and reported, never silent. -/
meta def isComputedFieldOverride (info : ConstantInfo) (constant : Name) (outside : List Name) : Bool :=
  info matches .defnInfo _ && constant.components.getLast? == some `_override &&
    outside == [``lcProof]

/-- This package's module roots. -/
meta def packageRoots : List Name :=
  [`Theory, `Compiler, `Kernel, `Assurance, `Pred, `Effects, `Selvage, `Host, `Obend]

/-- The module a constant was declared in, when it is one of this package's. -/
meta def packageModule? (env : Environment) (constant : Name) : Option Name := do
  let index ← env.getModuleIdxFor? constant
  let module ← env.header.moduleNames[index.toNat]?
  if packageRoots.contains module.getRoot then some module else none

/-- The directory a module is reported under: its first two components (`Obend.Core`), or the
module itself when it sits at the root (`Obend.Slot`, `Obend.Fold`). -/
meta def directoryOf (module : Name) : Name :=
  match module.components with
  | a :: b :: _ :: _ => Name.anonymous.str a.toString |>.str b.toString
  | _ => module

/-- A statement is *closed* when it quantifies over nothing: after looking through `let`s, every
binder is a proposition (a hypothesis) or an instance. `decide +kernel` on a concrete fixture, a
`rfl` between two literals, a conjunction of such: closed. One `∀ x : Nat` or one `(m : String)`:
not closed. Closed statements are tests; the census reports them so they can become `example`s. -/
meta partial def closedStatement (e : Expr) : MetaM Bool := do
  match e with
  | .mdata _ b => closedStatement b
  | .letE n t v b _ => Meta.withLetDecl n t v fun x => closedStatement (b.instantiate1 x)
  | .forallE n d b bi =>
    if bi == .instImplicit then
      Meta.withLocalDecl n bi d fun x => closedStatement (b.instantiate1 x)
    else if ← Meta.isProp d then
      Meta.withLocalDecl n bi d fun x => closedStatement (b.instantiate1 x)
    else
      return false
  | _ => return true

/-- Per directory: the package theorems whose statements quantify over something, and the names of
those whose statements are closed. Internal and auxiliary names (`_private`, `match_`, `proof_`,
`_tooth`, `_native`) are skipped. -/
meta def theoremCensus : MetaM (Array (Name × Nat × Array Name)) := do
  let env ← getEnv
  let mut acc : NameMap (Nat × Array Name) := {}
  for (constant, info) in env.constants.map₁.toList do
    let .thmInfo _ := info | continue
    if constant.isInternal || constant.isInternalDetail then continue
    if constant.components.any (fun c => c == `_tooth || c == `_native) then continue
    let some module := packageModule? env constant | continue
    let dir := directoryOf module
    let (universal, closed) := acc.getD dir (0, #[])
    if ← closedStatement info.type then
      acc := acc.insert dir (universal, closed.push constant)
    else
      acc := acc.insert dir (universal + 1, closed)
  let rows := acc.toList.toArray.map fun (d, (u, c)) => (d, u, c.qsort (·.toString < ·.toString))
  return rows.qsort (fun a b => a.1.toString < b.1.toString)

elab "#assert_axioms_tree" : command => do
  let env ← getEnv
  let mut compiledByDir : NameMap Nat := {}
  let mut overrides := 0
  let mut offenders : Array (Name × List Name) := #[]
  for (constant, info) in env.constants.map₁.toList do
    let some module := packageModule? env constant | continue
    if info matches .axiomInfo _ then
      unless isCompilerTrust constant do offenders := offenders.push (constant, [constant])
      continue
    let axioms ← liftCoreM <| collectAxioms constant
    let outside := axioms.toList.filter (fun axiomName => !standard.contains axiomName)
    if outside.isEmpty then continue
    if outside.all isCompilerTrust then
      let dir := directoryOf module
      compiledByDir := compiledByDir.insert dir (compiledByDir.getD dir 0 + 1)
    else if isComputedFieldOverride info constant outside then overrides := overrides + 1
    else offenders := offenders.push (constant, outside)
  unless offenders.isEmpty do
    throwError m!"#assert_axioms_tree: {offenders.size} package constants rest on axioms outside the standard three and the compiler trust (first 20): {offenders.toList.take 20}"
  let compiled := compiledByDir.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
    |>.map (fun (d, n) => m!"{d} {n}")
  logInfo m!"#assert_axioms_tree: no package constant rests on sorryAx or a declared axiom; compiled trust (native_decide/bv_decide, each re-run by #assert_compiled) by directory: {MessageData.joinSep compiled.toList m!", "}; computed_fields overrides (lcProof, compiled code only): {overrides}"

end Obend.AssertAxioms

end
