module
public import Lean

/-!
`#tooth T by mutation f := value` kernel-checks the *stored* proof of `T`, not a
newly elaborated tactic script. A successful command reports a rejected proof in
T's dependency closure. It does not claim that the mutated proposition is false.

Only safe definitions can be mutated. Affected definitions, opaque constants and
theorems are cloned under fresh names; affected inductives/constructors/recursors
are refused. Hidden module bodies are refused: use `import all` for the relevant
imports (or put the command beside the theorem). No declaration is overwritten,
no axiom is introduced, and no scratch declaration survives the command.
-/

public section
namespace Obend.Tactic.Tooth
open Lean Elab Command

private meta def exprDeps (e : Expr) : CoreM NameSet := do
  let refs ← IO.mkRef ({} : NameSet)
  e.forEach fun e => do
    match e with
    | .const n _ | .proj n .. => refs.modify (·.insert n)
    | _ => pure ()
  refs.get

/-- Includes proof bodies, opaque bodies, and inductive declaration groups. -/
private meta def deps (info : ConstantInfo) (mutation : Name) : CoreM NameSet := do
  let mut ds ← exprDeps info.type
  -- The old implementation of the mutated definition is not needed by the
  -- experiment. Replacement dependencies are added separately below.
  if info.name != mutation then
    if let some value := info.value? (allowOpaque := true) then
      ds := ds ++ (← exprDeps value)
  match info with
  | .inductInfo v => ds := ds ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => ds := ds.insert v.induct
  | .recInfo v => ds := ds ++ .ofList v.all
  | _ => pure ()
  return ds

private meta def getInfo (env : Environment) (n : Name) (mutation : Option Name := none) : CoreM ConstantInfo := do
  let some info := env.find? n
    | throwError "#tooth: missing dependency {n}; use `import all` to make its body available"
  if n == ``sorryAx then
    throwError "#tooth: sorryAx is not supported"
  if let .axiomInfo _ := info then
    if getOriginalConstKind? env n != some .axiom then
      -- Imported module order is topological. A declaration from a strictly
      -- earlier module cannot depend on a definition introduced later. Its
      -- hidden body can therefore be reused without trusting a mutated proof.
      let earlier := match mutation with
        | none => false
        | some m => match env.getModuleIdxFor? n, env.getModuleIdxFor? m with
          | some ni, some mi => ni.toNat < mi.toNat
          | some _, none => true
          | _, _ => false
      unless earlier do
        throwError "#tooth: hidden body for {n}; use `import all` for its module"
  return info

private meta def graph (env : Environment) (target mutation : Name) (value : Expr) :
    CoreM (NameMap NameSet) := do
  let replacementDeps ← exprDeps value
  let mut todo := [target, mutation] ++ replacementDeps.toList
  let mut result : NameMap NameSet := {}
  while !todo.isEmpty do
    let n :: rest := todo | unreachable!
    todo := rest
    if result.contains n then continue
    let info ← getInfo env n (some mutation)
    let mut ds ← deps info mutation
    if n == mutation then ds := ds ++ replacementDeps
    result := result.insert n ds
    todo := ds.toList ++ todo
  return result

/-- Reverse reachability includes dependencies through *proofs*, even when their
statements do not mention the mutation. Unaffected declarations can be reused. -/
private meta def affected (g : NameMap NameSet) (mutation : Name) : NameSet := Id.run do
  let mut parents : NameMap NameSet := {}
  for (n, ds) in g do
    for d in ds do
      parents := parents.insert d ((parents.getD d {}).insert n)
  let mut seen : NameSet := {}
  let mut todo := [mutation]
  while !todo.isEmpty do
    let n :: rest := todo | unreachable!
    todo := rest
    if seen.contains n then continue
    seen := seen.insert n
    todo := (parents.getD n {}).toList ++ todo
  return seen

private meta partial def orderVisit (g : NameMap NameSet) (changed : NameSet)
    (n : Name) (visiting done_ : NameSet) (out : Array Name) :
    CoreM (NameSet × Array Name) := do
  if done_.contains n then return (done_, out)
  if visiting.contains n then
    throwError "#tooth: unsupported cyclic replacement/dependency at {n}"
  let mut done_ := done_
  let mut out := out
  for d in g.getD n {} do
    if changed.contains d then
      (done_, out) ← orderVisit g changed d (visiting.insert n) done_ out
  return (done_.insert n, out.push n)

private meta def rewrite (names : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => names.find? n |>.map (fun n => .const n us)
    | .proj n i e => names.find? n |>.map (fun n => .proj n i (rewriteBody e))
    | _ => none
where
  -- Affected structures are rejected before replay, so the projection case is
  -- defensive; ordinary projection operands still need the constant rewrite.
  rewriteBody e := e.replace fun
    | .const n us => names.find? n |>.map (fun n => .const n us)
    | _ => none

private meta def clone (info : ConstantInfo) (names : NameMap Name)
    (mutation : Name) (replacement : Option Expr) : CoreM Declaration := do
  let n := names.getD info.name info.name
  let ty := rewrite names info.type
  match info with
  | .defnInfo v =>
    unless v.safety == .safe do
      throwError "#tooth: unsupported unsafe/partial definition {info.name}"
    let value := if info.name == mutation then replacement.getD v.value else v.value
    return .defnDecl { v with name := n, type := ty, value := rewrite names value, all := [n] }
  | .thmInfo v =>
    return .thmDecl { v with name := n, type := ty, value := rewrite names v.value, all := [n] }
  | .opaqueInfo v =>
    if v.isUnsafe then throwError "#tooth: unsupported unsafe opaque constant {info.name}"
    return .opaqueDecl { v with name := n, type := ty, value := rewrite names v.value, all := [n] }
  | _ => throwError "#tooth: unsupported affected declaration {info.name} (expected def/theorem/opaque)"

private meta def declType : Declaration → Expr
  | .defnDecl v => v.type
  | .thmDecl v => v.type
  | .opaqueDecl v => v.type
  | _ => mkSort .zero

/-- Resource failures and scratch plumbing failures are never proof rejection. -/
private meta def proofRejection : Kernel.Exception → Bool
  | .declTypeMismatch .. | .funExpected .. | .typeExpected ..
  | .letTypeMismatch .. | .exprTypeMismatch .. | .appTypeMismatch ..
  | .invalidProj .. => true
  | _ => false

private meta def inScratch (env : Environment) (opts : Options) (m : MessageData) : MessageData :=
  .withContext { env, opts, mctx := {}, lctx := {} } m

/-- Explicitly bypasses the `debug.skipKernelTC` option and asynchronous checking. -/
private meta def addChecked (env : Environment) (decl : Declaration) :
    CoreM (Except Kernel.Exception Environment) := do
  return env.addDeclCore (Core.getMaxHeartbeats (← getOptions)).toUSize decl none (doCheck := true)

private meta def experiment (env : Environment) (target mutation : Name)
    (replacement : Expr) : CoreM MessageData := do
  let opts ← getOptions
  let g ← graph env target mutation replacement
  let changed := affected g mutation
  unless changed.contains target do
    throwError "#tooth: stored proof of {target} still succeeds (no dependency on {mutation})"
  -- Reject the entire unsupported frontier before any proof failure can be
  -- credited; an early lemma failure must not mask a later unsupported replay.
  let scratchPrefix ← mkFreshUserName `_tooth
  let mut names : NameMap Name := {}
  for n in changed do
    names := names.insert n (scratchPrefix ++ n)
  for n in changed do
    discard <| clone (← getInfo env n) names mutation none
  let (_, order) ← orderVisit g changed target {} {} #[]
  -- Detect a replacement that reaches the mutation, even if that dependency is
  -- not part of the original target proof (it is now part of the graph).
  unless order.contains mutation do throwError "#tooth: mutation is outside the proof closure"
  -- Control replay: a renamed ORIGINAL closure must check. Failures here are
  -- reconstruction problems, never evidence that the mutation has a tooth.
  let mut control := env.unlockAsync
  for n in order do
    let decl ← clone (← getInfo env n) names mutation none
    match ← addChecked control decl with
    | .ok next => control := next
    | .error ex =>
      throwError inScratch control opts m!"#tooth: original closure replay failed at {n}; unsupported experiment\n{ex.toMessageData opts}"
  let mut scratch := env.unlockAsync
  for n in order do
    let decl ← clone (← getInfo env n) names mutation (some replacement)
    let ty := declType decl
    -- A broken declaration TYPE is an invalid experiment, not a broken proof.
    match Kernel.check scratch {} ty with
    | .error ex =>
      throwError inScratch scratch opts m!"#tooth: mutated type is ill-formed at {n}\n{ty}\n{ex.toMessageData opts}"
    | .ok sort =>
      if let .thmDecl _ := decl then
        unless sort == mkSort .zero do
          throwError "#tooth: mutated theorem type is not a proposition at {n}"
    match ← addChecked scratch decl with
    | .ok next => scratch := next
    | .error ex =>
      if (decl matches .thmDecl _) && proofRejection ex then
        return inScratch scratch opts m!"#tooth {target}: mutation of {mutation} rejected stored proof at {n}\nfailing goal/type:\n{ty}\nkernel reason:\n{ex.toMessageData opts}"
      throwError inScratch scratch opts m!"#tooth: mutation/reconstruction invalid at {n}; no tooth credited\n{ty}\n{ex.toMessageData opts}"
  throwError "#tooth: stored proof of {target} still succeeds under mutation of {mutation}"

elab "#tooth " target:ident " by " "mutation " mutation:ident " := " replacement:term : command =>
  withoutModifyingEnv do
    let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
    let mutation ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo mutation
    let env := (← getEnv).setExporting false
    let .thmInfo _ ← liftCoreM <| getInfo env target
      | throwError "#tooth: target must be a theorem with an available stored proof"
    let .defnInfo defn ← liftCoreM <| getInfo env mutation
      | throwError "#tooth: mutation must name a definition with an available body"
    unless defn.safety == .safe do
      throwError "#tooth: mutation must name a safe definition"
    let value ← runTermElabM fun _ => Term.withLevelNames defn.levelParams <| Term.withoutErrToSorry do
      let value ← Term.elabTermEnsuringType replacement defn.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasMVar || value.hasFVar || value.hasLooseBVars then
        throwError "#tooth: replacement must be a closed term (abstract all definition arguments)"
      return value
    -- Elaboration may create auxiliary declarations. They live in this command's
    -- saved environment, and are discarded along with the scratch experiment.
    let env := (← getEnv).setExporting false
    let validationName ← liftCoreM <| mkFreshUserName `_toothReplacement
    let validation := Declaration.defnDecl { defn with name := validationName, value, all := [validationName] }
    match ← liftCoreM <| addChecked env.unlockAsync validation with
    | .ok _ => pure ()
    | .error ex => throwError "#tooth: replacement is not kernel-valid at the original type\n{ex.toMessageData (← getOptions)}"
    let result ← liftCoreM <| experiment env target mutation value
    logInfo result

end Obend.Tactic.Tooth
