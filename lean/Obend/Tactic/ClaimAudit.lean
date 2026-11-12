module
/-
# `Obend.Tactic.ClaimAudit` — Kernel `MetaM` / `CommandElabM` Enforcement of the MoA 5 Claim-Contract Laws

Implements the Lean 4 kernel theorem, obligation, hypothesis-vacuity, and statement-succession
auditor directly over `Lean.Environment` and `Lean.ConstantInfo`:

1. **`#audit_claim_contract <ConstName>`**:
   - **Law 1 (`axiomPurity`)**: Inspects transitive `collectAxioms` and original constant kinds;
     refuses `sorryAx`, any custom `axiom`, any `_native`/`ofReduceBool` compiler trust, and any
     declaration whose proof body is hidden behind a module boundary without `import all`.
   - **Law 2 (`earnedProof` — Anti-Projection-Cosplay)**: Inspects the kernel `Expr` proof body
     (stripping `.lam`/`.letE`/`.mdata` binders, plus auditing obligation constructor fields and
     1-hop thin wrappers); refuses 1-step projection/determinism cosplay (`Eq.refl`, `rfl`,
     `congrArg`, `congrFun`, `congr`, `And.left`, `And.right`, `Prod.fst`, `Prod.snd`, `True.intro`,
     `trivial`, `Bool.and_eq_true` projections, bare `.bvar` identity, and `Eq.rec`+`Eq.refl`).
   - **Law 3 (`nonDegenerateCarrier`)**: Inspects typeclass/theorem carrier arguments, premise
     binders, and predicate lambdas; refuses `Unit`, `PUnit`, `Empty`, `PEmpty`, uninhabited
     binders `(x : Empty)` / `(h : False)`, and constant vacuous fragments `fun _ => False`.
2. **`#verify_non_vacuous <HypPred> by <WitnessTerm>`**:
   - **Law 4 (`modelInhabited`)**: Elaborates and kernel-checks (`addDeclCore ... (doCheck := true)`)
     that a hardness or well-formedness hypothesis `H` is constructively inhabited on closed,
     non-degenerate model parameters with zero `sorryAx` or custom axioms (killing `ModuleSISHard = False`!).
3. **`#verify_judge_succession <NewThm> implies <OldThm> via <BridgeTerm>`**:
   - **Law 5 (`judgeSuccession` / `judge-succession@1`)**: Elaborates and kernel-checks that the
     statement of `NewThm` logically entails the statement of `OldThm` (`P_new → P_old`), enforcing
     independence from `OldThm` itself and genuine consumption of the `P_new` hypothesis so locked
     Statement Cards can never be silently weakened during proof repair.
-/
public import Lean
public meta import Lean

public section
namespace Obend.Tactic.ClaimAudit

set_option autoImplicit false

/-! ## 1. Structured Claim-Contract Law & Verdict Algebra -/

/-- Enumeration of the MoA Five Claim-Contract Laws enforced in Lean's kernel. -/
inductive ClaimContractLaw where
  | axiomPurity
  | earnedProof
  | nonDegenerateCarrier
  | modelInhabited
  | judgeSuccession
  deriving DecidableEq, Repr, Inhabited

/-- Human-readable label for each of the 5 Claim-Contract Laws. -/
@[expose] def ClaimContractLaw.label : ClaimContractLaw → String
  | .axiomPurity          => "Law 1 (Axiom Purity)"
  | .earnedProof          => "Law 2 (Earned Proof / Anti-Projection-Cosplay)"
  | .nonDegenerateCarrier => "Law 3 (Non-Degenerate Carrier)"
  | .modelInhabited       => "Law 4 (Model-Inhabited / Non-Vacuous Hypothesis)"
  | .judgeSuccession      => "Law 5 (judge-succession@1 Non-Weakening)"

/-- A concrete Claim-Contract Law violation recorded by the kernel auditor. -/
structure ClaimViolation where
  law    : ClaimContractLaw
  target : Lean.Name
  detail : String
  deriving DecidableEq, Repr, Inhabited

/-- Structured audit outcome returned by `MetaM` / `CommandElabM` claim-contract checks. -/
inductive AuditVerdict where
  | passed (target : Lean.Name) (summary : String)
  | refused (target : Lean.Name) (violations : List ClaimViolation)
  deriving DecidableEq, Repr, Inhabited

meta instance : Inhabited ClaimContractLaw := ⟨.axiomPurity⟩
meta instance : Inhabited ClaimViolation := ⟨⟨.axiomPurity, .anonymous, ""⟩⟩
meta instance : Inhabited AuditVerdict := ⟨.passed .anonymous ""⟩

/-- Boolean acceptance predicate on `AuditVerdict`. -/
@[expose] def AuditVerdict.isOk : AuditVerdict → Bool
  | .passed _ _  => true
  | .refused _ _ => false

/-- Extract recorded violations from an `AuditVerdict`. -/
@[expose] def AuditVerdict.violations : AuditVerdict → List ClaimViolation
  | .passed _ _   => []
  | .refused _ vs => vs

/-- Check whether an `AuditVerdict` failed a specific `ClaimContractLaw`. -/
@[expose] def AuditVerdict.violatesLaw (v : AuditVerdict) (law : ClaimContractLaw) : Bool :=
  v.violations.any (fun viol => viol.law == law)

theorem AuditVerdict.isOk_iff (v : AuditVerdict) :
    v.isOk = true ↔ ∃ tgt summary, v = .passed tgt summary := by
  cases v with
  | passed t s => exact ⟨fun _ => ⟨t, s, rfl⟩, fun _ => rfl⟩
  | refused _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, h⟩; cases h

theorem AuditVerdict.isOk_false_iff (v : AuditVerdict) :
    v.isOk = false ↔ ∃ tgt vs, v = .refused tgt vs := by
  cases v with
  | passed _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, h⟩; cases h
  | refused t vs => exact ⟨fun _ => ⟨t, vs, rfl⟩, fun _ => rfl⟩

/-- Combine a list of violations for `target` into a canonical `AuditVerdict`. -/
@[expose] def AuditVerdict.ofViolations (target : Lean.Name) (okSummary : String) :
    List ClaimViolation → AuditVerdict
  | [] => .passed target okSummary
  | vs => .refused target vs

theorem AuditVerdict.ofViolations_isOk_iff (target : Lean.Name) (okSummary : String)
    (vs : List ClaimViolation) :
    (AuditVerdict.ofViolations target okSummary vs).isOk = true ↔ vs = [] := by
  cases vs <;> simp [AuditVerdict.ofViolations, AuditVerdict.isOk]

-- Inhabitedness witness for `AuditVerdict.isOk`.
example : (AuditVerdict.ofViolations `demo "ok" []).isOk = true := rfl

/-! ## 2. Kernel `MetaM` Inspectors for Laws 1–3 (`auditClaimContract`) -/

open Lean Meta Elab Command Term

/-- The three standard Lean kernel axioms permitted under Law 1 (`axiomPurity`). -/
meta def allowedStandardAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Compiler-trust axioms (`native_decide`, `bv_decide` native trust, `ofReduceBool`, `trustCompiler`). -/
meta def isCompilerTrustAxiom (ax : Name) : Bool :=
  ax.components.any (· == `_native) ||
  ax == `Lean.ofReduceBool ||
  ax == `Lean.trustCompiler

/-- Strip outer `Expr.mdata` wrappers. -/
meta partial def stripMData (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => stripMData inner
  | _ => e

/-- Strip outer `.lam`, `.letE` (substituting non-dependent/small lets), and `.mdata` wrappers. -/
meta partial def stripProofBinders (e : Expr) : Expr :=
  match stripMData e with
  | .lam _ _ body _ => stripProofBinders body
  | .letE _ _ val body _ => stripProofBinders (body.instantiate1 val)
  | core => core

private meta def lawLabelMeta : ClaimContractLaw → String
  | .axiomPurity          => "Law 1 (Axiom Purity)"
  | .earnedProof          => "Law 2 (Earned Proof / Anti-Projection-Cosplay)"
  | .nonDegenerateCarrier => "Law 3 (Non-Degenerate Carrier)"
  | .modelInhabited       => "Law 4 (Model-Inhabited / Non-Vacuous Hypothesis)"
  | .judgeSuccession      => "Law 5 (judge-succession@1 Non-Weakening)"

private meta def mkAuditVerdictMeta (target : Name) (okSummary : String) :
    List ClaimViolation → AuditVerdict
  | [] => .passed target okSummary
  | vs => .refused target vs

/-- Format a list of `ClaimViolation`s for error diagnostics. -/
meta def formatViolations (vs : List ClaimViolation) : String :=
  String.intercalate "\n" <| vs.map fun v =>
    s!"  • [{lawLabelMeta v.law}] on `{v.target}`: {v.detail}"

/-- **Law 1 (`axiomPurity`)**: check transitive axioms and module-boundary body visibility. -/
meta def checkAxiomPurity (fullEnv : Environment) (declName : Name) (info : ConstantInfo) :
    CoreM (List ClaimViolation) :=
  withEnv fullEnv do
    let mut out : List ClaimViolation := []
    if let .axiomInfo _ := info then
      if getOriginalConstKind? fullEnv declName != some .axiom then
        out := out ++ [⟨.axiomPurity, declName,
          s!"proof/definition body of `{declName}` is hidden behind a module boundary; add `import all` to audit it"⟩]
      else
        out := out ++ [⟨.axiomPurity, declName,
          s!"`{declName}` is itself a declared custom `axiom`"⟩]
      return out
    let axs ← collectAxioms declName
    for ax in axs do
      if ax == ``sorryAx then
        out := out ++ [⟨.axiomPurity, declName, "depends on `sorryAx`"⟩]
      else if isCompilerTrustAxiom ax then
        out := out ++ [⟨.axiomPurity, declName,
          s!"depends on compiler-trust axiom `{ax}` (`native_decide` / `ofReduceBool`)"⟩]
      else if !allowedStandardAxioms.contains ax then
        out := out ++ [⟨.axiomPurity, declName,
          s!"depends on non-standard custom axiom `{ax}`"⟩]
    return out

/-- Trivial 1-step reflexivity / congruence / projection / unit-truth cosplay head constants. -/
meta def classifyDirectCosplayHead? (cName : Name) : Option String :=
  if cName == ``Eq.refl || cName == ``rfl || cName == ``HEq.refl || cName == ``Iff.rfl then
    some s!"1-step reflexivity cosplay (`{cName}`)"
  else if cName == ``congrArg || cName == ``congrFun || cName == ``congr then
    some s!"1-step determinism/congruence cosplay (`{cName}`)"
  else if cName == ``And.left || cName == ``And.right ||
          cName == ``Prod.fst || cName == ``Prod.snd ||
          cName == ``PProd.fst || cName == ``PProd.snd ||
          cName == ``Subtype.property || cName == ``Subtype.val then
    some s!"1-step projection cosplay (`{cName}`)"
  else if cName == ``True.intro || cName == ``trivial || cName == ``Subsingleton.elim then
    some s!"1-step trivial unit/subsingleton cosplay (`{cName}`)"
  else
    none

/-- Pure character-list substring check (Std-independent). -/
private meta def charsContainsSublist : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | h :: t, n => n.isPrefixOf (h :: t) || charsContainsSublist t n

private meta def hasSubstr (haystack needle : String) : Bool :=
  charsContainsSublist haystack.toList needle.toList

/-- Whether a structure name represents an obligation/ledger/contract bundle whose `Prop` fields
    must ALL be earned (as opposed to auxiliary monotonicity fields on `Judge`). -/
meta def isObligationStructName (sName : Name) : Bool :=
  let s := sName.toString
  s.endsWith "Obligations" || hasSubstr s "HypothesisLedger" ||
  s.endsWith "Ledger" || s.endsWith "Contract"

/-- Whether a specific named field on a non-`*Obligations` structure (such as `Judge` or `SilverWorkflow`)
    is a core soundness obligation field that must be earned. -/
meta def isCoreSoundnessFieldName (fName : Name) : Bool :=
  let s := fName.getString!
  s == "sound" || s == "step_sound" || s == "silverSound" ||
  s.endsWith "_sound" || s.endsWith "Sound"

/-- Inspect a kernel proof expression `e` for Law 2 (`earnedProof`) anti-projection-cosplay violations. -/
meta partial def detectCosplayInProofExpr? (fullEnv : Environment) (depth : Nat) (e : Expr) :
    MetaM (Option String) := do
  let core := stripProofBinders e
  match core with
  | .bvar _ =>
    return some "1-step bare hypothesis identity (`fun h => h`)"
  | .proj sName idx inner =>
    if sName == ``And || sName == ``Prod || sName == ``PProd ||
       sName == ``Subtype || sName == ``Iff then
      return some s!"1-step structure projection cosplay (`.proj {sName} {idx}`)"
    if (stripProofBinders inner).isBVar then
      return some s!"1-step hypothesis field projection (`.proj {sName} {idx}`)"
    return none
  | _ =>
    let fn := stripMData core.getAppFn
    let args := core.getAppArgs
    let some cName := fn.constName? | return none
    if let some directReason := classifyDirectCosplayHead? cName then
      return some directReason
    -- `id x` or `Function.const _ x`
    if (cName == ``id || cName == ``Function.const) && !args.isEmpty then
      return (← detectCosplayInProofExpr? fullEnv depth args.back!)
    -- `Iff.mp` / `Iff.mpr` / `Eq.mp` / `Eq.mpr` wrapping `Bool.and_eq_true`
    if cName == ``Iff.mp || cName == ``Iff.mpr || cName == ``Eq.mp || cName == ``Eq.mpr then
      let used := core.getUsedConstantsAsSet
      if used.contains ``Bool.and_eq_true || used.contains ``Bool.and_eq_true_iff then
        return some "1-step `Bool.and_eq_true` boolean-arm unpacking cosplay"
      if !args.isEmpty then
        if (stripProofBinders args.back!).isBVar && args.size >= 2 then
          if let some innerReason ← detectCosplayInProofExpr? fullEnv depth args[args.size - 2]! then
            return some innerReason
    -- `Eq.rec` / `Eq.ndrec` / `Eq.casesOn` wrapping `Eq.refl` (`by cases h; rfl` determinism cosplay!)
    if (cName == ``Eq.rec || cName == ``Eq.ndrec || cName == ``Eq.casesOn) && args.size >= 4 then
      -- Minor premise in `Eq.ndrec` / `Eq.rec` / `Eq.casesOn` is `args[3]!`
      if let some baseReason ← detectCosplayInProofExpr? fullEnv depth args[3]! then
        return some s!"`{cName}` determinism cosplay ({baseReason}, e.g. `cases h; rfl`)"
    -- `And.casesOn` / `And.rec` / `Prod.casesOn` destructuring directly to a bound variable / cosplay
    if (cName == ``And.casesOn || cName == ``And.rec ||
        cName == ``Prod.casesOn || cName == ``Prod.rec) && !args.isEmpty then
      for arg in args do
        if (stripMData arg).isLambda then
          if let some armReason ← detectCosplayInProofExpr? fullEnv depth arg then
            return some s!"`{cName}` projection cosplay ({armReason})"
    -- Audit structure/class constructor obligation fields (e.g. `instance : MyObligations C where ...`)
    if depth > 0 then
      if let some (.ctorInfo cval) := fullEnv.find? cName then
        let structName := cval.induct
        let auditAllPropFields := isObligationStructName structName
        let fieldNames :=
          if isStructure fullEnv structName then getStructureFields fullEnv structName else #[]
        for fIdx in [0 : cval.numFields] do
          let argPos := cval.numParams + fIdx
          if h : argPos < args.size then
            let fExpr := args[argPos]
            let fName := if fIdx < fieldNames.size then fieldNames[fIdx]! else Name.mkSimple s!"field_{fIdx}"
            if auditAllPropFields || isCoreSoundnessFieldName fName then
              let isProofField ← try Meta.isProp (← inferType fExpr) catch _ => pure false
              if isProofField then
                if let some fReason ← detectCosplayInProofExpr? fullEnv (depth - 1) fExpr then
                  return some s!"field `{fName}` of `{structName}` uses {fReason}"
      -- Smart constructor `Judge.ofSoundCheck`: `step_sound` is argument index 5
      if (cName.getString! == "ofSoundCheck") && args.size >= 6 then
        if let some sReason ← detectCosplayInProofExpr? fullEnv (depth - 1) args[5]! then
          return some s!"`ofSoundCheck` `step_sound` argument uses {sReason}"
      -- Unfold 1-hop auxiliary `._proof_k` or thin wrapper constants when `core` has no other work
      if let some subInfo := fullEnv.find? cName then
        let isAuxProof := cName.components.any fun c =>
          c.toString.startsWith "_proof_" || c.toString.startsWith "proof_"
        if isAuxProof || (depth >= 2 && (subInfo matches .thmInfo _)) then
          if let some subVal := subInfo.value? (allowOpaque := true) then
            -- Only treat as thin wrapper if `subVal` itself is directly cosplay (no recursors!)
            let subConsts := subVal.getUsedConstantsAsSet
            let hasInductiveRec := subConsts.toList.any fun k =>
              k != ``Eq.rec && k != ``Eq.ndrec && k != ``Eq.casesOn &&
              k != ``And.rec && k != ``And.casesOn &&
              (k.getString! == "rec" || k.getString! == "casesOn" || k.getString! == "brecOn")
            if !hasInductiveRec then
              if let some wReason ← detectCosplayInProofExpr? fullEnv (depth - 1) subVal then
                return some s!"delegates directly to thin cosplay wrapper `{cName}` ({wReason})"
    return none

/-- Degenerate carrier type names forbidden by Law 3 (`nonDegenerateCarrier`). -/
meta partial def isDegenerateCarrierTypeExpr (e : Expr) : Bool :=
  let e := stripMData e
  let fn := stripMData e.getAppFn
  let args := e.getAppArgs
  if let some cName := fn.constName? then
    if cName == ``Unit || cName == ``PUnit || cName == ``Empty ||
       cName == ``PEmpty || cName == ``False || cName == ``True then
      true
    else if (cName == ``ULift || cName == ``PLift) && args.size >= 1 then
      isDegenerateCarrierTypeExpr args[0]!
    else if cName == ``Prod && args.size == 2 then
      isDegenerateCarrierTypeExpr args[0]! && isDegenerateCarrierTypeExpr args[1]!
    else
      false
  else
    false

/-- Detect constant uninhabited predicate lambdas `fun _ => False` / `fun _ => Empty` (`Fragment := fun _ => False`). -/
meta partial def containsConstFalseLambda (e : Expr) : Bool :=
  let e := stripMData e
  let rec isConstEmptyBody (b : Expr) : Bool :=
    match stripMData b with
    | .lam _ _ inner _ => isConstEmptyBody inner
    | .const c _ => c == ``False || c == ``Empty || c == ``PEmpty
    | _ => false
  match e with
  | .lam _ _ body _ =>
    if isConstEmptyBody body then true else containsConstFalseLambda body
  | .forallE _ d b _ => containsConstFalseLambda d || containsConstFalseLambda b
  | .letE _ t v b _ =>
    containsConstFalseLambda t || containsConstFalseLambda v || containsConstFalseLambda b
  | .app f a => containsConstFalseLambda f || containsConstFalseLambda a
  | .proj _ _ s => containsConstFalseLambda s
  | _ => false

/-- **Law 3 (`nonDegenerateCarrier`)**: inspect binders, target carrier arguments, and `fun _ => False` fragments. -/
meta partial def checkNonDegenerateCarrier (declName : Name) (info : ConstantInfo) :
    MetaM (List ClaimViolation) := do
  let mut out : List ClaimViolation := []
  -- 1. Walk `forallE` binders and conclusion of `info.type`
  let rec walkTelescope (ty : Expr) : MetaM (List ClaimViolation) := do
    let ty := stripMData ty
    match ty with
    | .forallE bName dom body bi =>
      let mut errs : List ClaimViolation := []
      let domClean := stripMData dom
      if domClean.isConstOf ``Empty || domClean.isConstOf ``PEmpty || domClean.isConstOf ``False then
        errs := errs ++ [⟨.nonDegenerateCarrier, declName,
          s!"vacuous uninhabited binder `({bName} : {domClean})` in statement signature"⟩]
      if bi == .instImplicit then
        for arg in domClean.getAppArgs do
          let isTypeArg ← try pure (← inferType arg).isSort catch _ => pure false
          if isTypeArg && isDegenerateCarrierTypeExpr arg then
            errs := errs ++ [⟨.nonDegenerateCarrier, declName,
              s!"typeclass binder `{domClean}` instantiated at degenerate carrier `{arg}`"⟩]
      let rest ← Meta.withLocalDecl bName bi dom fun x => walkTelescope (body.instantiate1 x)
      return errs ++ rest
    | .letE bName t v body _ =>
      Meta.withLetDecl bName t v fun x => walkTelescope (body.instantiate1 x)
    | concl =>
      let mut errs : List ClaimViolation := []
      if concl.isConstOf ``True then
        errs := errs ++ [⟨.nonDegenerateCarrier, declName,
          "trivial conclusion `True` carries zero semantic constraint"⟩]
      for arg in concl.getAppArgs do
        let isTypeArg ← try pure (← inferType arg).isSort catch _ => pure false
        if isTypeArg && isDegenerateCarrierTypeExpr arg then
          errs := errs ++ [⟨.nonDegenerateCarrier, declName,
            s!"conclusion `{concl.getAppFn}` instantiated at degenerate carrier `{arg}`"⟩]
      return errs
  out := out ++ (← walkTelescope info.type)
  -- 2. Scan `info.type` and `info.value` for `fun _ => False` / `Fragment := fun _ => False`
  if containsConstFalseLambda info.type then
    out := out ++ [⟨.nonDegenerateCarrier, declName,
      "statement signature contains constant uninhabited predicate `fun _ => False` / `fun _ => Empty`"⟩]
  if let some val := info.value? (allowOpaque := true) then
    if containsConstFalseLambda val then
      out := out ++ [⟨.nonDegenerateCarrier, declName,
        "body/instance contains constant uninhabited predicate `fun _ => False` (e.g. `Fragment := fun _ => False`)"⟩]
  return out

/-- Full structured kernel audit of `<ConstName>` across Laws 1, 2, and 3. -/
meta def auditClaimContract (env : Environment) (declName : Name) : MetaM AuditVerdict := do
  let fullEnv := env.setExporting false
  withEnv fullEnv do
    let some info := fullEnv.find? declName
      | return .refused declName [⟨.axiomPurity, declName, s!"constant `{declName}` not found in environment"⟩]
    let mut violations ← checkAxiomPurity fullEnv declName info
    if let some val := info.value? (allowOpaque := true) then
      if let some cosplayReason ← detectCosplayInProofExpr? fullEnv 2 val then
        violations := violations ++ [⟨.earnedProof, declName, cosplayReason⟩]
    violations := violations ++ (← checkNonDegenerateCarrier declName info)
    return mkAuditVerdictMeta declName
      s!"`{declName}` passed Axiom Purity, Earned Proof, and Non-Degenerate Carrier kernel audits"
      violations

/-- **`#audit_claim_contract <ConstName>`**: kernel-audits `<ConstName>` against Axiom Purity (Law 1),
    Earned Proof / Anti-Projection-Cosplay (Law 2), and Non-Degenerate Carrier / Fragment (Law 3). -/
elab "#audit_claim_contract " id:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let verdict ← liftTermElabM <| auditClaimContract env declName
  match verdict with
  | .passed _ summary =>
    logInfo m!"[PASS] #audit_claim_contract: {summary}"
  | .refused _ vs =>
    throwError m!"#audit_claim_contract refused `{declName}` ({vs.length} violation(s)):\n{formatViolations vs}"

/-! ## 3. Law 4 (`modelInhabited`): `#verify_non_vacuous <HypPred> by <WitnessTerm>` -/

/-- Explicitly kernel-typecheck a candidate theorem `(ty, val)` in a scratch environment (`doCheck := true`)
    and verify Law 1 Axiom Purity on the checked declaration. -/
meta def kernelCheckScratchTheorem (targetLabel : Name) (law : ClaimContractLaw)
    (ty val : Expr) : MetaM (List ClaimViolation) := do
  let env ← getEnv
  let fullEnv := env.setExporting false
  let opts ← getOptions
  let ty ← instantiateMVars ty
  let val ← instantiateMVars val
  if ty.hasExprMVar || val.hasExprMVar then
    return [⟨law, targetLabel, "elaborated witness/bridge still contains unsolved metavariables"⟩]
  if ty.hasFVar || val.hasFVar then
    return [⟨law, targetLabel, "elaborated witness/bridge contains free local variables (must be closed)"⟩]
  -- Collect used universe level parameters across `ty` and `val`
  let lparams := (collectLevelParams (collectLevelParams {} ty) val).params.toList
  let scratchName ← mkFreshUserName `_claim_audit_kernel
  let decl : Declaration := .thmDecl {
    name := scratchName
    levelParams := lparams
    type := ty
    value := val
  }
  match fullEnv.unlockAsync.addDeclCore
      (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize decl none (doCheck := true) with
  | .error kex =>
    let msg ← (kex.toMessageData opts).toString
    return [⟨law, targetLabel, s!"Lean kernel rejected proof term: {msg}"⟩]
  | .ok checkedEnv =>
    let some scratchInfo := checkedEnv.find? scratchName
      | return [⟨law, targetLabel, "internal error: scratch declaration missing after addDeclCore"⟩]
    let axViolations ← checkAxiomPurity checkedEnv scratchName scratchInfo
    return axViolations.map fun v => { v with law := law, target := targetLabel }

/-- Wrap an `n`-ary predicate `H : ∀ (x₁ : A₁) ... (xₙ : Aₙ), Prop` in `∃ x₁ ... xₙ, H x₁ ... xₙ`. -/
meta partial def mkNestedExistsForPred (predExpr predTy : Expr) : MetaM Expr := do
  let predTy ← whnf predTy
  match predTy with
  | .forallE bName dom body bi =>
    if dom.isProp && !(body.hasLooseBVar 0) then
      -- Note: if `dom` is a data/parameter binder, wrap in `Exists`
      let lam ← Meta.withLocalDecl bName bi dom fun x => do
        let sub ← mkNestedExistsForPred (mkApp predExpr x) (body.instantiate1 x)
        mkLambdaFVars #[x] sub
      mkAppM ``Exists #[lam]
    else
      let lam ← Meta.withLocalDecl bName bi dom fun x => do
        let sub ← mkNestedExistsForPred (mkApp predExpr x) (body.instantiate1 x)
        mkLambdaFVars #[x] sub
      mkAppM ``Exists #[lam]
  | _ =>
    return predExpr

/-- Check whether `e` is a degenerate trivial value (`Unit.unit` or `PUnit.unit`). -/
meta def isDegenerateModelValue (e : Expr) : Bool :=
  let fn := (stripMData e).getAppFn
  fn.isConstOf ``Unit.unit || fn.isConstOf ``PUnit.unit

/-- Audit that `hypStx` is non-vacuously inhabited via `witStx` (Law 4: `modelInhabited`). -/
meta def verifyNonVacuousAudit (hypStx witStx : Syntax) : TermElabM AuditVerdict := do
  let hypExpr ← Term.elabTermAndSynthesize hypStx none
  let hypExpr ← instantiateMVars hypExpr
  let hypTy ← instantiateMVars (← inferType hypExpr)
  let targetLabel := (stripMData hypExpr.getAppFn).constName?.getD `_non_vacuous_hyp
  -- Reject syntactic `False` or `fun _ => False`
  if (stripMData hypExpr).isConstOf ``False || containsConstFalseLambda hypExpr then
    return .refused targetLabel [⟨.modelInhabited, targetLabel,
      s!"hypothesis `{hypExpr}` is syntactically uninhabited (`False` / `fun _ => False`)"⟩]
  if let some cName := (stripMData hypExpr).constName? then
    let fullEnv := (← getEnv).setExporting false
    if let some cInfo := fullEnv.find? cName then
      if let some cVal := cInfo.value? (allowOpaque := true) then
        if (stripMData cVal).isConstOf ``False || containsConstFalseLambda cVal then
          return .refused targetLabel [⟨.modelInhabited, targetLabel,
            s!"hypothesis `{cName}` unfolds directly to uninhabited `False` / `fun _ => False`"⟩]
  -- Case 1: `hypExpr` is already a `Prop` (`hypTy` is `Prop`)
  if ← Meta.isProp hypExpr then
    let redHyp ← whnf hypExpr
    if (stripMData redHyp).isConstOf ``False then
      return .refused targetLabel [⟨.modelInhabited, targetLabel,
        s!"hypothesis `{hypExpr}` reduces in WHNF to `False`"⟩]
    let witExpr ← try
      Term.withoutErrToSorry do
        let w ← Term.elabTermEnsuringType witStx (some hypExpr)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars w
    catch ex =>
      let msg ← ex.toMessageData.toString
      return .refused targetLabel [⟨.modelInhabited, targetLabel,
        s!"witness failed to inhabit `{hypExpr}`: {msg}"⟩]
    let kErrs ← kernelCheckScratchTheorem targetLabel .modelInhabited hypExpr witExpr
    return mkAuditVerdictMeta targetLabel
      s!"hypothesis `{hypExpr}` is kernel-verified non-vacuous" kErrs
  -- Case 2: `hypExpr` is an `n`-ary predicate `A₁ → ... → Aₙ → Prop`
  let existsTy ← mkNestedExistsForPred hypExpr hypTy
  -- Support Style A (`⟨modelParam, hProof⟩ : ∃ x, H x`) OR Style B (`hProof : H modelParam`)
  let saved ← saveState
  let styleA? : Option (Expr × Expr) ← try
    Term.withoutErrToSorry do
      let w ← Term.elabTermEnsuringType witStx (some existsTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      let w ← instantiateMVars w
      if (stripMData w.getAppFn).isConstOf ``Exists.intro && w.getAppArgs.size >= 4 then
        let modelArg := w.getAppArgs[2]!
        if isDegenerateModelValue modelArg then
          throwError "degenerate Unit model witness"
      pure (some (existsTy, w))
  catch _ =>
    restoreState saved
    pure none
  if let some (chkTy, chkVal) := styleA? then
    let kErrs ← kernelCheckScratchTheorem targetLabel .modelInhabited chkTy chkVal
    return mkAuditVerdictMeta targetLabel
      s!"predicate `{hypExpr}` is kernel-verified inhabited (`{chkTy}`)" kErrs
  -- Style B: direct proof `w : H m₁ ... mₙ`
  try
    Term.withoutErrToSorry do
      let w ← Term.elabTermAndSynthesize witStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let w ← instantiateMVars w
      let wTy ← instantiateMVars (← inferType w)
      let wHead := stripMData wTy.getAppFn
      let hHead := stripMData hypExpr.getAppFn
      let matchesPred ← withoutModifyingState (isDefEq wHead hHead)
      if !matchesPred then
        return .refused targetLabel [⟨.modelInhabited, targetLabel,
          s!"witness has type `{wTy}`, which neither inhabits `{existsTy}` nor applies `{hypExpr}`"⟩]
      for mArg in wTy.getAppArgs do
        if isDegenerateModelValue mArg then
          return .refused targetLabel [⟨.modelInhabited, targetLabel,
            s!"model parameter `{mArg}` is degenerate (`Unit`)"⟩]
      let kErrs ← kernelCheckScratchTheorem targetLabel .modelInhabited wTy w
      return mkAuditVerdictMeta targetLabel
        s!"predicate `{hypExpr}` is kernel-verified inhabited via `{wTy}`" kErrs
  catch ex =>
    let msg ← ex.toMessageData.toString
    return .refused targetLabel [⟨.modelInhabited, targetLabel,
      s!"witness failed to inhabit `{existsTy}`: {msg}"⟩]

/-- **`#verify_non_vacuous <HypPred> by <WitnessTerm>`**:
    Kernel-checks that a hardness or well-formedness hypothesis `HypPred` is constructively
    inhabited on concrete non-degenerate parameters (killing `ModuleSISHard = False` vacuity). -/
elab "#verify_non_vacuous " hyp:term " by " wit:term : command => do
  let verdict ← liftTermElabM <| verifyNonVacuousAudit hyp wit
  match verdict with
  | .passed _ summary =>
    logInfo m!"[PASS] #verify_non_vacuous: {summary}"
  | .refused tgt vs =>
    throwError m!"#verify_non_vacuous refused `{tgt}`:\n{formatViolations vs}"

/-! ## 4. Law 5 (`judgeSuccession`): `#verify_judge_succession <New> implies <Old> via <Bridge>` -/

/-- Extract the propositional claim `P : Prop` from either a `theorem name : P` or a Statement Card
    `def CardName : Prop := P`, instantiating universe parameters consistently. -/
meta def extractStatementCardProp (fullEnv : Environment) (declName : Name) :
    MetaM (Except String Expr) := do
  let some info := fullEnv.find? declName
    | return .error s!"constant `{declName}` not found in environment"
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let instTy := info.type.instantiateLevelParams info.levelParams lvls
  if ← Meta.isProp instTy then
    return .ok instTy
  if instTy.isProp then
    if let some val := info.value? (allowOpaque := true) then
      return .ok (val.instantiateLevelParams info.levelParams lvls)
    return .error s!"Statement Card `{declName} : Prop` is opaque; add `import all` or `@[expose]`"
  return .error s!"`{declName}` is neither a `theorem` (`: P`) nor a `Prop` Statement Card (`: Prop`)"

/-- Check whether `targetConst` occurs anywhere in the transitive constant closure of `rootExpr`. -/
meta def exprTransitivelyReferences (fullEnv : Environment) (rootExpr : Expr) (targetConst : Name) : Bool := Id.run do
  let initSet := rootExpr.getUsedConstantsAsSet
  if initSet.contains targetConst then return true
  let mut queue : Array Name := initSet.toArray
  let mut visited : NameSet := initSet
  let mut head : Nat := 0
  while h : head < queue.size do
    let cur := queue[head]
    head := head + 1
    if let some info := fullEnv.find? cur then
      let mut deps := info.type.getUsedConstantsAsSet
      if let some v := info.value? (allowOpaque := true) then
        deps := deps ++ v.getUsedConstantsAsSet
      if deps.contains targetConst then return true
      for d in deps.toList do
        if !visited.contains d then
          visited := visited.insert d
          queue := queue.push d
  return false

/-- Verify that `bridgeExpr : P_new → P_old` genuinely consumes its `hNew : P_new` assumption
    (rejecting constant bridges `fun _hNew => independentProof` when `NewThm` was weakened to `True`). -/
meta def bridgeConsumesNewAssumption (pNew bridgeExpr : Expr) : MetaM Bool :=
  Meta.withLocalDecl `_hNewAudit .default pNew fun hNewFVar => do
    let applied ← Core.betaReduce (mkApp bridgeExpr hNewFVar)
    let zetaClean ← Meta.zetaReduce applied
    -- Also unfold top-level `id` or `Function.const`
    let norm :=
      let fn := stripMData zetaClean.getAppFn
      let args := zetaClean.getAppArgs
      if fn.isConstOf ``Function.const && args.size == 4 then args[2]!
      else if fn.isConstOf ``id && args.size == 2 then args[1]!
      else zetaClean
    return norm.containsFVar hNewFVar.fvarId!

/-- Structured `TermElabM` audit for Law 5 (`judge-succession@1`: `NewThm → OldThm`). -/
meta def verifyJudgeSuccessionAudit (newName oldName : Name) (bridgeStx : Syntax) :
    TermElabM AuditVerdict := do
  let fullEnv := (← getEnv).setExporting false
  withEnv fullEnv do
    let pNew ← match ← extractStatementCardProp fullEnv newName with
      | .ok p => pure p
      | .error e => return .refused newName [⟨.judgeSuccession, newName, e⟩]
    let pOld ← match ← extractStatementCardProp fullEnv oldName with
      | .ok p => pure p
      | .error e => return .refused newName [⟨.judgeSuccession, newName, e⟩]
    let impTy := Expr.forallE `_hNew pNew pOld .default
    let bridgeExpr ← try
      Term.withoutErrToSorry do
        let b ← Term.elabTermEnsuringType bridgeStx (some impTy)
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars b
    catch ex =>
      let msg ← ex.toMessageData.toString
      return .refused newName [⟨.judgeSuccession, newName,
        s!"bridge term failed to prove `{newName} → {oldName}` (`{impTy}`): {msg}"⟩]
    let mut violations : List ClaimViolation := []
    -- Guard 1: Bridge must NOT cite `OldThm` itself (when `OldThm` is a theorem, citing it bypasses `P_new`!)
    if let some oldInfo := fullEnv.find? oldName then
      if (← Meta.isProp oldInfo.type) && exprTransitivelyReferences fullEnv bridgeExpr oldName then
        violations := violations ++ [⟨.judgeSuccession, newName,
          s!"bridge term transitively cites `{oldName}` itself instead of deriving `{oldName}`'s statement from `{newName}`"⟩]
    -- Guard 2: Bridge must genuinely consume `hNew : P_new`
    if !(← bridgeConsumesNewAssumption pNew bridgeExpr) then
      violations := violations ++ [⟨.judgeSuccession, newName,
        s!"bridge term ignores the `{newName}` hypothesis (`_hNew` unused); `{newName}` may have been silently weakened"⟩]
    -- Guard 3: Kernel-check `bridgeExpr : P_new → P_old` + Law 1 Axiom Purity
    let kErrs ← kernelCheckScratchTheorem newName .judgeSuccession impTy bridgeExpr
    violations := violations ++ kErrs
    return mkAuditVerdictMeta newName
      s!"`judge-succession@1` kernel-verified: `{newName}` entails `{oldName}`" violations

/-- **`#verify_judge_succession <NewThm> implies <OldThm> via <BridgeTerm>`**:
    Enforces `judge-succession@1` in Lean's kernel — elaborates and kernel-checks `BridgeTerm`
    against `(StatementOf NewThm) → (StatementOf OldThm)` while rejecting self-citation of `OldThm`
    and unused-hypothesis weakening bypasses. -/
elab "#verify_judge_succession " newId:ident " implies " oldId:ident " via " bridge:term : command => do
  let newName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo newId
  let oldName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo oldId
  let verdict ← liftTermElabM <| verifyJudgeSuccessionAudit newName oldName bridge
  match verdict with
  | .passed _ summary =>
    logInfo m!"[PASS] #verify_judge_succession: {summary}"
  | .refused _ vs =>
    throwError m!"#verify_judge_succession refused `{newName} → {oldName}`:\n{formatViolations vs}"

/-! ## 5. Command-Level Negative-Test Harness (`#expect_claim_audit_failure`) -/

/-- **`#expect_claim_audit_failure "expectedSubstring" in <command>`**:
    Executes `<command>` in a rolled-back state, succeeding ONLY if `<command>` logs an error
    containing `"expectedSubstring"`, and restoring the environment and message log cleanly. -/
elab "#expect_claim_audit_failure " expected:str " in " cmd:command : command => do
  let want := expected.getString
  let savedState ← get
  let priorCount := savedState.messages.toList.length
  let mut escapedErr : Option String := none
  try
    elabCommand cmd
  catch ex =>
    escapedErr := some (← ex.toMessageData.toString)
  let postMsgs := (← get).messages.toList.drop priorCount
  set savedState
  let mut errTexts : List String := []
  if let some e := escapedErr then
    errTexts := [e]
  for m in postMsgs do
    if m.severity == .error then
      errTexts := errTexts ++ [← m.data.toString]
  if errTexts.isEmpty then
    throwError m!"#expect_claim_audit_failure failed: command succeeded with 0 errors (expected failure matching \"{want}\")"
  let combined := String.intercalate "\n" errTexts
  unless hasSubstr combined want do
    throwError m!"#expect_claim_audit_failure failed: error did not mention \"{want}\". Actual error:\n{combined}"
  logInfo m!"[PASS] #expect_claim_audit_failure caught expected kernel refusal (\"{want}\")"

end Obend.Tactic.ClaimAudit
end
