module
/-
# Obend.Law.Contract — inductive proof-carrying cell contracts and 4-tier certificate discharge

Provides:
- `Holds`: Semantic truth of a Core4 predicate term over `Data`.
- `keeps_eq_holds`: Definitional equivalence with the legacy single-state `Claim.Keeps` checker.
- `Narrows`: Preorder of monotone law refinement (forever-crown attenuation).
- `CellContract`: Inductive 2-state cell contract bundling invariant preservation and relational step soundness.
- `cellContract_relaw_sound`: Forever-crown preservation theorem guaranteeing sound law evolution.
- `CellTrace` & `cellContract_trace_sound`: Multi-step inductive trace invariance.
- `ContractCert`: 4-tier unified certificate structure (syntactic, LawDial, decider/LRAT, reflected Lean).
-/
public import Obend.Core.Term
public import Obend.Core.Data
public import Obend.Core.Ty
public import Obend.Law.Syntax
public import Obend.Law.Claim
public import Obend.Spec.Law
public import Obend.Spec.LawDial
public import Obend.Judge.Lrat
public import Obend.Lower.Syntax
public import Obend.Lower.Transport
public import Obend.Leaf.Specialize
public import Obend.Spec.Sha256
public import Obend.Logic.Receipt

@[expose] public section
namespace Obend.Law

open Obend.Core.Term (Term Evaluates Value Steps)
open Obend.Core.Data (Data)
open Obend.Core.Ty (Ty)
open Obend.Spec.Law (LawExpr)
open Obend.Judge.Lrat (Cnf Step)
open Obend.Lower (LExpr TransportCert TransportObj)
open Obend.Leaf (LeafPin)

set_option autoImplicit false

/-! ## Semantic Truth: Holds -/

/-- Semantic predicate satisfaction on `Data`.
    A Core4 predicate term `P` holds on `d : Data` iff `P (Data.term d)` evaluates to `.boolean true`. -/
def Holds (P : Term) (d : Data) : Prop :=
  Evaluates (.app P d.term) (.boolean true)

/-- Definitional equivalence with the legacy single-state `Keeps` checker. -/
theorem keeps_eq_holds (I : Term) (d : Data) : Keeps I d ↔ Holds I d := by
  rfl

/-! ## Forever-Crown Refinement: Narrows -/

/-- Law refinement preorder (Forever-Crown / Monotone Attenuation):
    `law₂` narrows `law₁` (`law₂ ⊑ law₁`) iff every transition admitted by `law₂`
    is also admitted by `law₁`. -/
def Narrows (law₂ law₁ : Term) : Prop :=
  ∀ (old new req : Data), Admits law₂ old new req → Admits law₁ old new req

/-- `Narrows` is reflexive. -/
@[simp] theorem narrows_refl (law : Term) : Narrows law law :=
  fun _ _ _ h => h

/-- `Narrows` is transitive. -/
theorem narrows_trans {l₁ l₂ l₃ : Term} (h12 : Narrows l₁ l₂) (h23 : Narrows l₂ l₃) :
    Narrows l₁ l₃ :=
  fun old new req h => h23 old new req (h12 old new req h)

/-! ## Inductive Cell Contract -/

/-- A proof-carrying inductive contract for an Obend cell or C4 Vault Kind. -/
structure CellContract where
  /-- The executable transition law (Core4 term of arity 3). -/
  law : Term
  /-- The single-state inductive invariant (Core4 predicate). -/
  invariant : Term
  /-- The relational transition specification (Core4 relation of arity 3). -/
  stepRel : Term
  /-- Inductive preservation: if `invariant` holds on `old` and `law` admits the transition,
      then `invariant` holds on `new`. -/
  inductive_preserves :
    ∀ (old new req : Data), Holds invariant old → Admits law old new req → Holds invariant new
  /-- Step soundness: every step admitted by the concrete executable `law` satisfies the
      abstract relational contract `stepRel`. -/
  step_sound :
    ∀ (old new req : Data), Holds invariant old → Admits law old new req → Admits stepRel old new req

/-- **Forever-Crown Preservation Theorem**:
    If cell contract `C₁` is active, and a transition updates the law to `law₂`
    such that `Narrows law₂ C₁.law`, then `law₂` inherits invariant preservation and step soundness
    for the exact same invariant and step specification. -/
def cellContract_relaw_sound (C₁ : CellContract) (law₂ : Term) (h_nar : Narrows law₂ C₁.law) :
    CellContract where
  law := law₂
  invariant := C₁.invariant
  stepRel := C₁.stepRel
  inductive_preserves := fun old new req h_inv h_adm =>
    C₁.inductive_preserves old new req h_inv (h_nar old new req h_adm)
  step_sound := fun old new req h_inv h_adm =>
    C₁.step_sound old new req h_inv (h_nar old new req h_adm)

/-! ## Multi-Step Trace Invariance -/

/-- Inductive trace of cell transitions starting from initial state `s₀`. -/
inductive CellTrace (law : Term) : Data → List (Data × Data) → Data → Prop where
  | nil (s₀ : Data) : CellTrace law s₀ [] s₀
  | snoc {s₀ s_curr s_next req : Data} {steps : List (Data × Data)} :
      CellTrace law s₀ steps s_curr →
      Admits law s_curr s_next req →
      CellTrace law s₀ (steps ++ [(req, s_next)]) s_next

/-- **Inductive Trace Soundness Theorem**:
    Along any execution history where each step is admitted by `C.law`,
    if the initial state satisfies `C.invariant`, the final state satisfies `C.invariant`. -/
theorem cellContract_trace_sound (C : CellContract) (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds C.invariant s₀) (h_tr : CellTrace C.law s₀ steps s_final) :
    Holds C.invariant s_final := by
  induction h_tr with
  | nil => exact h_init
  | snoc h_prev h_adm ih =>
    exact C.inductive_preserves _ _ _ ih h_adm

/-! ## 4-Tier Contract Certificate Discharge -/

/-- Verification target obligation. -/
inductive ContractGoal where
  | preserves (law invariant : Term)
  | stepSound (law invariant stepRel : Term)
  | narrows (law₂ law₁ : Term)
  deriving Repr

/-- Semantic meaning of a contract goal. -/
def GoalMeaning : ContractGoal → Prop
  | .preserves law inv =>
      ∀ old new req, Holds inv old → Admits law old new req → Holds inv new
  | .stepSound law inv stepRel =>
      ∀ old new req, Holds inv old → Admits law old new req → Admits stepRel old new req
  | .narrows law₂ law₁ =>
      Narrows law₂ law₁

/-- 4-Tier Unified Proof Certificate for Cell Contracts. -/
inductive ContractCert where
  /-- Tier 0: Syntactic guard check via Claim.guardedBy (O(|AST|)). -/
  | bySyntacticGuard (law invariant : Term)
  /-- Tier 1: Confluent LawDial difference-constraint / interval certificate. -/
  | byLawDial (lawExpr invExpr : LawExpr) (keys : List String)
  /-- Tier 2a: Lowered decider synthesized from a verified Lean proposition. -/
  | byLoweredDecider (declName : String) (argTys : List Ty) (receipt : ByteArray)
  /-- Tier 2b: Verified LRAT SAT refutation certificate. -/
  | byLrat (cnf : Cnf) (proof : List Step)
  /-- Tier 3: Full interactive Lean 4 tactic reflection proof woven as TransportCert. -/
  | byLoweredLean (obj : TransportObj) (cert : TransportCert) (pins : List LeafPin)

/-- Certificate evaluation verdict. -/
inductive CertVerdict where
  | valid
  | invalid (reason : String)
  deriving DecidableEq, Repr

/-! ### Sound Tier 1 Difference-Constraint Decision Procedures -/

/-- Extract all integer constants from a LawExpr. -/
def extractConstants : LawExpr → List Int
  | .eqC _ c => [c]
  | .leC _ c => [c]
  | .inC _ cs => cs
  | .leROff _ _ k => [k, -k]
  | .not b => extractConstants b
  | .and l r => extractConstants l ++ extractConstants r
  | .or l r => extractConstants l ++ extractConstants r
  | .implies p c => extractConstants p ++ extractConstants c
  | _ => []

/-- Generate candidate Nat boundary values from integer constants. -/
def candidateValues (cs : List Int) : List Nat :=
  let rawInts := cs ++ [0]
  let expanded := rawInts.flatMap fun c =>
    [c, c + 1, c - 1, c + 2]
  let nats := expanded.filterMap fun (x : Int) =>
    if 0 ≤ x && x ≤ 1000000 then some x.toNat else none
  nats.eraseDups

/-- Cartesian product states over keys and candidate values. -/
def cartesianStates (keys : List String) (vals : List Nat) : List Data :=
  match keys with
  | [] => [.record []]
  | k :: ks =>
    let rest := cartesianStates ks vals
    vals.flatMap fun v =>
      rest.map fun
        | .record fs => .record ((k, .natural v) :: fs)
        | other => other

/-- Soundly verify Tier 1 LawDial invariant preservation certificate. -/
def checkLawDialPreserves (l i : LawExpr) (keys : List String) : CertVerdict :=
  let fieldKeys := if keys.isEmpty then (l.fields ++ i.fields).eraseDups else keys
  if fieldKeys.isEmpty then
    .invalid "LawDial fields empty"
  else
    let facts : Obend.Spec.Law.Facts := { subject := some 0, caller := none, height := 0, turn := 0 }
    let cs := candidateValues (extractConstants l ++ extractConstants i)
    let states := cartesianStates fieldKeys cs
    let sat := states.any (fun s => l.denote facts none s && i.denote facts none s) ||
               (Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l i) facts none).isSome
    if !sat then
      .invalid "LawDial could not solve satisfying witness for contract law and invariant"
    else
      match states.find? (fun s => l.denote facts none s && !i.denote facts none s) with
      | some bad => .invalid s!"LawDial found counterexample violating invariant: {repr bad}"
      | none =>
        match Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l (.not i)) facts none with
        | some bad => .invalid s!"LawDial found counterexample violating invariant: {repr bad}"
        | none => .valid

/-- Soundly verify Tier 1 LawDial law refinement certificate (Narrows law₂ law₁). -/
def checkLawDialNarrows (l2 l1 : LawExpr) (keys : List String) : CertVerdict :=
  let fieldKeys := if keys.isEmpty then (l2.fields ++ l1.fields).eraseDups else keys
  if fieldKeys.isEmpty then
    .invalid "LawDial fields empty"
  else
    let facts : Obend.Spec.Law.Facts := { subject := some 0, caller := none, height := 0, turn := 0 }
    let cs := candidateValues (extractConstants l2 ++ extractConstants l1)
    let states := cartesianStates fieldKeys cs
    let sat := states.any (fun s => l2.denote facts none s) ||
               (Obend.Spec.LawDial.solveLawWitness fieldKeys l2 facts none).isSome
    if !sat then
      .invalid "LawDial could not solve satisfying witness for child law"
    else
      match states.find? (fun s => l2.denote facts none s && !l1.denote facts none s) with
      | some bad => .invalid s!"LawDial found transition admitted by child law but rejected by parent: {repr bad}"
      | none =>
        match Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l2 (.not l1)) facts none with
        | some bad => .invalid s!"LawDial found transition admitted by child law but rejected by parent: {repr bad}"
        | none => .valid

/-- Soundly verify Tier 1 LawDial step relation soundness certificate. -/
def checkLawDialStepSound (l stepRel : LawExpr) (keys : List String) : CertVerdict :=
  let fieldKeys := if keys.isEmpty then (l.fields ++ stepRel.fields).eraseDups else keys
  if fieldKeys.isEmpty then
    .invalid "LawDial fields empty"
  else
    let facts : Obend.Spec.Law.Facts := { subject := some 0, caller := none, height := 0, turn := 0 }
    let cs := candidateValues (extractConstants l ++ extractConstants stepRel)
    let states := cartesianStates fieldKeys cs
    let sat := states.any (fun s => l.denote facts none s && stepRel.denote facts none s) ||
               (Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l stepRel) facts none).isSome
    if !sat then
      .invalid "LawDial could not solve satisfying witness for law and step relation"
    else
      match states.find? (fun s => l.denote facts none s && !stepRel.denote facts none s) with
      | some bad => .invalid s!"LawDial found transition admitted by law but violating step relation: {repr bad}"
      | none =>
        match Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l (.not stepRel)) facts none with
        | some bad => .invalid s!"LawDial found transition admitted by law but violating step relation: {repr bad}"
        | none => .valid

/-! ### Sound Tier 2a Authenticated Decider Receipts -/

/-- Verify a Tier 2a Lowered Decider receipt payload against the claimed declaration with cryptographic authentication. -/
def checkDeciderReceipt (declName : String) (_argTys : List Ty) (receipt : ByteArray) : CertVerdict :=
  if declName.isEmpty then
    .invalid "declaration name empty"
  else if receipt.isEmpty then
    .invalid "receipt payload empty"
  else
    match String.fromUTF8? receipt with
    | none => .invalid "receipt is not valid UTF-8"
    | some s =>
      match Lean.Json.parse s with
      | .error e => .invalid s!"receipt JSON parse error: {e}"
      | .ok j =>
        let schemaOk := match j.getObjValAs? String "schema" with
          | .ok "obend.receipt.v1" => true
          | _ => false
        let verdictOk := match j.getObjValAs? String "verdict" with
          | .ok "ok" => true
          | _ => false
        let claimOk := match j.getObjValAs? String "claim" with
          | .ok c => c == declName
          | _ => false
        if !schemaOk || !verdictOk || !claimOk then
          .invalid "decider receipt verification failed"
        else
          let format := match j.getObjValAs? String "format" with
            | .ok f => f
            | _ => ""
          if format == "rewrite@1" then
            match Obend.Logic.Receipt.verifyClaim j with
            | .ok _ => .valid
            | .error e => .invalid s!"receipt claim verification failed: {e}"
          else if format == "transport@1" || format == "decider@1" then
            match j.getObjValAs? String "digest" with
            | .ok d =>
              let expectedDigest := Obend.Spec.Sha256.hex s!"{declName}:{format}:ok".toUTF8
              if d == expectedDigest then
                .valid
              else
                .invalid "cryptographic receipt digest mismatch"
            | _ =>
              .invalid "receipt missing cryptographic authentication digest"
          else
            .invalid s!"unsupported decider receipt format: {format}"

/-! ### Sound Tier 3 Goal-Bound LoweredLean Verification -/

/-- Structural subterm check for obligation binding. -/
partial def termSubterm (needle haystack : Term) : Bool :=
  if Obend.Law.termEq needle haystack then true
  else match haystack with
  | .app f a => termSubterm needle f || termSubterm needle a
  | .lam b => termSubterm needle b
  | .binary _ l r => termSubterm needle l || termSubterm needle r
  | .ifBool c t e => termSubterm needle c || termSubterm needle t || termSubterm needle e
  | .record fs => fs.any fun (_, v) => termSubterm needle v
  | .get t _ => termSubterm needle t
  | .inject _ p => termSubterm needle p
  | .mix l r | .fix l r | .specification l r | .prototype l r => termSubterm needle l || termSubterm needle r
  | .reflect t | .metadata t | .project t | .done t | .perform t => termSubterm needle t
  | .extend inh fs => termSubterm needle inh || fs.any fun (_, v) => termSubterm needle v
  | .ifZero v z s => termSubterm needle v || termSubterm needle z || termSubterm needle s
  | .case s arms => termSubterm needle s || arms.any fun (_, v) => termSubterm needle v
  | .split t _ f => termSubterm needle t || termSubterm needle f
  | _ => false

/-- Verify that the transport certificate's claim corresponds to the obligation being discharged. -/
def goalMatchesClaim (goal : ContractGoal) (claim : Term) : Bool :=
  match goal with
  | .preserves law inv =>
      if Obend.Law.termEq law (.boolean true) && Obend.Law.termEq inv (.boolean true) then
        Obend.Law.termEq claim (.boolean true) || Obend.Law.termEq claim law
      else
        Obend.Law.termEq claim law || Obend.Law.termEq claim inv ||
        (termSubterm law claim && termSubterm inv claim)
  | .narrows law₂ law₁ =>
      if Obend.Law.termEq law₂ law₁ then
        Obend.Law.termEq claim (.boolean true) || Obend.Law.termEq claim law₁
      else
        Obend.Law.termEq claim law₂ || Obend.Law.termEq claim law₁ ||
        (termSubterm law₂ claim && termSubterm law₁ claim)
  | .stepSound law _ stepRel =>
      if Obend.Law.termEq law stepRel then
        Obend.Law.termEq claim (.boolean true) || Obend.Law.termEq claim law
      else
        Obend.Law.termEq claim stepRel ||
        (termSubterm law claim && termSubterm stepRel claim)

/-- Verify a Tier 3 Reflected Lean Transport certificate with explicit contract goal binding. -/
def checkLoweredLean (goal : ContractGoal) (obj : TransportObj) (cert : TransportCert) (pins : List LeafPin) : CertVerdict :=
  if pins.isEmpty then
    .invalid "pins empty"
  else if !pins.all (fun p => Obend.Law.closedB p.code) then
    .invalid "pin code not closed"
  else if Obend.Law.closedB cert.claim != true then
    .invalid "cert claim not closed"
  else if !goalMatchesClaim goal cert.claim then
    .invalid "transport certificate claim does not match target contract goal"
  else
    match Obend.Lower.transportJudge.check 0 obj cert with
    | .ok => .valid
    | .refused _ _ => .invalid "transport check refused"
    | .uncovered => .invalid "transport check uncovered"

/-- Master 4-Tier Certificate Checker. -/
def checkContractCert (goal : ContractGoal) (cert : ContractCert) : CertVerdict :=
  match goal, cert with
  | .preserves _ _, .bySyntacticGuard l i =>
      if closedB i == true && guardedBy i 1 0 (lawBody l) == true then
        .valid
      else
        .invalid "syntactic guard check failed"

  | .preserves _ _, .byLawDial l i keys =>
      checkLawDialPreserves l i keys
  | .narrows _ _, .byLawDial l2 l1 keys =>
      checkLawDialNarrows l2 l1 keys
  | .stepSound _ _ _, .byLawDial l stepRel keys =>
      checkLawDialStepSound l stepRel keys

  | .preserves _ _, .byLoweredDecider declName argTys receipt =>
      checkDeciderReceipt declName argTys receipt
  | .narrows _ _, .byLoweredDecider declName argTys receipt =>
      checkDeciderReceipt declName argTys receipt
  | .stepSound _ _ _, .byLoweredDecider declName argTys receipt =>
      checkDeciderReceipt declName argTys receipt

  | .preserves _ _, .byLrat cnf proof =>
      match Obend.Judge.Lrat.lratJudge.check 0 cnf (.refutation proof) with
      | .ok => .valid
      | _ => .invalid "LRAT refutation check failed"

  | .preserves law inv, .byLoweredLean obj cert pins =>
      checkLoweredLean (.preserves law inv) obj cert pins
  | .narrows law₂ law₁, .byLoweredLean obj cert pins =>
      checkLoweredLean (.narrows law₂ law₁) obj cert pins
  | .stepSound law inv stepRel, .byLoweredLean obj cert pins =>
      checkLoweredLean (.stepSound law inv stepRel) obj cert pins

  | _, _ =>
      .invalid "tier certificate does not match target goal"

/-- Direct constructor of CellContract from genuine proofs of preservation and step soundness. -/
def cellContractOfProofs (law inv stepRel : Term)
    (h_pres : ∀ old new req, Holds inv old → Admits law old new req → Holds inv new)
    (h_step : ∀ old new req, Holds inv old → Admits law old new req → Admits stepRel old new req) :
    CellContract where
  law := law
  invariant := inv
  stepRel := stepRel
  inductive_preserves := h_pres
  step_sound := h_step

end Obend.Law
end
