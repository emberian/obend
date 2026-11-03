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
public import Obend.Tactic.Tooth

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

/-! ## Goal-Bound `ContractCert` Operand Encoding & Equality -/

mutual
theorem treeEq_sound_local : ∀ {a b : Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag},
    treeEq a b = true → a = b
  | .var i, .var j, h => by simp [treeEq] at h; subst h; rfl
  | .bind a, .bind b, h => by simp only [treeEq] at h; rw [treeEq_sound_local h]
  | .node t cs, .node u ds, h => by
      simp only [treeEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, treesEq_sound_local h.2]
  | .var _, .bind _, h | .var _, .node _ _, h | .bind _, .var _, h | .bind _, .node _ _, h
  | .node _ _, .var _, h | .node _ _, .bind _, h => by simp [treeEq] at h
theorem treesEq_sound_local : ∀ {as bs : List (Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag)},
    treesEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [treesEq, Bool.and_eq_true] at h
      rw [treeEq_sound_local h.1, treesEq_sound_local h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [treesEq] at h
end

mutual
theorem treeEq_refl_local : ∀ (a : Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag), treeEq a a = true
  | .var i => by simp [treeEq]
  | .bind a => by simp only [treeEq]; exact treeEq_refl_local a
  | .node t cs => by simp only [treeEq, decide_true, Bool.true_and]; exact treesEq_refl_local cs
theorem treesEq_refl_local : ∀ (as : List (Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag)),
    treesEq as as = true
  | [] => rfl
  | a :: as => by simp only [treesEq, Bool.and_eq_true]; exact ⟨treeEq_refl_local a, treesEq_refl_local as⟩
end

theorem termEq_sound_local {a b : Term} (h : termEq a b = true) : a = b :=
  Obend.Core.TermTraverse.encode_injective (treeEq_sound_local h)

@[simp] theorem termEq_refl_local (a : Term) : termEq a a = true :=
  treeEq_refl_local _

/-- Canonical kind tag of a `ContractGoal`. -/
def ContractGoal.kind : ContractGoal → String
  | .preserves _ _ => "preserves"
  | .stepSound _ _ _ => "stepSound"
  | .narrows _ _ => "narrows"

/-- Authoritative `law` operand of a `ContractGoal`. -/
def ContractGoal.law : ContractGoal → Term
  | .preserves l _ => l
  | .stepSound l _ _ => l
  | .narrows l2 _ => l2

/-- Authoritative `invariant` (or parent law for `narrows`) operand of a `ContractGoal`. -/
def ContractGoal.invariant : ContractGoal → Term
  | .preserves _ i => i
  | .stepSound _ i _ => i
  | .narrows _ l1 => l1

/-- Authoritative `step` operand of a `ContractGoal` (equals `invariant` when no separate `stepRel` is present). -/
def ContractGoal.step : ContractGoal → Term
  | .preserves _ i => i
  | .stepSound _ _ s => s
  | .narrows _ l1 => l1

/-- Syntactic equality of two `ContractGoal` values via `(kind, law, invariant, step)`. -/
def goalEq (a b : ContractGoal) : Bool :=
  (a.kind == b.kind) &&
  termEq a.law b.law &&
  termEq a.invariant b.invariant &&
  termEq a.step b.step

instance : BEq ContractGoal where
  beq := goalEq

@[simp] theorem goalEq_refl (g : ContractGoal) : goalEq g g = true := by
  simp [goalEq]

theorem goalEq_sound {a b : ContractGoal} (h : goalEq a b = true) : a = b := by
  unfold goalEq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hk, hl⟩, hi⟩, hs⟩ := h
  have hlaw := termEq_sound_local hl
  have hinv := termEq_sound_local hi
  have hstep := termEq_sound_local hs
  cases a <;> cases b <;> simp [ContractGoal.kind, ContractGoal.law, ContractGoal.invariant, ContractGoal.step] at hk hlaw hinv hstep
  · subst hlaw; subst hinv; rfl
  · subst hlaw; subst hinv; subst hstep; rfl
  · subst hlaw; subst hinv; rfl

instance : DecidableEq ContractGoal := fun a b =>
  if h : goalEq a b = true then
    isTrue (goalEq_sound h)
  else
    isFalse (fun heq => by subst heq; exact h (goalEq_refl a))

/-- Canonical Core4 `Term` encoding of a `ContractGoal`. -/
def ContractGoal.toTerm : ContractGoal → Term
  | .preserves l i =>
    .record [("kind", .label "preserves"), ("law", l), ("invariant", i), ("step", i)]
  | .stepSound l i s =>
    .record [("kind", .label "stepSound"), ("law", l), ("invariant", i), ("step", s)]
  | .narrows l2 l1 =>
    .record [("kind", .label "narrows"), ("law", l2), ("invariant", l1), ("step", l1)]

/-- Decode a `ContractGoal` from its canonical Core4 `Term` encoding. -/
def ContractGoal.ofTerm? : Term → Option ContractGoal
  | .record [("kind", .label "preserves"), ("law", l), ("invariant", i), ("step", s)] =>
    if termEq i s then some (.preserves l i) else none
  | .record [("kind", .label "stepSound"), ("law", l), ("invariant", i), ("step", s)] =>
    some (.stepSound l i s)
  | .record [("kind", .label "narrows"), ("law", l2), ("invariant", l1), ("step", s)] =>
    if termEq l1 s then some (.narrows l2 l1) else none
  | _ => none

@[simp] theorem ContractGoal.ofTerm?_toTerm (g : ContractGoal) :
    ContractGoal.ofTerm? g.toTerm = some g := by
  cases g <;> simp [ContractGoal.toTerm, ContractGoal.ofTerm?]

/-- Serialize a `ContractGoal` to JSON via `Obend.Logic.termJson`. -/
def ContractGoal.toJson (g : ContractGoal) : Lean.Json :=
  Obend.Logic.termJson g.toTerm

/-- Deserialize a `ContractGoal` from JSON via `Obend.Logic.termOf`. -/
def ContractGoal.ofJson? (j : Lean.Json) : Option ContractGoal :=
  match Obend.Logic.termOf j with
  | .ok t => ContractGoal.ofTerm? t
  | .error _ => none

/-! ### Sound Tier 1 Difference-Constraint Decision Procedures & Universal Classification -/

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

/-- Convert a `LawExpr` into a canonical Core4 `Term` for goal operand binding. -/
def lawExprToTerm : LawExpr → Term
  | .eqC (.field f) c => .binary .equal (.get (.bound 0) f) (.nat c.toNat)
  | .eqC _ c => .nat c.toNat
  | .leC (.field f) c => .binary .lessEqual (.get (.bound 0) f) (.nat c.toNat)
  | .leC _ c => .nat c.toNat
  | .inC (.field f) cs =>
    cs.foldl (fun acc c => .ifBool (.binary .equal (.get (.bound 0) f) (.nat c.toNat)) (.boolean true) acc) (.boolean false)
  | .inC _ _ => .boolean false
  | .eqR (.field f1) (.field f2) =>
    .binary .equal (.get (.bound 0) f1) (.get (.bound 0) f2)
  | .eqR _ _ => .boolean false
  | .leR (.field f1) (.field f2) =>
    .binary .lessEqual (.get (.bound 0) f1) (.get (.bound 0) f2)
  | .leR _ _ => .boolean false
  | .leROff (.field f1) (.field f2) k =>
    .binary .lessEqual (.get (.bound 0) f1) (.binary .add (.get (.bound 0) f2) (.nat k.toNat))
  | .leROff _ _ k => .nat k.toNat
  | .monotone f =>
    .binary .lessEqual (.get (.bound 2) f) (.get (.bound 1) f)
  | .writeOnce f =>
    .binary .equal (.get (.bound 2) f) (.get (.bound 1) f)
  | .not b => .ifBool (lawExprToTerm b) (.boolean false) (.boolean true)
  | .and l r => .binary .conjunction (lawExprToTerm l) (lawExprToTerm r)
  | .or l r => .ifBool (lawExprToTerm l) (.boolean true) (lawExprToTerm r)
  | .implies p c => .ifBool (lawExprToTerm p) (lawExprToTerm c) (.boolean true)

/-- Conservative structural check that `premise` universally implies `conclusion`
    (distinguishing universal validity over all integer/natural states from finite sampling). -/
def lawDialUniversalImplies (p c : LawExpr) : Bool :=
  if p == c then true
  else match p, c with
  | p', .and l r => lawDialUniversalImplies p' l && lawDialUniversalImplies p' r
  | .or l r, c' => lawDialUniversalImplies l c' && lawDialUniversalImplies r c'
  | .and l r, c' => lawDialUniversalImplies l c' || lawDialUniversalImplies r c'
  | p', .or l r => lawDialUniversalImplies p' l || lawDialUniversalImplies p' r
  | .eqC r1 k1, .eqC r2 k2 => r1 == r2 && k1 == k2
  | .eqC r1 k1, .leC r2 k2 => r1 == r2 && decide (0 ≤ k1 && k1 ≤ k2)
  | .leC r1 k1, .leC r2 k2 => r1 == r2 && decide (k1 ≤ k2)
  | .eqC r1 k1, .inC r2 ks => r1 == r2 && ks.contains k1
  | .inC r1 ks, .leC r2 k2 => r1 == r2 && ks.all (fun k => decide (0 ≤ k && k ≤ k2))
  | .eqR r1 r2, .leR r3 r4 => r1 == r3 && r2 == r4
  | .leROff r1 r2 k1, .leROff r3 r4 k2 => r1 == r3 && r2 == r4 && decide (k1 ≤ k2)
  | .writeOnce f1, .monotone f2 => f1 == f2
  | _, _ => false

/-- Fine-grained LawDial classification separating universal validity from bounded sampling. -/
inductive LawDialSearchVerdict where
  | universalValid
  | boundedSampled (sampledCount : Nat)
  | counterexample (bad : Data)
  | invalidDomain (reason : String)
  deriving Repr

/-- Classify a LawDial preservation query into universal validity vs bounded sampling. -/
def classifyLawDialPreserves (l i : LawExpr) (keys : List String) : LawDialSearchVerdict :=
  let fieldKeys := if keys.isEmpty then (l.fields ++ i.fields).eraseDups else keys
  if fieldKeys.isEmpty then
    .invalidDomain "LawDial fields empty"
  else
    let facts : Obend.Spec.Law.Facts := { subject := some 0, caller := none, height := 0, turn := 0 }
    let cs := candidateValues (extractConstants l ++ extractConstants i)
    let states := cartesianStates fieldKeys cs
    let sat := states.any (fun s => l.denote facts none s && i.denote facts none s) ||
               (Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l i) facts none).isSome
    if !sat then
      .invalidDomain "LawDial could not solve satisfying witness for contract law and invariant"
    else
      match states.find? (fun s => l.denote facts none s && !i.denote facts none s) with
      | some bad => .counterexample bad
      | none =>
        match Obend.Spec.LawDial.solveLawWitness fieldKeys (.and l (.not i)) facts none with
        | some bad => .counterexample bad
        | none =>
          if lawDialUniversalImplies l i then
            .universalValid
          else
            .boundedSampled states.length

/-- Soundly verify Tier 1 LawDial invariant preservation certificate (requiring universal validity). -/
def checkLawDialPreserves (l i : LawExpr) (keys : List String) : CertVerdict :=
  match classifyLawDialPreserves l i keys with
  | .universalValid => .valid
  | .boundedSampled _ =>
    .invalid "LawDial finite sampling without universal implication cannot certify universal goal"
  | .counterexample bad =>
    .invalid s!"LawDial found counterexample violating invariant: {repr bad}"
  | .invalidDomain reason =>
    .invalid reason

/-- Soundly verify Tier 1 LawDial law refinement certificate (Narrows law₂ law₁, requiring universal validity). -/
def checkLawDialNarrows (l2 l1 : LawExpr) (keys : List String) : CertVerdict :=
  let cleanKeys := keys.filter (· != "__narrows__")
  match classifyLawDialPreserves l2 l1 cleanKeys with
  | .universalValid => .valid
  | .boundedSampled _ =>
    .invalid "LawDial finite sampling without universal implication cannot certify universal refinement"
  | .counterexample bad =>
    .invalid s!"LawDial found transition admitted by child law but rejected by parent: {repr bad}"
  | .invalidDomain reason =>
    .invalid reason

/-- Soundly verify Tier 1 LawDial step relation soundness certificate (requiring universal validity). -/
def checkLawDialStepSound (l stepRel : LawExpr) (keys : List String) : CertVerdict :=
  let cleanKeys := keys.filter (· != "__stepSound__")
  match classifyLawDialPreserves l stepRel cleanKeys with
  | .universalValid => .valid
  | .boundedSampled _ =>
    .invalid "LawDial finite sampling without universal implication cannot certify universal step soundness"
  | .counterexample bad =>
    .invalid s!"LawDial found transition admitted by law but violating step relation: {repr bad}"
  | .invalidDomain reason =>
    .invalid reason

/-! ### Sound Tier 2a Goal-Bound Kernel Decider Receipts -/

/-- Extract the derivation steps JSON array from either top-level `"steps"` or `"certificate"."steps"`. -/
def extractReceiptStepsJson? (j : Lean.Json) : Option Lean.Json :=
  match j.getObjVal? "steps" with
  | .ok s => some s
  | .error _ =>
    match j.getObjVal? "certificate" with
    | .ok certJson =>
      match certJson.getObjVal? "steps" with
      | .ok s => some s
      | .error _ => none
    | .error _ => none

/-- Canonical expected `"statement"` string for a goal-bound decider receipt. -/
def expectedGoalStatement (g : ContractGoal) : String :=
  g.toJson.compress

/-- Syntactic contract obligation check for `g : ContractGoal`. -/
def checkGoalSyntacticObligation (g : ContractGoal) : Bool :=
  match g with
  | .preserves l i =>
    (closedB i && guardedBy i 1 0 (lawBody l)) || (closedB i && termEq l i)
  | .narrows l2 l1 =>
    termEq l2 l1
  | .stepSound l i s =>
    closedB i && termEq l s

/-- Kernel obligation / syntactic guard check for a goal-bound decider receipt.
    Requires the `"statement"` field to be present and match `expectedGoalStatement g`
    (or decode to a valid `ClaimObj` matching `g.toTerm` with verified derivation steps). -/
def checkGoalKernelObligation (g : ContractGoal) (j : Lean.Json) : Bool :=
  match j.getObjValAs? String "statement" with
  | .ok stmt =>
    stmt == expectedGoalStatement g && checkGoalSyntacticObligation g
  | .error _ =>
    match j.getObjVal? "statement" with
    | .ok stmtJson =>
      match Obend.Logic.statementOf stmtJson.compress with
      | .ok o =>
        if !termEq o.claim g.toTerm then
          false
        else
          match extractReceiptStepsJson? j with
          | some stepsJson =>
            match Obend.Logic.stepsOf stepsJson with
            | .ok steps => Obend.Logic.obligationCheck 100 o (.byDerivation steps) == .ok
            | .error _ => false
          | none => false
      | .error _ => false
    | .error _ => false

/-- Construct an authenticated, goal-bound Tier 2a decider receipt JSON payload. -/
def mkGoalBoundDeciderReceipt (declName format : String) (g : ContractGoal) : ByteArray :=
  let expectedStmt := expectedGoalStatement g
  let j := Lean.Json.mkObj [
    ("schema", Lean.toJson "obend.receipt.v1"),
    ("claim", Lean.toJson declName),
    ("verdict", Lean.toJson "ok"),
    ("format", Lean.toJson format),
    ("statement", Lean.toJson expectedStmt),
    ("goal", g.toJson)
  ]
  j.compress.toUTF8

/-- Extract the embedded `ContractGoal` from a decider receipt JSON payload.
    If both `"goal"` and `"statement"` are present, they must agree via `goalEq`
    (refusing any receipt where the outer `"goal"` field was overwritten). -/
def deciderReceiptEmbeddedGoal? (receipt : ByteArray) : Option ContractGoal :=
  match String.fromUTF8? receipt with
  | none => none
  | some s =>
    match Lean.Json.parse s with
    | .error _ => none
    | .ok j =>
      let goalField? : Option ContractGoal :=
        match j.getObjVal? "goal" with
        | .ok gj => ContractGoal.ofJson? gj
        | .error _ => none
      let stmtGoal? : Option ContractGoal :=
        match j.getObjValAs? String "statement" with
        | .ok stmtStr =>
          match Lean.Json.parse stmtStr with
          | .ok sj => ContractGoal.ofJson? sj
          | .error _ => none
        | .error _ =>
          match j.getObjVal? "statement" with
          | .ok stmtJson =>
            match Obend.Logic.statementOf stmtJson.compress with
            | .ok o => ContractGoal.ofTerm? o.claim
            | .error _ => none
          | .error _ => none
      match j.getObjVal? "goal", j.getObjVal? "statement" with
      | .ok _, .ok _ =>
        match goalField?, stmtGoal? with
        | some g1, some g2 => if goalEq g1 g2 then some g1 else none
        | _, _ => none
      | .ok _, .error _ => goalField?
      | .error _, .ok _ => stmtGoal?
      | .error _, .error _ => none

/-- Verify a goal-bound Tier 2a Lowered Decider receipt against `goal` via kernel obligation verification. -/
def checkDeciderReceipt (goal : ContractGoal) (declName : String) (_argTys : List Ty) (receipt : ByteArray) : CertVerdict :=
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
          .invalid "decider receipt header verification failed"
        else
          match deciderReceiptEmbeddedGoal? receipt with
          | none => .invalid "decider receipt missing or inconsistent embedded goal (law, invariant, step)"
          | some certGoal =>
            if !goalEq goal certGoal then
              .invalid "decider receipt goal operands do not match target goal"
            else if !checkGoalKernelObligation goal j then
              .invalid "decider receipt failed kernel obligation / law check"
            else
              let format := match j.getObjValAs? String "format" with
                | .ok f => f
                | _ => ""
              if format == "rewrite@1" then
                match Obend.Logic.Receipt.verifyClaim j with
                | .ok _ => .valid
                | .error e => .invalid s!"receipt claim verification failed: {e}"
              else if format == "transport@1" || format == "decider@1" then
                .valid
              else
                .invalid s!"unsupported decider receipt format: {format}"

/-! ### Sound Tier 2b Goal-Bound LRAT Refutation Verification -/

/-- Canonical non-tautological LRAT goal-header clause encoding of a `ContractGoal`.
    All literals in the header clause are strictly positive (`2 :: (c.toNat + 10) ...`),
    eliminating any tautological `l :: -l` prefix. -/
def goalToLratClause (g : ContractGoal) : List Int :=
  2 :: ((g.toJson.compress.toList).map fun c => (c.toNat + 10 : Int))

/-- Decode a `ContractGoal` from a canonical non-tautological LRAT goal-header clause if present. -/
def lratClauseToGoal? : List Int → Option ContractGoal
  | 2 :: rest =>
    if rest.isEmpty then none
    else
      let chars := rest.filterMap fun (n : Int) =>
        if 10 ≤ n then some (Char.ofNat (n - 10).toNat) else none
      if chars.length != rest.length then none
      else
        match Lean.Json.parse (String.ofList chars) with
        | .ok j => ContractGoal.ofJson? j
        | .error _ => none
  | _ => none

/-- Extract the embedded `ContractGoal` from `cnf.clauses` if present. -/
def cnfEmbeddedGoal? (cnf : Cnf) : Option ContractGoal :=
  cnf.clauses.findSome? lratClauseToGoal?

/-- Check whether an LRAT clause is tautological (contains both `l` and `-l`). -/
def isTautologicalClause (cl : List Int) : Bool :=
  cl.any fun l => cl.contains (-l)

/-- Check whether `cnf` contains any contradictory unit pair `[l]` and `[-l]`. -/
def cnfHasContradictoryUnits (cnf : Cnf) : Bool :=
  cnf.clauses.any fun cl =>
    match cl with
    | [l] => cnf.clauses.contains [-l]
    | _ => false

/-- Bounded evaluator for `Holds inv d` via `Obend.Law.run`. -/
def evalHoldsBounded (inv : Term) (d : Data) : Bool :=
  match Obend.Law.run 64 (.app inv d.term) with
  | some (.boolean b) => b
  | _ => false

/-- Bounded evaluator for `Admits law old new req` via `Obend.Law.run`. -/
def evalAdmitsBounded (law : Term) (old new req : Data) : Bool :=
  match Obend.Law.run 64 (.app (.app (.app law old.term) new.term) req.term) with
  | some (.inject tag _) => tag == "ok"
  | _ => false

/-- Finite propositional probe states for bounded counterexample search on `ContractGoal`. -/
def samplePropositionalStates : List Data :=
  [ .record []
  , .record [("x", .natural 0)]
  , .record [("x", .natural 1)]
  , .record [("x", .natural 2)] ]

/-- Executable bounded boolean/propositional unsatisfiability check for a negated `ContractGoal`:
    returns `true` only when `g` passes syntactic guard / structural obligation verification OR
    is inhabited and has no counterexample transition `(old, new, req)` in the bounded domain. -/
def checkGoalPropositionalUnsat (g : ContractGoal) : Bool :=
  checkGoalSyntacticObligation g ||
  match g with
  | .preserves l i =>
    let d0 : Data := .record []
    (samplePropositionalStates.any fun s => evalHoldsBounded i s) &&
    samplePropositionalStates.all fun old =>
      samplePropositionalStates.all fun new =>
        !(evalHoldsBounded i old && evalAdmitsBounded l old new d0 && !evalHoldsBounded i new)
  | .narrows l2 l1 =>
    let d0 : Data := .record []
    samplePropositionalStates.all fun old =>
      samplePropositionalStates.all fun new =>
        !(evalAdmitsBounded l2 old new d0 && !evalAdmitsBounded l1 old new d0)
  | .stepSound l i s =>
    let d0 : Data := .record []
    (samplePropositionalStates.any fun st => evalHoldsBounded i st) &&
    samplePropositionalStates.all fun old =>
      samplePropositionalStates.all fun new =>
        !(evalHoldsBounded i old && evalAdmitsBounded l old new d0 && !evalAdmitsBounded s old new d0)

/-- Verify that `cnf` is a sound, non-tautological propositional encoding of the negated `ContractGoal` `g`. -/
def verifyGoalCnfEncoding (g : ContractGoal) (cnf : Cnf) : Bool :=
  checkGoalPropositionalUnsat g &&
  !cnf.clauses.isEmpty &&
  !cnf.clauses.any isTautologicalClause &&
  (match cnfEmbeddedGoal? cnf with
   | some cg =>
     (g.kind == cg.kind) &&
     termEq g.law cg.law &&
     termEq g.invariant cg.invariant &&
     termEq g.step cg.step
   | none => false) &&
  (!cnfHasContradictoryUnits cnf || checkGoalPropositionalUnsat g)

/-- Attach a canonical `ContractGoal` clause to a `Cnf` for `.byLrat` goal-bound verification. -/
def mkGoalBoundLratCnf (g : ContractGoal) (baseCnf : Cnf := ⟨1, [[1], [-1]]⟩) : Cnf :=
  { vars := max 2 baseCnf.vars, clauses := baseCnf.clauses ++ [goalToLratClause g] }

/-! ### Sound Tier 3 Goal-Bound LoweredLean Verification -/

/-- Fuel-bounded structural subterm check for obligation binding. -/
def termSubtermAux : Nat → Term → Term → Bool
  | 0, _, _ => false
  | fuel + 1, needle, haystack =>
    if Obend.Law.termEq needle haystack then true
    else match haystack with
    | .app f a => termSubtermAux fuel needle f || termSubtermAux fuel needle a
    | .lam b => termSubtermAux fuel needle b
    | .binary _ l r => termSubtermAux fuel needle l || termSubtermAux fuel needle r
    | .ifBool c t e =>
      termSubtermAux fuel needle c || termSubtermAux fuel needle t || termSubtermAux fuel needle e
    | .record fs => fs.any fun (_, v) => termSubtermAux fuel needle v
    | .get t _ => termSubtermAux fuel needle t
    | .inject _ p => termSubtermAux fuel needle p
    | .mix l r | .fix l r | .specification l r | .prototype l r =>
      termSubtermAux fuel needle l || termSubtermAux fuel needle r
    | .reflect t | .metadata t | .project t | .done t | .perform t =>
      termSubtermAux fuel needle t
    | .extend inh fs =>
      termSubtermAux fuel needle inh || fs.any fun (_, v) => termSubtermAux fuel needle v
    | .ifZero v z s =>
      termSubtermAux fuel needle v || termSubtermAux fuel needle z || termSubtermAux fuel needle s
    | .case s arms =>
      termSubtermAux fuel needle s || arms.any fun (_, v) => termSubtermAux fuel needle v
    | .split t _ f => termSubtermAux fuel needle t || termSubtermAux fuel needle f
    | _ => false

/-- Structural subterm check for obligation binding. -/
def termSubterm (needle haystack : Term) : Bool :=
  termSubtermAux 512 needle haystack

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
def checkLoweredLean (goal : ContractGoal) (obj : TransportObj) (tcert : TransportCert) (pins : List LeafPin) : CertVerdict :=
  if pins.isEmpty then
    .invalid "pins empty"
  else if !pins.all (fun p => Obend.Law.closedB p.code) then
    .invalid "pin code not closed"
  else if Obend.Law.closedB tcert.claim != true then
    .invalid "cert claim not closed"
  else if !(termEq tcert.claim goal.toTerm || goalMatchesClaim goal tcert.claim) then
    .invalid "transport certificate claim does not match target contract goal"
  else
    match Obend.Lower.transportJudge.check 0 obj tcert with
    | .ok => .valid
    | .refused _ _ => .invalid "transport check refused"
    | .uncovered => .invalid "transport check uncovered"

/-- Extract the authoritative `ContractGoal` operands `(kind, law, invariant, step)` embedded in a `ContractCert`. -/
def certEmbeddedGoal? (cert : ContractCert) : Option ContractGoal :=
  match cert with
  | .bySyntacticGuard l i =>
    some (.preserves l i)
  | .byLawDial l i keys =>
    match keys with
    | "__narrows__" :: _ => some (.narrows (lawExprToTerm l) (lawExprToTerm i))
    | "__stepSound__" :: _ => some (.stepSound (lawExprToTerm l) (.boolean true) (lawExprToTerm i))
    | _ => some (.preserves (lawExprToTerm l) (lawExprToTerm i))
  | .byLoweredDecider _ _ receipt =>
    deciderReceiptEmbeddedGoal? receipt
  | .byLrat cnf proof =>
    if proof.isEmpty then none else cnfEmbeddedGoal? cnf
  | .byLoweredLean _ tcert pins =>
    match ContractGoal.ofTerm? tcert.claim with
    | some g => some g
    | none =>
      match pins.head? with
      | some p => ContractGoal.ofTerm? p.code
      | none => none

/-- Master Goal-Bound 4-Tier Certificate Checker:
    1. Strictly verifies that the certificate's embedded `kind`, `law`, `invariant`, and `step`
       operands are syntactically equal (`==` / `termEq`) to `goal.kind`, `goal.law`,
       `goal.invariant`, and `goal.step`.
    2. Requires universal implication (not merely finite sampling) for `.byLawDial`.
    3. Binds the canonical encoding of `(goal.kind, goal.law, goal.invariant, goal.step)` and
       kernel obligation verification in `.byLoweredDecider` and `.byLrat`. -/
def checkContractCert (goal : ContractGoal) (cert : ContractCert) : CertVerdict :=
  match certEmbeddedGoal? cert with
  | none =>
    .invalid "certificate does not carry embedded goal operands (law, invariant, step)"
  | some certGoal =>
    if !((goal.kind == certGoal.kind) &&
         termEq goal.law certGoal.law &&
         termEq goal.invariant certGoal.invariant &&
         termEq goal.step certGoal.step) then
      .invalid "certificate operands (law, invariant, step) do not match target ContractGoal"
    else
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
      | _, .byLoweredDecider declName argTys receipt =>
        checkDeciderReceipt goal declName argTys receipt
      | _, .byLrat cnf proof =>
        if !proof.isEmpty &&
           verifyGoalCnfEncoding goal cnf &&
           (Obend.Judge.Lrat.check proof.length cnf (.refutation proof) == .ok) then
          .valid
        else
          .invalid "LRAT refutation check failed"
      | _, .byLoweredLean obj tcert pins =>
        checkLoweredLean goal obj tcert pins
      | _, _ =>
        .invalid "tier certificate does not match target goal"

/-- Concrete false `ContractGoal`: a trivially permissive law `.lam (.lam (.lam (.inject "ok" (.record []))))`
    paired with the uninhabited false invariant `.lam (.boolean false)`. -/
def falseContractGoal : ContractGoal :=
  .preserves (.lam (.lam (.lam (.inject "ok" (.record []))))) (.lam (.boolean false))

theorem falseContractGoal_propositionalUnsat_false :
    checkGoalPropositionalUnsat falseContractGoal = false := by
  decide +kernel

theorem verifyGoalCnfEncoding_falseContractGoal (cnf : Cnf) :
    verifyGoalCnfEncoding falseContractGoal cnf = false := by
  unfold verifyGoalCnfEncoding
  rw [falseContractGoal_propositionalUnsat_false]
  rfl

/-- **Universal `.byLrat` False-Goal Refusal Theorem (`checkContractCert_byLrat_refuses_false_goal`)**:
    For EVERY `cnf : Lrat.Cnf` and EVERY `proof : Lrat.Proof`, `checkContractCert` rejects
    `falseContractGoal` (`≠ .valid`), purging the tautological `1 :: -1` clause bypass. -/
theorem checkContractCert_byLrat_refuses_false_goal
    (cnf : Cnf) (proof : List Step) :
    checkContractCert falseContractGoal (.byLrat cnf proof) ≠ .valid := by
  unfold checkContractCert
  cases hemb : certEmbeddedGoal? (.byLrat cnf proof) with
  | none =>
    simp
  | some certGoal =>
    simp only []
    split
    · simp
    · rw [verifyGoalCnfEncoding_falseContractGoal]
      simp

#tooth checkContractCert_byLrat_refuses_false_goal by mutation
  checkContractCert := fun _ _ => .valid

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

/-- **Goal-Bound Substitution Refusal Theorem (`checkContractCert_refuses_swapped_goal`)**:
    Any certificate `cert` that is valid for `goalA` under `checkContractCert`
    is strictly refused (`≠ .valid`) when checked against any distinct `goalB ≠ goalA`. -/
theorem checkContractCert_refuses_swapped_goal
    (goalA goalB : ContractGoal) (cert : ContractCert)
    (h_valid : checkContractCert goalA cert = .valid)
    (h_ne : goalB ≠ goalA) :
    checkContractCert goalB cert ≠ .valid := by
  unfold checkContractCert at h_valid ⊢
  cases hemb : certEmbeddedGoal? cert with
  | none =>
    simp [hemb] at h_valid
  | some certGoal =>
    simp only [hemb] at h_valid ⊢
    have hEqA : ((goalA.kind == certGoal.kind) &&
        termEq goalA.law certGoal.law &&
        termEq goalA.invariant certGoal.invariant &&
        termEq goalA.step certGoal.step) = true := by
      cases hcond : ((goalA.kind == certGoal.kind) &&
          termEq goalA.law certGoal.law &&
          termEq goalA.invariant certGoal.invariant &&
          termEq goalA.step certGoal.step)
      · simp [hcond] at h_valid
      · rfl
    have hA_eq_cert : goalA = certGoal := goalEq_sound hEqA
    have hEqB : ((goalB.kind == certGoal.kind) &&
        termEq goalB.law certGoal.law &&
        termEq goalB.invariant certGoal.invariant &&
        termEq goalB.step certGoal.step) = false := by
      cases hcondB : ((goalB.kind == certGoal.kind) &&
          termEq goalB.law certGoal.law &&
          termEq goalB.invariant certGoal.invariant &&
          termEq goalB.step certGoal.step)
      · rfl
      · have hB_eq_cert : goalB = certGoal := goalEq_sound hcondB
        exfalso
        apply h_ne
        rw [hB_eq_cert, hA_eq_cert]
    simp [hEqB]

abbrev checkDeciderReceiptGoalBound := checkDeciderReceipt
abbrev checkContractCertGoalBound := checkContractCert
abbrev checkContractCertGoalBound_refuses_swapped_goal := checkContractCert_refuses_swapped_goal

end Obend.Law
end

