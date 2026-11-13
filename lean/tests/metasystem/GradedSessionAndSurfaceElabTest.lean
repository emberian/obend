module
public import Obend.Core.GradedSessionMetatheory
public import Obend.Spec.BidirectionalSurfaceElab
import all Init.Data.String.Defs
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.Check
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.GradedSessionMetatheory
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Polis.CapTP
import all Obend.Spec.BidirectionalSurfaceElab
import all Obend.Spec.C4
import all Obend.Spec.Law
import all Obend.Spec.Syntax
import all Obend.Spec.Types
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Obend.Vault.Mandate
import all Obend.Category.GradedLogic
import all Obend.Category.Refines
import all Obend.Core.Capacity
import all Obend.Core.Code
import all Obend.Core.Cubical2LTT
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.Invariant
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RuntimeOrigins
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Intention
import all Obend.Judge.Clearing
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Rewrite
import all Obend.Logic.SuperRefines
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Repair.DeltaLensRenew
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.DataWire
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.MonadicReduction

/-!
Witnesses and teeth for `Obend.Core.GradedSessionMetatheory` and
`Obend.Spec.BidirectionalSurfaceElab`: inhabitants of the premises the theorems assume, the
refusals named clause by clause, and mutations the stored proofs do not survive.
-/

public section
namespace Obend.Tests.GradedSessionAndSurfaceElab
open Obend.Core.GradedSessionMetatheory Obend.Polis.CapTP
open Obend.Spec.BidirectionalSurfaceElab
open Obend.Core.Ty (Quantity Reuse)
set_option autoImplicit false

/-! ## Grades: weakening, contraction, split -/

abbrev G := ZeroOneOmega
abbrev GTy := Obend.Core.GradedSessionMetatheory.Ty G

example : ¬ ZeroOneOmega.le .zero .one := by decide
example : ZeroOneOmega.le .zero .omega := by decide
example : ¬ ZeroOneOmega.le (ZeroOneOmega.add .one .one) .one := by decide
example : ZeroOneOmega.le (ZeroOneOmega.add .omega .omega) .omega := by decide
example : ZeroOneOmega.add .one .zero = .one ∧ ZeroOneOmega.add .one .one = .omega := by decide

/-! ## A linear capability is used exactly once -/

/-- A channel endpoint that sends one Boolean. -/
def capTy : GTy := .chan (.send .one .bool .endS)

/-- `fun (c :¹ chan) => c`: the capability is handed on. -/
def handOn : Tm G := .lam .one capTy (.var 0)

theorem handOn_typed :
    HasTy [] handOn (.arr .one capTy capTy) (Usage.tail (Usage.single 0)) :=
  .lam (.var (by rfl)) (by simp [Usage.single, ZeroOneOmega.le])

example : handOn.occ 0 = 0 ∧ (Tm.var 0 : Tm G).occ 0 = 1 := by decide

/-- No weakening: a linear capability may not be dropped. -/
theorem linear_drop_untypable :
    ¬ ∃ T U, HasTy ([] : List GTy) (.lam .one capTy .unit) T U := by
  rintro ⟨T, U, h⟩
  have once := (binder_discipline h).1 rfl
  simp [Tm.occ] at once

/-- No contraction: a linear Boolean may not be read three times. -/
theorem linear_duplicate_untypable :
    ¬ ∃ T U, HasTy ([] : List GTy) (.lam .one .bool (.ite (.var 0) (.var 0) (.var 0))) T U := by
  rintro ⟨T, U, h⟩
  have once := (binder_discipline h).1 rfl
  simp [Tm.occ] at once

/-- The same body at `ω` is fine. -/
theorem unrestricted_duplicate_typed :
    HasTy ([] : List GTy) (.lam .omega .bool (.ite (.var 0) (.var 0) (.var 0)))
      (.arr .omega .bool .bool) (Usage.tail (Usage.add (Usage.single 0) (Usage.single 0))) :=
  .lam (.ite (.var (by rfl)) (.var (by rfl)) (.var (by rfl)))
    (by simp [Usage.add, Usage.single, ZeroOneOmega.add, ZeroOneOmega.le])

/-- A ghost binder cannot be read at run time. -/
theorem ghost_read_untypable :
    ¬ ∃ T U, HasTy ([] : List GTy) (.lam .zero .bool (.var 0)) T U := by
  rintro ⟨T, U, h⟩
  have never := (binder_discipline h).2 rfl
  simp [Tm.occ] at never

/-! ## Erasure -/

/-- `(fun (g :⁰ bool) => true) false`: the argument is a ghost. -/
def ghostCall (argument : Tm G) : Tm G := .app .zero (.lam .zero .bool (.bool true)) argument

theorem ghostCall_typed :
    HasTy ([] : List GTy) (ghostCall (.bool false)) .bool
      (Usage.add (Usage.tail Usage.zero) (Usage.scale .zero Usage.zero)) :=
  .app (.lam .bool (by simp [Usage.zero, ZeroOneOmega.le])) .bool

theorem ghostCall_runs : Steps (ghostCall (.bool false)) (.bool true) :=
  .head .beta (.refl _)

example : (ghostCall (.bool false)).erase = .app .zero (.lam .zero .bool (.bool true)) .ghost := by
  simp [ghostCall, Tm.erase, erasable]

/-- The erased call computes the same answer whatever the ghost argument was. -/
example : Steps (ghostCall (.bool true)).erase (.bool true) :=
  qtt_zero_grade_noninterference ghostCall_typed ghostCall_runs

example : Steps (ghostCall (.bool false)).erase (Tm.bool true : Tm G).erase :=
  qtt_zero_grade_erasure_sound ghostCall_typed ghostCall_runs

/-! ## Sessions -/

/-- Send a Boolean, then offer `ok` (done) or `retry` (receive a unit, done). -/
def proto : SessionTy G :=
  .send .one .bool (.offer (.cons "ok" .endS (.cons "retry" (.recv .one .unit .endS) .nil)))

example : proto.dual =
    .recv .one .bool (.select (.cons "ok" .endS (.cons "retry" (.send .one .unit .endS) .nil))) := by
  simp [proto, SessionTy.dual, Branches.dual]

example : proto.dual.dual = proto := SessionTy.dual_dual proto

theorem proto_wellFormed : proto.WellFormed := by
  simp [proto, SessionTy.WellFormed, Branches.WellFormed]

def okRun : List (Action G) := [.send .one .bool, .offer "ok"]

theorem okTrace : Trace proto okRun .endS :=
  .step .send (.step (.offer (by simp [Branches.find])) (.done _))

/-- The peer follows with the co-actions and ends too. -/
example : Trace proto.dual (okRun.map Action.co) (SessionTy.endS : SessionTy G).dual := okTrace.dual

example : ∃ a S' T', SStep proto a S' ∧ SStep proto.dual a.co T' ∧ T' = S'.dual := by
  rcases wellTyped_dual_endpoints_progress proto_wellFormed rfl with ended | moves
  · simp [proto, SessionTy.isEnd] at ended
  · exact moves

/-- Without well-formedness progress fails: an empty offer has not ended and cannot move. -/
theorem empty_offer_stuck :
    (SessionTy.offer .nil : SessionTy G).isEnd = false ∧
      ¬ ∃ a S', SStep (.offer .nil : SessionTy G) a S' := by
  refine ⟨by simp [SessionTy.isEnd], ?_⟩
  rintro ⟨a, S', h⟩
  cases h with
  | offer found => simp [Branches.find] at found

/-! ## Settlement on CapTP -/

def freshHole : GuardedHole := ⟨SortedU64Set.empty, SortedU64Set.empty⟩

theorem freshHole_unspent (k : PendingId) : ¬ freshHole.spentNullifiers.spec k := by
  simp [freshHole, SortedU64Set.spec, SortedU64Set.empty]

/-- A completed session settles its promise once. -/
example : countResolved freshHole (sessionEvents 7 okRun (SessionTy.endS : SessionTy G)) 7 = 1 := by
  rw [session_capTP_settlement freshHole 7 (freshHole_unspent 7)]
  rfl

/-- An endpoint abandoned after the send never settles: the promise stays open. -/
example : countResolved freshHole
    (sessionEvents 7 [Action.send .one .bool]
      (.offer (.cons "ok" .endS .nil) : SessionTy G)) 7 = 0 := by
  rw [session_capTP_settlement freshHole 7 (freshHole_unspent 7)]
  rfl

/-- Replaying the close does not settle twice. -/
example : countResolved freshHole
    (sessionEvents 7 okRun (SessionTy.endS : SessionTy G) ++ [.resolve 7, .resolve 7]) 7 ≤ 1 :=
  session_capTP_at_most_once freshHole 7 okRun .endS _

/-! ## Surface elaboration -/

def typeOf? {env : Env} {scope : Scope} {source : Surface} :
    Except Diagnostic (Elaborated env scope source) → Option Obend.Core.Ty.Ty
  | .ok out => some out.type
  | .error _ => none

def termOf? {env : Env} {scope : Scope} {source : Surface} :
    Except Diagnostic (Elaborated env scope source) → Option Obend.Core.Term.Term
  | .ok out => some out.term
  | .error _ => none

def obligationsOf? {env : Env} {scope : Scope} {source : Surface} :
    Except Diagnostic (Elaborated env scope source) → Option (List Obligation)
  | .ok out => some out.residual.obligations
  | .error _ => none

def diagnosticOf? {α : Type} : Except Diagnostic α → Option Diagnostic
  | .ok _ => none
  | .error diagnostic => some diagnostic

/-- An ambient effect row with two actions. -/
def effEnv : Env :=
  { planRow := .field "log" .natural (.field "audit" .boolean .emptyRow), response := .natural }

def accountRow : Obend.Core.Ty.Ty := .field "balance" .natural (.field "open" .boolean .emptyRow)

def account : Surface := .record (.cons "balance" (.nat 10) (.cons "open" (.bool true) .nil))

example : typeOf? (synthSurface {} [] account) = some accountRow := by decide +kernel

example : typeOf? (synthSurface {} [] (.member account "balance")) = some .natural := by
  decide +kernel

example : typeOf? (synthSurface {} []
    (.extend account (.cons "owner" (.nat 1) .nil))) =
    some (.field "owner" .natural accountRow) := by decide +kernel

/-- Missing row label, named with the row it is missing from. -/
example : diagnosticOf? (synthSurface {} [] (.member account "owner")) =
    some (.rowLabelMissing "owner" accountRow) := by decide +kernel

/-- Unbound variable. -/
example : diagnosticOf? (synthSurface {} [] (.var "x")) = some (.unboundVariable "x") := by
  decide +kernel

example : resolve [("x", ⟨.natural, .linear⟩), ("y", ⟨.boolean, .unrestricted⟩)] "y" = some 1 := by
  decide +kernel

/-- A linear binder used once elaborates to the core lambda. -/
example : typeOf? (synthSurface {} [] (.lam "c" .linear .once (some .natural) (.var "c"))) =
    some (.arrow .once .linear .natural .natural) := by decide +kernel

example : (match termOf? (synthSurface {} [] (.lam "c" .linear .once (some .natural) (.var "c"))) with
    | some (.lam (.bound 0)) => true
    | _ => false) = true := by decide +kernel

/-- Dropped: the linearity refusal names the binder, its quantity and the count 0. -/
example : diagnosticOf? (synthSurface {} [] (.lam "c" .linear .once (some .natural) (.nat 0))) =
    some (.linearityViolation "c" .linear 0) := by decide +kernel

/-- Duplicated: the count is 2. -/
example : diagnosticOf? (synthSurface {} []
    (.lam "c" .linear .once (some .natural)
      (.record (.cons "a" (.var "c") (.cons "b" (.var "c") .nil))))) =
    some (.linearityViolation "c" .linear 2) := by decide +kernel

/-- Bidirectional: an unannotated lambda is refused in synthesis and accepted against an arrow. -/
example : diagnosticOf? (synthSurface {} [] (.lam "x" .unrestricted .reusable none (.var "x"))) =
    some (.missingAnnotation "x") := by decide +kernel

example : diagnosticOf? (checkSurface {} [] (.lam "x" .unrestricted .reusable none (.var "x"))
    (.arrow .reusable .unrestricted .natural .natural)) = none := by decide +kernel

example : diagnosticOf? (checkSurface {} [] (.nat 3) .boolean) =
    some (.typeMismatch .boolean .natural) := by decide +kernel

/-- `let` and a call. -/
example : typeOf? (synthSurface {} []
    (.letE "id" .unrestricted none (.lam "x" .unrestricted .reusable (some .natural) (.var "x"))
      (.call (.var "id") (.nat 3)))) = some .natural := by decide +kernel

/-- An effect in the ambient row elaborates to an activity over that row. -/
example : typeOf? (synthSurface effEnv [] (.perform "log" (.nat 1))) =
    some (.computation (.variant effEnv.planRow) .natural .natural) := by decide +kernel

example : (match termOf? (synthSurface effEnv [] (.perform "log" (.nat 1))) with
    | some (.perform (.inject "log" (.nat 1))) => true
    | _ => false) = true := by decide +kernel

/-- Effect leak: `launch` is not an action of the row, here or under a binder. -/
example : diagnosticOf? (synthSurface effEnv [] (.perform "launch" (.nat 1))) =
    some (.effectLeak "launch" effEnv.planRow) := by decide +kernel

example : diagnosticOf? (synthSurface effEnv []
    (.lam "x" .unrestricted .once (some .natural) (.perform "launch" (.var "x")))) =
    some (.effectLeak "launch" effEnv.planRow) := by decide +kernel

example : ¬ EffectIn effEnv "launch" :=
  (effectAllowed_none_iff effEnv "launch").1 (by decide +kernel)

example : EffectIn effEnv "audit" := ⟨.boolean, 3, by decide +kernel⟩

/-- A law leaves its obligation, with the row of its subject. -/
def nonNegative : Obend.Spec.Law.LawExpr := .leC (.field "balance") 100

example : obligationsOf? (synthSurface {} [] (.law "cap" nonNegative account)) =
    some [⟨"cap", nonNegative, accountRow⟩] := by decide +kernel

example : (Surface.law "cap" nonNegative account).laws = [("cap", nonNegative)] := by
  decide +kernel

/-- A law that reads a field its subject lacks is refused, naming the field. -/
example : diagnosticOf? (synthSurface {} []
    (.law "owned" (.leC (.field "owner") 1) account)) =
    some (.lawOutsideRow "owned" "owner" accountRow) := by decide +kernel

/-- Two laws, two obligations, in order. -/
example : (obligationsOf? (synthSurface {} []
    (.law "outer" (.monotone "balance") (.law "cap" nonNegative account)))).map
      (·.map Obligation.key) =
    some [("outer", .monotone "balance"), ("cap", nonNegative)] := by decide +kernel

/-- The front end's `perform.log(true)` is the effect form. -/
example : ((ofSyntax (fun _ => none) 8
    (.call (.member (.var "perform") "log") [.bool true])).toOption.map Surface.effects) =
    some ["log"] := by decide +kernel

example : (match ofSyntax (fun _ => none) 4 (.nat "42") with
    | .ok (.nat 42) => true
    | _ => false) = true := by decide +kernel

example : diagnosticOf? (ofSyntax (fun _ => none) 4 (.nat "4x")) =
    some (.unsupported "numeral") := by decide +kernel

/-- A contract's law becomes the assertion over its step. -/
example : ((ofContract (fun _ => none)
    { name := "cap", targetType := "Account", law := some nonNegative,
      step := some (.record [("balance", .bool true)]) }).toOption.map Surface.laws) =
    some [("cap", nonNegative)] := by decide +kernel

example : (ofPTy (.arrow "once" "linear" .natural .boolean)).toOption =
    some (.arrow .once .linear .natural .boolean) := by decide +kernel

example : diagnosticOf? (ofPTy (.arrow "sometimes" "linear" .natural .boolean)) =
    some (.unknownAnnotation "sometimes") := by decide +kernel

/-! ## Teeth -/

#tooth linear_cap_used_exactly_once by mutation ZeroOneOmega.add :=
  fun a b => match a, b with
    | .zero, g => g
    | g, .zero => g
    | .one, .one => .one
    | _, _ => .omega

#tooth qtt_zero_grade_erasure_sound by mutation erasable := fun _ => true

#tooth session_step_preserves_duality by mutation Action.co := fun a => a

#tooth wellTyped_dual_endpoints_progress by mutation SessionTy.isEnd := fun _ => false

#tooth session_capTP_settlement by mutation sessionEvents :=
  fun k actions _ => PromiseEvent.allocate k :: actions.map (fun _ => PromiseEvent.deliver k)

#tooth effectAllowed_sound by mutation effectAllowed := fun _ _ => some Obend.Core.Ty.Ty.natural

#tooth lawScope_sound by mutation lawScope := fun _ _ _ => none

#tooth law_obligations_enforce by mutation obligationsHold := fun _ _ _ _ => true

#tooth resolve_sound by mutation resolve := fun _ _ => some 0

/-! Delegation moves a live endpoint, including a nonterminal delegated session. -/
def delegated : SessionTy G := .send .one .bool .endS
example : HasTy [.chan delegated] (.var 0) (.chan delegated) (Usage.single 0) := .var rfl
theorem delegation_moves_once :
    let payload : Tm G := .var 0
    let after := Tm.pair .one (.var 0) (.pair .one (payload.shift 0 |>.shift 0) (.var 1))
    HasTy [.chan .endS, .chan .endS, .chan delegated] after
      (.tensor .one (.chan .endS) (.tensor .one (.chan delegated) (.chan .endS)))
      (communicationUsage .one (Usage.single 0)) :=
  (delegated_channel_subject_reduction (S := .endS)
    (HasTy.var (Γ := [.chan delegated]) (i := 0) rfl)).2.2.1
example : communicationUsage .one (Usage.single 0) 2 = .one := by decide +kernel
example : (Tm.send .one (.var 0) (.var 0) : Tm G).occ 0 = 2 := by decide +kernel
example : HasTy ([.chan .endS] : List GTy) (.close (.var 0)) .unit (Usage.single 0) := .close (.var rfl)
example : HasTy ([.chan .endS] : List GTy) (.wait (.var 0)) .unit (Usage.single 0) := .wait (.var rfl)
example : Step (Tm.letPair .one (.lam .one .bool (.lam .one .unit (.var 1)))
    (.pair .one (.bool true) .unit) : Tm G)
    (.app .one (.app .one (.lam .one .bool (.lam .one .unit (.var 1))) (.bool true)) .unit) := .pairBeta

example : Quantity.linear.toZeroOneOmega = .one ∧ Quantity.erased.toZeroOneOmega = .zero := by decide +kernel
example : (checkSurfaceQtt {} []
    (.lam "x" .linear .once (some .boolean) (.var "x"))
    (.arrow .once .linear .boolean .boolean)).isSome = true := by decide +kernel
example : (checkSurfaceQtt {} []
    (.lam "x" .erased .once (some .boolean) (.bool true))
    (.arrow .once .erased .boolean .boolean)).isSome = true := by decide +kernel
example : (checkSurfaceQtt {} []
    (.lam "x" .linear .once (some .boolean) (.bool true))
    (.arrow .once .linear .boolean .boolean)).isNone = true := by decide +kernel
example : (checkSurfaceQtt {} []
    (.lam "x" .affine .once (some .boolean) (.bool true))
    (.arrow .once .affine .boolean .boolean)).isNone = true := by decide +kernel

example : Rendezvous [.chan .endS, .chan .endS] closePair [] closedPair := .close []
example : HasTy ([] : List GTy) closedPair (.tensor .one .unit .unit) Usage.zero :=
  (close_wait_subject_reduction []).2.2

-- Pair elimination consumes its continuation at grade one, even when its payload is erased.
def consumeGhost : Tm G := .lam .zero .bool (.lam .one (.chan .endS) (.close (.var 0)))
theorem consumeGhost_typed :
    HasTy [] consumeGhost (.arr .zero .bool (.arr .one (.chan .endS) .unit)) Usage.zero := by
  have h := HasTy.lam (Γ := []) (π := ZeroOneOmega.zero)
    (HasTy.lam (π := ZeroOneOmega.one) (HasTy.close (HasTy.var (Γ := [.chan .endS, .bool]) (i := 0) rfl))
      (by simp [Usage.single, ZeroOneOmega.le]))
    (by simp [Usage.tail, Usage.single, ZeroOneOmega.le])
  have hz : Usage.tail (Usage.tail (Usage.single 0 : Usage G)) = Usage.zero := by
    funext n; simp [Usage.tail, Usage.single, Usage.zero]
  rw [hz] at h
  exact h
example :
    HasTy [.chan .endS] (.app .one (.app .zero (consumeGhost.shift 0) (.bool true)) (.var 0)) .unit
      (Usage.add (Usage.insertAt 0 .zero Usage.zero)
        (Usage.add (Usage.single 0) (Usage.scale .zero Usage.zero))) := by
  have h := HasTy.letPair (consumeGhost_typed.weaken (Γ₁ := []) (.chan .endS))
    (HasTy.pair (q := ZeroOneOmega.zero) (HasTy.var (i := 0) rfl) (HasTy.bool (v := true)))
  exact (qtt_step_preserves_typing_and_linear_caps h Step.pairBeta).1

example : (checkSurfaceQtt {} []
    (.call (.lam "x" .linear .once (some .boolean) (.var "x")) (.bool true))
    .boolean).isSome = true := by decide +kernel
example : (checkSurfaceQtt {} []
    (.letE "x" .linear none (.bool true) (.var "x")) .boolean).isSome = true := by decide +kernel
#tooth Quantity.fits_qtt_iff by mutation Quantity.toZeroOneOmega := fun _ => .omega

#tooth Rendezvous.erase by mutation erasable := fun _ => false
#tooth delegated_channel_subject_reduction by mutation Tm.occ := fun _ _ => 0
#tooth Quantity.toZeroOneOmega_left_inverse by mutation Quantity.toZeroOneOmega := fun _ => .omega
#tooth checkSurface_qtt_grade_bridge by mutation Tm.occ := fun _ _ => 0

/-! ## Cross-module synergy witnesses (`BidirectionalSurfaceElab` ↔ `GradedSessionMetatheory` ↔ `Cubical2LTT`) -/

example : quantityToStageGrade .erased = .zero ∧
    quantityToStageGrade .linear = .one ∧
    quantityToStageGrade .unrestricted = .one := by decide +kernel

example : Obend.Core.Cubical2LTT.runStageOne [10]
    (bindByQttStage .zero (.varZero 0) (.varOne 0)) = 10 := by decide +kernel

example : Obend.Core.Cubical2LTT.runStageOne [10]
    (bindByQttStage .one (.litU64 7) (.addU64 (.varOne 0) (.varOne 1))) = 17 := by decide +kernel

example :
    ∃ ctx out,
      checkSurfaceQtt {} [] (.lam "x" .linear .once (some .boolean) (.var "x"))
        (.arrow .once .linear .boolean .boolean) = some ⟨ctx, out⟩ ∧
      Obend.Core.Cubical2LTT.ApproxRun
        [.affine 1 0 2 1, .affine (-3) 4 1 2]
        (Int.ofNat (Obend.Core.Cubical2LTT.runStageOne [10]
          (bindByQttStage .zero (.varZero 0) (.varOne 0))).toNat)
        (-33) := by
  cases h : checkSurfaceQtt {} [] (.lam "x" .linear .once (some .boolean) (.var "x"))
      (.arrow .once .linear .boolean .boolean) with
  | none =>
    have hs : (checkSurfaceQtt {} [] (.lam "x" .linear .once (some .boolean) (.var "x"))
      (.arrow .once .linear .boolean .boolean)).isSome = true := by decide +kernel
    rw [h] at hs; cases hs
  | some p =>
    exact ⟨p.1, p.2, rfl,
      .cons (y := 12) (by decide) (.cons (y := -33) (by decide) (.nil _))⟩

#tooth qtt_erasable_iff_stageZero by mutation qttToStageGrade := fun _ => .one
#tooth bindByQttStage_wellStaged by mutation bindByQttStage := fun _ p r => .letOne p r
#tooth surface_qtt_cubical_delegated_synergy by mutation bindByQttStage := fun _ p r => .letOne p r

#assert_axioms_tree

end Obend.Tests.GradedSessionAndSurfaceElab

end
