module
/-
# `Obend.Teeth.Extracted.RunLeafLowerTeeth` — Run & Lower Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (38 mutation witnesses) extracted from
Tier-1 `Obend` modules so `lake build Obend` elaborates pure definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Core.Brand
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Proofs.Collect.Statements
import all Obend.Core.Proofs.Force
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Proofs.Settle
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Lrat
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Run
import all Obend.Law.Syntax
import all Obend.Leaf.BytecodeRegisterJit
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Specialize
import all Obend.Leaf.UpTo
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.Obligation
import all Obend.Lower.Fragment
import all Obend.Lower.Inductive
import all Obend.Lower.Judge
import all Obend.Lower.LCNF
import all Obend.Lower.LeanKernel
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Proofs.Complete
import all Obend.Lower.Reflect
import all Obend.Lower.Transport
import all Obend.Reasons
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.ControlExample
import all Obend.Run.Core4
import all Obend.Run.Durable
import all Obend.Run.DurableExample
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.ForkExample
import all Obend.Run.HyperLaw
import all Obend.Run.LawJudge
import all Obend.Run.Negotiation
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Core4
import all Obend.Run.Proofs.Durable
import all Obend.Run.Proofs.Interpret
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.SharedExample
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Negotiation
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Tactic.Cases

public section
end

namespace Obend.Teeth.Extracted.RunLeafLowerTeeth
/-! ## Extracted from `Obend.Run.ControlExample` (2 teeth) -/
section Obend_Run_ControlExample
open Obend.Run.ControlExample
open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control
open Obend.Run.Negotiation (decOp reserveOp commitOp)

-- Without the office in a `whileInOffice` decision's citations, Alice's choice dispatches after she
-- has left office.
#tooth editorial_receipt by mutation citesFor := fun {_ _ _} S _ _ c => S.supports c

#tooth latch_receipt by mutation latchedOf := fun {_ _ _ _} [_] [_] {_ _ _ _ _ _} _ {_} _ _ {_} _ => false

end Obend_Run_ControlExample

/-! ## Extracted from `Obend.Run.DurableExample` (1 teeth) -/
section Obend_Run_DurableExample
open Obend.Run.DurableExample
open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control Obend.Run.Shared
open Obend.Run.Durable Obend.Run.SharedExample
open Obend.Run.Negotiation (Wv host O₀ ctl au stored₀ NCand commitOp)

-- A recovery that forgets the journal admits Bob after the restart.
#tooth Obend.Run.DurableExample.restart_receipt by mutation Obend.Run.Durable.replay :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} [_] [_] [_] [_] [_] [_] _ _ _ _ _ {_} J _ => some J

end Obend_Run_DurableExample

/-! ## Extracted from `Obend.Run.ForkExample` (4 teeth) -/
section Obend_Run_ForkExample
open Obend.Run.ForkExample
open Obend.Slot.Protocol.Negotiation (Tok sig spec)
open Obend.Run.Negotiation (ctl au commitOp)
open Obend.Run.Shared Obend.Run.Fork Obend.Run.SharedExample

-- A fork that may spend shared tokens grants the capability twice.
#tooth Obend.Run.ForkExample.fork_refuses by mutation Obend.Run.Fork.forkStep :=
  fun {_ _ _ _} [_] _ _ F r => match r with
    | .spend _ t => .ok { F with spentHere := F.spentHere ++ [t] }
    | .grow m => .ok { F with grown := F.grown ++ [m] }
    | .mint t => .ok { F with own := F.own ++ [t] }
    | .defer e => .ok { F with escalated := F.escalated ++ [e] }

-- Without the shared mask, Bob's runner admits his escalated commitment and it is granted too.
#tooth Obend.Run.ForkExample.bob_offline_conflict by mutation Obend.Run.Shared.sharedLive :=
  fun {_ _ _ _} [_] _ base d t => (base (Obend.Run.Shared.Ledger.raw _ d)).live t

-- The former stitch: each escalated row a commit through the ledger's step alone, bypassing the
-- runner. Bob is granted the capability at a main where he never reserved.
#tooth Obend.Run.ForkExample.runner_judges_escalation by mutation Obend.Run.Fork.jstep :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} [_] [_] [_] [_] [_] [_] L _ sp _ _ {_} J e =>
    match Obend.Run.Shared.ledgerStep L J.led (Obend.Run.Shared.ledgerRowOf L (sp e.1) J.led e.1 e.2) with
    | .ok d => .ok { J with led := d }
    | .error c => .error (.ledger c)

-- A non-atomic settlement: the first commitment stays committed although the second was refused.
#tooth Obend.Run.ForkExample.two_step_atomic by mutation Obend.Run.Fork.settle :=
  fun {_ _ _} _ tentative _ => tentative

end Obend_Run_ForkExample

/-! ## Extracted from `Obend.Run.SharedExample` (3 teeth) -/
section Obend_Run_SharedExample
open Obend.Run.SharedExample
open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control Obend.Run.Shared
open Obend.Run.Negotiation (Wv everything stepW host O₀ ctl au stored₀ NCand reserveOp commitOp)

-- Without the shared mask, Bob's commitment is admitted at his own view: two grants.
#tooth alice_wins by mutation sharedLive := fun {_ _ _ _} [_] _ base d t => (base (Ledger.raw _ d)).live t

-- Durability is a field: a record whose abandonment erases the consumption fails the obligation the
-- structure consumes, so it is not a `Ledger` (and `nledger` cannot be rebuilt over it).
#tooth ledgerAbandon_durable by mutation ledgerAbandon := fun d => ⟨d.raw, [], d.grants, d.height⟩

-- Without propagating the ledger's moves, Bob does not see Alice's commit.
#tooth coupled_after_commit by mutation propagate :=
  fun {_ _ _ _ _ _ _ _ _ _ _} _ {_} _ _ cs => .ok cs

end Obend_Run_SharedExample

/-! ## Extracted from `Obend.Run.HyperLaw` (3 teeth) -/
section Obend_Run_HyperLaw
open Obend.Run.HyperLaw

-- Mutating the per-step low-equivalence guard to ignore leaks breaks `checkHyperLaw2NonInterference_sound`.
#tooth checkHyperLaw2NonInterference_sound by mutation checkHyperLaw2Step :=
  fun {_ _} [_] _ _ => true

-- Mutating the fixed-point equivalence check to `true` breaks `checkGLEquilibrium_sound`.
#tooth checkGLEquilibrium_sound by mutation checkFactSetEquiv :=
  fun _ _ => true

-- Mutating `findOddSelfLoop?` to claim even `defaultBirdProg` is an odd loop breaks `checkGLEquilibrium_refuted`.
#tooth checkGLEquilibrium_refuted by mutation findOddSelfLoop? :=
  fun _ => some "bird"

end Obend_Run_HyperLaw

/-! ## Extracted from `Obend.Run.LawJudge` (2 teeth) -/
section Obend_Run_LawJudge
open Obend.Run
open Obend.Slot Obend.Slot.Protocol
open Obend.Law (Blame judgeEffective effective Admits RefusesAs closedB Submission Consensus sealAt seal_future)
open Obend.Core.Term (Term)
open Obend.Core.Data (Data Budget)
open Obend.Core.Machine (State Limits)

#tooth checkLawSubmission_sound by mutation
  checkLawSubmission := fun _ _ _ => .ok

#tooth checkLawSubmission_refuted by mutation
  checkLawSubmission := fun _ _ _ => .refused (.futureSubmission 1 0) []

end Obend_Run_LawJudge

/-! ## Extracted from `Obend.Run.Negotiation` (8 teeth) -/
section Obend_Run_Negotiation
open Obend.Run Obend.Run.Negotiation Obend.Run.Ticket
open Obend.Slot Obend.Slot.Protocol Obend.Slot.Protocol.Negotiation Obend.Run.Control

-- Without the replan guard the three replans in flight are not refused by name (the cancellation
-- and the return to `p1` become `inconsistent`, and the same-first-call `planFlip` is ACCEPTED).
#tooth receipt by mutation frozenHole := fun {_ _ _ _} [_] {_ _ _ _} _ => none

-- Without durable spending the capability the world calls live again is unspent.
#tooth stayed by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent

#tooth withdrawn_refused by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => true

#tooth reserve_retry_refused by mutation awaiting := fun {_ _} _ => none

#tooth abandon_ends by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none

#tooth decision_rechecked by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

#tooth initial_decision_rechecked by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

#tooth second_use_refused by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent

end Obend_Run_Negotiation

/-! ## Extracted from `Obend.Run.Proofs.Core4` (1 teeth) -/
section Obend_Run_Proofs_Core4
open Obend.Run Obend.Run.Core4
open Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data

#tooth session_of_transcript by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => false

end Obend_Run_Proofs_Core4

/-! ## Extracted from `Obend.Run.Proofs.Interpret` (1 teeth) -/
section Obend_Run_Proofs_Interpret
open Obend.Run
open Obend.Slot Obend.Slot.Protocol

-- Completeness rests on the dispatch guard admitting what the judgment and the world support.
#tooth drive_complete by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => false

end Obend_Run_Proofs_Interpret

/-! ## Extracted from `Obend.Run.Proofs.Invariant` (9 teeth) -/
section Obend_Run_Proofs_Invariant
open Obend.Run
open Obend.Slot Obend.Slot.Protocol

-- Each guard is load-bearing in the induction step: the stored proof fails without it.
#tooth step_inv by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => true

#tooth step_inv by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent

#tooth step_inv by mutation frozenHole := fun {_ _ _ _} [_] {_ _ _ _} _ => none

#tooth step_inv by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none

#tooth step_inv by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

-- The no-new-commitment guard is what refuses a dispatch while a reply is missing.
#tooth inflight_busy by mutation awaiting := fun {_ _} _ => none

-- Acceptance of a safe replacement rests on the replan's consistency check passing.
#tooth replan_accepted by mutation nextIs := fun {_ _ _ _} [_] _ _ => false

#tooth replace_then_dispatch by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => false

#tooth ended_frozen by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none

end Obend_Run_Proofs_Invariant

/-! ## Extracted from `Obend.Lower.LeanKernel` (1 teeth) -/
section Obend_Lower_LeanKernel
open Obend.Lower.LeanKernel
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Leaf
open Obend.Lower
open Obend.Lower.Inductive

/-- Broken `etaDomCompat` that defaults `none ↦ true` (unsoundly permitting $\eta$-expansion
against untyped free variables or ill-typed terms). -/
private def etaDomCompatFailOpen (env : KEnv) (fuel : Nat)
    (inferPrev : List KExpr → KExpr → Option KExpr)
    (defEqPrev : List KExpr → KExpr → KExpr → Bool)
    (ctx : List KExpr) (dom other : KExpr) : Bool :=
  match inferPrev ctx other with
  | some otherTy =>
    match kernelWhnf env fuel otherTy with
    | .forallE otherDom _ => defEqPrev ctx dom otherDom
    | _ => false
  | none => true

#tooth etaDomCompat_fail_closed_sound by mutation etaDomCompat := etaDomCompatFailOpen

end Obend_Lower_LeanKernel

/-! ## Extracted from `Obend.Lower.Reflect` (3 teeth) -/
section Obend_Lower_Reflect
open Obend.Lower.Reflect
open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty)
open Obend.Logic (Composition)
open Obend.Leaf (LeafDef LeafPin LeafView specSlot Candidate moved_pin_blocks)
open Obend.Slot.World (holdsAt)
open Obend.Lower (LExpr lowerT)

#tooth fusedPrototypeSlot_sound_and_conservative by mutation
  fusedPrototypeJudge := fun _ _ _ => true

#tooth fusedPrototypeSlot_override_outside_usable by mutation
  overrideMethodView := fun v _ newCode => { v with decl := fun _ => some newCode }

#tooth fusedPrototypeSlot_moved_pin_blocks by mutation
  overrideMethodView := fun v _ _ => v

end Obend_Lower_Reflect
end Obend.Teeth.Extracted.RunLeafLowerTeeth
