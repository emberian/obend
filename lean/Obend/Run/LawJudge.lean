module
/-
# Obend.Run.LawJudge — laws reach the runner

Until now a dispatched operation's authority came only from the deployment's `Spec`
(`REPORT-RUNNER-20261031.md` §9): `admitOp` checks the facts it requires and the token it spends.
Here the object's EFFECTIVE LAW (its own law and its parents', along their C4 precedence list,
`Obend.Law.Inherit`) judges every write a dispatch performs, by running the machine
(`Obend.Law.Machine.judgeEffective`), and the runner refuses what the law refuses, naming the
ancestor clause that refused.

Consensus time: the write an operation performs carries a `Submission`, never a request; the judge
seals it at the world's consensus (`consensus`, the ledger's height), so every law reads the
ledger's height and none reads a height the request chose. A submission claiming a height the ledger
has not reached is refused before any law runs: the fact `LawFact.current o` fails
(`dispatch_future_refused`).

Nothing in the runner changes. The law enters as FACTS: `LawFact.admitted o` (the machine's
verdict on the write `o` performs is `ok`) and `LawFact.clause o name` (the verdict is not a
refusal by ancestor `name`), embedded in the deployment's own fact type by a `LawJudge`, which
also says which write an operation performs at a world (`act`) and which law the object has
(`lin`). `lawHost` decides those facts by running the machine at the world; `lawSpec` adds them to
every operation's requirements: `admitted o`, then one `clause o name` per ancestor in precedence
order. So the existing runner, specification and invariant apply as they are (`reachable_legal`
at `lawHost`/`lawSpec`), and:

* `legal_law_admitted`: in every `Legal` log of the law-judged runner, every dispatched operation
  that performs a write was admitted by the effective law, i.e. by every ancestor's law, over the
  reference semantics (`Admits`, `Evaluates`).
* `legal_base_authorized`: the deployment's own authority is still enforced (`Authorized host sp`)
  when its requirements are not law facts.
* `dispatch_refused_names`: when the machine refuses the write by ancestor `name` with reason `why`,
  the runner refuses the dispatch `unadmitted`, its missing facts include `clause o name`, and
  `name` is on the precedence list, every law before it admitted, and its own law refused with
  `why`.
-/
public import Obend.Run.Spec
public import Obend.Law.Proofs.Machine
public import Obend.Run.Proofs.Invariant
import all Obend.Run.Runner
import all Obend.Run.Spec
@[expose] public section

namespace Obend.Run

open Obend.Slot Obend.Slot.Protocol
open Obend.Law (Blame judgeEffective effective Admits RefusesAs closedB Submission Consensus sealAt seal_future)
open Obend.Core.Term (Term)
open Obend.Core.Data (Data Budget)
open Obend.Core.Machine (State Limits)

/-- The facts the law contributes, about an operation `o`. -/
inductive LawFact (Op : Type) where
  /-- the machine's verdict on the write `o` performs is `ok` -/
  | admitted (o : Op)
  /-- the verdict on the write `o` performs is not a refusal by ancestor `name` -/
  | clause (o : Op) (name : String)
  /-- the write `o` performs claims no height the ledger has not reached -/
  | current (o : Op)
  deriving DecidableEq, Repr

/-- How an object's effective law judges a deployment's operations. -/
structure LawJudge (V Fact Op : Type) where
  /-- the law facts, as the deployment's facts -/
  embed : LawFact Op → Fact
  /-- which facts are law facts -/
  classify : Fact → Option (LawFact Op)
  classify_embed : ∀ x, classify (embed x) = some x
  /-- the write `o` performs at a world: old state, new state, the submission; `none` if it writes
  nothing -/
  act : V → Op → Option (Data × Data × Submission)
  /-- the ledger's consensus at a world: the height every law reads -/
  consensus : V → Consensus
  /-- the object's precedence list of named laws (`Obend.Law.Inherit.resolve` of its C4 linearization) -/
  lin : List (String × Term)
  /-- the machine the kernel judges with -/
  policy : State → Bool
  limits : Limits
  budget : Budget

section
variable {V Fact Op : Type}

/-- The machine's verdict on the write `o` performs at world `v`, its submission sealed at the
world's consensus (`ok` when it writes nothing; no verdict when the submission cannot be sealed). -/
def LawJudge.verdictAt (J : LawJudge V Fact Op) (v : V) (o : Op) : Option Blame :=
  match J.act v o with
  | none => some .ok
  | some (old, new, sub) =>
    match sealAt (J.consensus v) sub with
    | .ok rq => judgeEffective J.policy J.limits J.budget (effective J.lin) old new rq
    | .error _ => none

/-- Whether a law fact holds at world `v`. -/
def LawJudge.holds (J : LawJudge V Fact Op) (v : V) : LawFact Op → Bool
  | .admitted o => decide (J.verdictAt v o = some .ok)
  | .clause o name =>
    match J.verdictAt v o with
    | some (.refusedBy n _) => !decide (n = name)
    | _ => true
  | .current o =>
    match J.act v o with
    | some (_, _, sub) => (sealAt (J.consensus v) sub).toBool
    | none => true

/-- The host with the law's facts decided by running the machine at the world. -/
def lawHost {Tok : Type} (host : Host V Tok Fact) (J : LawJudge V Fact Op) : Host V Tok Fact where
  allowed := host.allowed
  view := fun v =>
    ⟨fun f => match J.classify f with
      | some x => J.holds v x
      | none => (host.view v).holds f,
     (host.view v).live⟩

/-- What the law adds to an operation's requirements: the write claims no future height, the verdict
is `ok`, and, in precedence order, no ancestor refused. -/
def lawRequires (J : LawJudge V Fact Op) (o : Op) : List Fact :=
  J.embed (.current o) :: J.embed (.admitted o) :: J.lin.map fun p => J.embed (.clause o p.1)

end

variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob V : Type}

/-- The deployment's spec with the law's requirements added to every operation. -/
def lawSpec (sp : Spec S Tok Fact Ob) (J : LawJudge V Fact (Σ i, S.Op i)) : Spec S Tok Fact Ob where
  consumes := sp.consumes
  requires := fun {i} op => sp.requires op ++ lawRequires J ⟨i, op⟩
  establishes := sp.establishes

/-! ## Admission under the law -/

theorem lawHost_holds_embed {host : Host V Tok Fact} {J : LawJudge V Fact (Σ i, S.Op i)} (v : V)
    (x : LawFact (Σ i, S.Op i)) : ((lawHost host J).view v).holds (J.embed x) = J.holds v x := by
  simp [lawHost, J.classify_embed]

theorem mask_holds {v : View Tok Fact} {spent : List Tok} [DecidableEq Tok] :
    (View.mask v spent).holds = v.holds := rfl

/-- A law-judged admission at a world's view has the machine's `ok` on the write. -/
public theorem admitOp_lawSpec_ok [DecidableEq Tok] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    {J : LawJudge V Fact (Σ i, S.Op i)} {v : V} {spent : List Tok} {i : Ix} {op : S.Op i}
    (h : admitOp (lawSpec sp J) (View.mask ((lawHost host J).view v) spent) op = true) :
    J.verdictAt v ⟨i, op⟩ = some .ok := by
  simp only [admitOp, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 (J.embed (.admitted ⟨i, op⟩)) (by simp [lawSpec, lawRequires])
  rw [mask_holds, lawHost_holds_embed] at this
  simpa [LawJudge.holds] using this

/-- **Laws reach the runner.** In every `Legal` log of the law-judged runner (in particular every
log it reaches: `reachable_legal`), every dispatched operation that performs a write was admitted,
at the world of its dispatch, by the object's effective law, that is by every law on its
precedence list, over the reference semantics. -/
public theorem legal_law_admitted [DecidableEq Tok] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    {J : LawJudge V Fact (Σ i, S.Op i)} (hc : ∀ p ∈ J.lin, closedB p.2 = true) {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {cs₀ : (j : Ix) → Hole j → List Fact}
    {log : List (Event S Hole A Fact V)} (legal : Legal (lawHost host J) (lawSpec sp J) O v₀ cs₀ log) :
    ∀ n o, log[n]? = some (.dispatch o) → ∀ old new sub,
      J.act (worldOf v₀ (log.take n)) o = some (old, new, sub) →
      ∃ rq, sealAt (J.consensus (worldOf v₀ (log.take n))) sub = .ok rq ∧
        Admits (effective J.lin) old new rq ∧ ∀ p ∈ J.lin, Admits p.2 old new rq := by
  intro n o hn old new sub hact
  have auth := legal.authorized n _ hn o rfl
  have ok := admitOp_lawSpec_ok (op := o.2) auth
  simp only [LawJudge.verdictAt, hact] at ok
  split at ok
  · rename_i rq hs
    have all := (Obend.Law.judgeEffective_names hc).1 ok
    exact ⟨rq, hs, (Obend.Law.effective_law_eval hc old new rq).2 all, all⟩
  · cases ok

/-- The tokens the law-judged spec spends are the deployment's. -/
theorem spentBy_lawSpec {sp : Spec S Tok Fact Ob} {J : LawJudge V Fact (Σ i, S.Op i)}
    (log : List (Event S Hole A Fact V)) : spentBy (lawSpec sp J) log = spentBy sp log := rfl

/-- **The deployment's authority is still enforced**: when none of its requirements is a law fact,
every dispatch of a law-judged `Legal` log was admitted by the deployment's spec too. -/
public theorem legal_base_authorized [DecidableEq Tok] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    {J : LawJudge V Fact (Σ i, S.Op i)}
    (hbase : ∀ (i : Ix) (op : S.Op i), ∀ f ∈ sp.requires op, J.classify f = none) {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {cs₀ : (j : Ix) → Hole j → List Fact}
    {log : List (Event S Hole A Fact V)} (legal : Legal (lawHost host J) (lawSpec sp J) O v₀ cs₀ log) :
    Authorized host sp v₀ log := by
  intro n z hn o hz
  subst hz
  have auth := legal.authorized n _ hn o rfl
  simp only [viewAt, spentBy_lawSpec, admitOp, Bool.and_eq_true, List.all_eq_true, mask_holds] at auth ⊢
  refine ⟨fun f hf => ?_, auth.2⟩
  have := auth.1 f (by simp [lawSpec, hf])
  simpa [lawHost, hbase _ _ f hf] using this

/-- An accepted dispatch appends itself to the log. -/
public theorem run_dispatch_log [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix]
    [∀ i, DecidableEq (Hole i)] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i} (h : run host sp c (.dispatch o) = .ok c') :
    c'.log = c.log ++ [.dispatch o] := by
  simp only [run] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · rename_i heq
          split at h
          · split at h
            · cases h; subst heq; rfl
            · cases h
          · cases h
        · cases h
      · cases h

/-- **Every reachable law-judged log is law-admitted**: `legal_law_admitted` at `reachable_legal`. -/
public theorem reachable_law_admitted [DecidableEq Tok] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]
    [DecidableEq (Σ i, S.Op i)] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    {J : LawJudge V Fact (Σ i, S.Op i)} (hc : ∀ p ∈ J.lin, closedB p.2 = true) {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {cs₀ : (j : Ix) → Hole j → List Fact}
    {c : Cfg S Hole A Tok Fact Ob V i} (h : Reachable (lawHost host J) (lawSpec sp J) (Cfg.init O v₀ cs₀) c) :
    ∀ n o, c.log[n]? = some (.dispatch o) → ∀ old new sub,
      J.act (worldOf v₀ (c.log.take n)) o = some (old, new, sub) →
      ∃ rq, sealAt (J.consensus (worldOf v₀ (c.log.take n))) sub = .ok rq ∧
        Admits (effective J.lin) old new rq ∧ ∀ p ∈ J.lin, Admits p.2 old new rq :=
  legal_law_admitted hc (reachable_legal h)

/-! ## A refusal names the ancestor -/

/-- **The runner's refusal names the ancestor clause.** At a configuration whose next call is
`op`, with nothing in flight and the run not ended, if the machine refuses the write `op` performs
by ancestor `name` with reason `why`, the runner refuses the dispatch `unadmitted`; the missing
facts include `clause op name`; and `name` is on the precedence list, every law before it
admitted, and its own law refused with reason `why`. -/
public theorem dispatch_refused_names [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix]
    [∀ i, DecidableEq (Hole i)] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    {J : LawJudge V Fact (Σ i, S.Op i)} (hc : ∀ p ∈ J.lin, closedB p.2 = true) {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} {j : Ix} {op : S.Op j} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
    (hres : c.res = ⟨j, .call op k⟩) (hend : c.ended = none) (hfree : c.obj.hist.inflight = none)
    {old new rq : Data} {sub : Submission} (hact : J.act c.world ⟨j, op⟩ = some (old, new, sub))
    (hseal : sealAt (J.consensus c.world) sub = .ok rq) {name why : String}
    (hv : judgeEffective J.policy J.limits J.budget (effective J.lin) old new rq = some (.refusedBy name why)) :
    (∃ missing dead, run (lawHost host J) (lawSpec sp J) c (.dispatch ⟨j, op⟩) =
        .error (.unadmitted ⟨j, op⟩ missing dead) ∧ J.embed (.clause ⟨j, op⟩ name) ∈ missing) ∧
      ∃ pre L post, J.lin = pre ++ (name, L) :: post ∧ (∀ q ∈ pre, Admits q.2 old new rq) ∧
        RefusesAs L old new rq why := by
  obtain ⟨pre, L, post, hlin, hpre, hL⟩ := (Obend.Law.judgeEffective_names hc).2 name why hv
  refine ⟨?_, pre, L, post, hlin, hpre, hL⟩
  have hverdict : J.verdictAt c.world ⟨j, op⟩ = some (.refusedBy name why) := by
    simp only [LawJudge.verdictAt, hact, hseal, hv]
  have hguard : dispatchGuard (lawSpec sp J) (c.admitView (lawHost host J)) op = false := by
    simp only [dispatchGuard, admitOp, Cfg.admitView, Bool.and_eq_false_iff]
    left
    simp only [List.all_eq_false]
    refine ⟨J.embed (.admitted ⟨j, op⟩), by simp [lawSpec, lawRequires], ?_⟩
    rw [mask_holds, lawHost_holds_embed]
    simp [LawJudge.holds, hverdict]
  refine ⟨(missingOf (lawSpec sp J) (c.admitView (lawHost host J)) op).1,
    (missingOf (lawSpec sp J) (c.admitView (lawHost host J)) op).2, ?_, ?_⟩
  · simp only [run, closedBy, hend, awaiting, hfree, hres, ↓reduceIte, hguard, Bool.false_eq_true]
  · simp only [missingOf, List.mem_filter, Bool.not_eq_true']
    refine ⟨by simp [lawSpec, lawRequires, hlin], ?_⟩
    simp only [Cfg.admitView, mask_holds, lawHost_holds_embed, LawJudge.holds, hverdict]
    simp

/-- **A submission from the future is refused before any law runs.** At a configuration whose next
call is `op`, with nothing in flight and the run not ended, if the write `op` performs claims a
height the world's consensus has not reached, the runner refuses the dispatch `unadmitted`, and the
missing facts include `current op`. -/
public theorem dispatch_future_refused [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix]
    [∀ i, DecidableEq (Hole i)] {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    {J : LawJudge V Fact (Σ i, S.Op i)} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} {j : Ix} {op : S.Op j} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
    (hres : c.res = ⟨j, .call op k⟩) (hend : c.ended = none) (hfree : c.obj.hist.inflight = none)
    {old new : Data} {sub : Submission} (hact : J.act c.world ⟨j, op⟩ = some (old, new, sub))
    {h : Nat} (hs : sub.seen = some h) (hlt : (J.consensus c.world).height < h) :
    ∃ missing dead, run (lawHost host J) (lawSpec sp J) c (.dispatch ⟨j, op⟩) =
      .error (.unadmitted ⟨j, op⟩ missing dead) ∧ J.embed (.current ⟨j, op⟩) ∈ missing := by
  have hcur : J.holds c.world (.current ⟨j, op⟩) = false := by
    simp [LawJudge.holds, hact, seal_future hs hlt, Except.toBool]
  have hguard : dispatchGuard (lawSpec sp J) (c.admitView (lawHost host J)) op = false := by
    simp only [dispatchGuard, admitOp, Cfg.admitView, Bool.and_eq_false_iff]
    left
    simp only [List.all_eq_false]
    refine ⟨J.embed (.current ⟨j, op⟩), by simp [lawSpec, lawRequires], ?_⟩
    rw [mask_holds, lawHost_holds_embed, hcur]
    simp
  refine ⟨(missingOf (lawSpec sp J) (c.admitView (lawHost host J)) op).1,
    (missingOf (lawSpec sp J) (c.admitView (lawHost host J)) op).2, ?_, ?_⟩
  · simp only [run, closedBy, hend, awaiting, hfree, hres, ↓reduceIte, hguard, Bool.false_eq_true]
  · simp only [missingOf, List.mem_filter, Bool.not_eq_true']
    refine ⟨by simp [lawSpec, lawRequires], ?_⟩
    simp only [Cfg.admitView, mask_holds, lawHost_holds_embed, hcur]

end Obend.Run

end
