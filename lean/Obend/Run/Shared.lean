module
/-
# Obend.Run.Shared — several runners over one World, through an atomic commit boundary

`astra/ASTRA-EFFECT-LAWS-20261031.md` §3 (Design B) and §9, built as the composition layer. Any
number of controlled runners (`Obend.Run.Control`, indexed by `ι`) share one authoritative record,
the LEDGER, whose laws are fields (`Ledger`): a commit records a token's consumption and its grant
(winner and epoch) in one step; a move of the raw world and an abandonment leave the consumption and
the grants as they were (the raw world may call a spent token live again; it cannot unspend it).
Consensus time is a field too: `height`, which a commit advances and no allowed move lowers; a
law judging a runner's write reads it (`Ledger.consensus`, `Obend.Run.LawJudge.consensus`), never a
height the request carries (`joint_height_mono`, `joint_consensus`). Durability is a field
(`abandon_spent`, `abandon_grants`): a record that releases on abandonment is
not a `Ledger` (the tooth `nledger` in `Obend.Run.SharedExample`). Each runner's host is built from
the ledger (`localHost`): it reads facts from the raw world and a token as live only while the raw
world says so AND the ledger has not consumed it (`sharedLive`, the shared mask).

The ledger is itself a member of the audited fold (`ledgerAdmission`, an `Obend.Fold.Admission`
over the record, whose rows are its moves: `commit`, `raw`, `abandon`, `observe`), with refusals of
its own (`LClause`: a commit of a consumed token is refused `taken`, naming the winner and the
epoch). The joint transition (`jrun`) is the family `members` (the ledger and every runner) stepping
interleaved rows:

- a raw world move is the ledger's row `raw w`; every runner observes the new record;
- a dispatch by runner `i` is (1) judged by `i`'s own runner at its view, which is the ledger's
  record (operation facts, decision citations, the token at the shared mask), then (2) the ledger's
  row: `commit i t` for the token the call consumes, `observe` (the record as it is) for a call
  that consumes none; (3) only then is the call exposed; every runner observes the ledger's record.
  A refusal for a token another runner holds names the winner and the epoch (`taken`);
- an abandonment is `i`'s own row, then the ledger's row `abandon i` (durable: nothing released);
- every other controlled event (`replyTo`, `advance`, `choose`) is `i`'s alone, a row of `i` that
  moves nothing, so no other member sees it.

The ledger's VIEW is committed (`viewReading`, `dated`): a Merkle map (`Obend.Receipt.Merkle`,
cSHAKE256 at `deployed`) over a public schema of facts and tokens, each at its bit at the shared view
(the raw world's fact; the token at the shared mask). A receipt of a member's row is dated by that
root and carries an opening proof per read (`Obend.Receipt.Naming.ofReading`), so the view a row
read is a checked support (`member_receipt_checks`, `member_receipt_dated_verdict`).

The theorems (`Obend.Run.Proofs.Shared`): the joint rows fold under the family (`jreachable_fold`),
so each runner's log is `Legal` by `Obend.Fold.project_moves_run` applied (projection), the ledger's
own rows fold from the start (`joint_ledger_fold`), the grants are exclusive and the consumption is
once globally, and the loser's refusal names the winner and the epoch.
-/
public import Obend.Run.Proofs.Control
public import Obend.Run.Fold
public import Obend.Receipt
public import Obend.Law.Syntax
public section

namespace Obend.Run.Shared

open Obend.Slot Obend.Slot.Protocol Obend.Run.Control

/-- A committed grant: the token, the runner that won it, and the epoch (the grant's position in
the ledger). -/
structure Grant (ι Tok : Type) where
  tok : Tok
  winner : ι
  epoch : Nat
  deriving DecidableEq, Repr

/-- The authoritative record several runners share, and its atomic commit boundary. -/
structure Ledger (ι W Tok : Type) where
  Rec : Type
  raw : Rec → W
  spent : Rec → List Tok
  grants : Rec → List (Grant ι Tok)
  /-- the raw world's own steps -/
  stepRaw : W → W → Bool
  /-- consume `t` for runner `i` and record the grant, atomically -/
  commit : Rec → ι → Tok → Rec
  /-- move the raw world -/
  setRaw : Rec → W → Rec
  /-- runner `i` abandoned its call in flight -/
  onAbandon : Rec → ι → Rec
  /-- the moves of the record every runner's host accepts -/
  allowed : Rec → Rec → Bool
  /-- CONSENSUS TIME: the ledger's height, the one clock every law reads (`Obend.Law.Consensus`) -/
  height : Rec → Nat
  commit_raw : ∀ d i t, raw (commit d i t) = raw d
  commit_spent : ∀ d i t, spent (commit d i t) = spent d ++ [t]
  commit_grants : ∀ d i t, grants (commit d i t) = grants d ++ [⟨t, i, (grants d).length⟩]
  setRaw_raw : ∀ d w, raw (setRaw d w) = w
  setRaw_spent : ∀ d w, spent (setRaw d w) = spent d
  setRaw_grants : ∀ d w, grants (setRaw d w) = grants d
  onAbandon_raw : ∀ d i, raw (onAbandon d i) = raw d
  allowed_refl : ∀ d, allowed d d = true
  allowed_commit : ∀ d i t, allowed d (commit d i t) = true
  allowed_setRaw : ∀ d w, stepRaw (raw d) w = true → allowed d (setRaw d w) = true
  allowed_onAbandon : ∀ d i, allowed d (onAbandon d i) = true
  /-- a commit is a new height -/
  commit_height : ∀ d i t, height (commit d i t) = height d + 1
  /-- no allowed move goes back in time -/
  allowed_height : ∀ d d', allowed d d' = true → height d ≤ height d'
  /-- DURABLE: an abandonment releases nothing (the call abandoned stays dispatched, its
  consumption and its grant stand) -/
  abandon_spent : ∀ d i, spent (onAbandon d i) = spent d
  abandon_grants : ∀ d i, grants (onAbandon d i) = grants d

/-- The consensus every law reads at a record: the ledger's height. -/
def Ledger.consensus {ι W Tok : Type} (L : Ledger ι W Tok) (d : L.Rec) : Obend.Law.Consensus := ⟨L.height d⟩

/-- The ledger is DURABLE (an abandonment releases nothing), as one proposition. Every `Ledger` is
(`Ledger.durable`): the law is a field. -/
structure Ledger.Durable {ι W Tok : Type} (L : Ledger ι W Tok) : Prop where
  spent : ∀ d i, L.spent (L.onAbandon d i) = L.spent d
  grants : ∀ d i, L.grants (L.onAbandon d i) = L.grants d

theorem Ledger.durable {ι W Tok : Type} (L : Ledger ι W Tok) : L.Durable :=
  ⟨L.abandon_spent, L.abandon_grants⟩

section
variable {ι W Tok Fact : Type} [DecidableEq Tok]

/-- The shared mask (a `#tooth` mutation target): a token is live only while the raw world says so
and the ledger has not consumed it. -/
def sharedLive (L : Ledger ι W Tok) (base : W → View Tok Fact) (d : L.Rec) (t : Tok) : Bool :=
  (base (L.raw d)).live t && !decide (t ∈ L.spent d)

/-- Every runner's host: facts from the raw world, tokens at the shared mask, moves the ledger's. -/
def localHost (L : Ledger ι W Tok) (base : W → View Tok Fact) : Host L.Rec Tok Fact where
  allowed := L.allowed
  view := fun d => ⟨(base (L.raw d)).holds, sharedLive L base d⟩

/-- The grant of `t`, if any. -/
@[expose] def grantOf (L : Ledger ι W Tok) (d : L.Rec) (t : Tok) : Option (Grant ι Tok) :=
  (L.grants d).find? fun g => decide (g.tok = t)

end

/-! ## The ledger as a member of the audited fold -/

/-- A row of the ledger: each one moves the record. -/
inductive LRow (ι W Tok R : Type) where
  /-- consume `t` for runner `i` and grant it -/
  | commit (i : ι) (t : Tok)
  /-- move the raw world to `w` -/
  | raw (w : W)
  /-- runner `i` abandoned its call in flight -/
  | abandon (i : ι)
  /-- the record moved to `d` by a move the ledger allows (`Obend.Fold.Admission.observe`) -/
  | observe (d : R)

/-- Why the ledger refused a row. -/
inductive LClause (ι Tok : Type) where
  /-- the token is consumed: granted to `winner` at `epoch` -/
  | taken (t : Tok) (winner : ι) (epoch : Nat)
  /-- the token is consumed and no grant names it (never, at a record a joint run reaches) -/
  | consumed (t : Tok)
  /-- the raw world does not step so -/
  | worldStep
  /-- the ledger does not allow the move -/
  | notAllowed
  deriving DecidableEq, Repr

section
variable {ι W Tok Fact : Type} [DecidableEq Tok]

/-- The ledger's step on one of its rows. -/
@[expose] def ledgerStep (L : Ledger ι W Tok) (d : L.Rec) : LRow ι W Tok L.Rec → Except (LClause ι Tok) L.Rec
  | .commit i t =>
    if t ∈ L.spent d then
      match grantOf L d t with
      | some g => .error (.taken t g.winner g.epoch)
      | none => .error (.consumed t)
    else .ok (L.commit d i t)
  | .raw w => if L.stepRaw (L.raw d) w then .ok (L.setRaw d w) else .error .worldStep
  | .abandon i => .ok (L.onAbandon d i)
  | .observe d' => if L.allowed d d' then .ok d' else .error .notAllowed

theorem ledgerStep_allowed (L : Ledger ι W Tok) {d d' : L.Rec} {r : LRow ι W Tok L.Rec}
    (h : ledgerStep L d r = .ok d') : L.allowed d d' = true := by
  cases r with
  | commit i t =>
    simp only [ledgerStep] at h; split at h
    · split at h <;> cases h
    · cases h; exact L.allowed_commit _ _ _
  | raw w =>
    simp only [ledgerStep] at h; split at h
    · cases h; exact L.allowed_setRaw _ _ (by assumption)
    · cases h
  | abandon i => simp only [ledgerStep] at h; cases h; exact L.allowed_onAbandon _ _
  | observe d'' =>
    simp only [ledgerStep] at h; split at h
    · cases h; assumption
    · cases h

/-- **The ledger as an audited fold**: its world component is its record, its rest is nothing, and
every row is a move. It reads no fact; it shares its fact type with the runners (`Fact ⊕ Tok`) so
that it can be a member of their family. -/
@[expose] def ledgerAdmission (L : Ledger ι W Tok) (base : W → View Tok Fact) :
    Obend.Fold.Admission L.Rec Unit (LRow ι W Tok L.Rec) (Fact ⊕ Tok) (LClause ι Tok) where
  step a r := (ledgerStep L a.1 r).map fun d => (d, ())
  reads _ _ := []
  look d := fun
    | .inl f => (base (L.raw d)).holds f
    | .inr t => sharedLive L base d t
  moves _ := true
  observe := .observe
  allowed := L.allowed
  keeps_world _ _ _ h := by cases h
  step_of_reads _ _ _ h := by cases h
  observe_ok w w' l ha := by cases l; simp [ledgerStep, ha]; rfl

end

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W : Type}

/-- A joint configuration: the ledger, and every runner's controlled configuration over it. -/
structure JCfg (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type)
    (P Cand Fact Ob : Type) (i₀ : Ix) where
  led : L.Rec
  cfgs : ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀

/-- A joint event. -/
inductive JEvent (ι W : Type) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Cred Cand Fact V : Type) where
  /-- the raw world moves -/
  | world (w : W)
  /-- runner `i` proposes to dispatch `o` -/
  | dispatch (i : ι) (o : Σ i, S.Op i)
  /-- runner `i` abandons `o` in flight -/
  | abandon (i : ι) (o : Σ i, S.Op i)
  /-- any other controlled event of runner `i` (a reply, an advance, a choice) -/
  | own (i : ι) (ev : CEvent S Hole A P Cred Cand Fact V)

/-- Why the joint transition refused. -/
inductive JRefusal (ι Tok : Type) (S : Sig Ix) (Hole : Ix → Type) (P Cand Fact : Type) where
  /-- the ledger refused its row -/
  | ledger (c : LClause ι Tok)
  /-- runner `i` refused, for its own reason -/
  | runner (i : ι) (r : CRefusal S Hole P Cand Tok Fact)
  /-- the token is held: committed to `winner` at `epoch` -/
  | taken (t : Tok) (winner : ι) (epoch : Nat)
  /-- a world move, a dispatch or an abandonment of a runner goes through the joint arm -/
  | notOwn (i : ι)

variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]

/-- Every runner observes the ledger's new record `d` as its world event: its log gains `.world d`
and its world is `d`. This is exactly the controlled runner's own acceptance of that event
(`Obend.Run.Proofs.Shared.crun_propagated`) at a runner coupled to an allowed move. -/
def propagated (L : Ledger ι W Tok) {i₀ : Ix} (d : L.Rec) (cs : ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀) :
    ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀ :=
  fun i => { cs i with cfg := { (cs i).cfg with world := d, log := (cs i).cfg.log ++ [.world d] } }

/-- Propagate the ledger's move from `prev` to `d` to every runner (a `#tooth` mutation target). The
move is judged once, by the ledger's `allowed`, which is every runner's host; a move it does not
allow is returned as the ledger's refusal, never swallowed. -/
def propagate (L : Ledger ι W Tok) {i₀ : Ix} (prev d : L.Rec) (cs : ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀) :
    Except (JRefusal ι Tok S Hole P Cand Fact) (ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀) :=
  if L.allowed prev d then .ok (propagated L d cs) else .error (.ledger .notAllowed)

/-- Replace runner `i`'s configuration. -/
def setCfg {i₀ : Ix} (cs : ι → CCfg S Hole A P Cand Tok Fact Ob W i₀) (i : ι)
    (c : CCfg S Hole A P Cand Tok Fact Ob W i₀) : ι → CCfg S Hole A P Cand Tok Fact Ob W i₀ :=
  fun j => if j = i then c else cs j

/-- The ledger's row for runner `i`'s dispatch of `o`: the commit of the token it consumes, or the
record observed as it is. -/
@[expose] def ledgerRowOf (L : Ledger ι W Tok) (sp : Spec S Tok Fact Ob) (d : L.Rec) (i : ι) (o : Σ i, S.Op i) :
    LRow ι W Tok L.Rec :=
  match sp.consumes o.2 with
  | some t => .commit i t
  | none => .observe d

/-- One joint transition. -/
@[expose] def jrun (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (J : JCfg L S Hole A P Cand Fact Ob i₀) :
    JEvent ι W S Hole A P Cred Cand Fact L.Rec → Except (JRefusal ι Tok S Hole P Cand Fact) (JCfg L S Hole A P Cand Fact Ob i₀)
  | .world w =>
    match ledgerStep L J.led (.raw w) with
    | .ok d => (propagate L J.led d J.cfgs).map (JCfg.mk d)
    | .error c => .error (.ledger c)
  | .dispatch i o =>
    match crun (localHost L base) (sp i) (au i) (k i) (J.cfgs i) (.base (.dispatch o)) with
    | .ok c₁ =>
      match ledgerStep L J.led (ledgerRowOf L (sp i) J.led i o) with
      | .ok d => (propagate L J.led d (setCfg J.cfgs i c₁)).map (JCfg.mk d)
      | .error c => .error (.ledger c)
    | .error (.run (.unadmitted o' m (some t))) =>
      match grantOf L J.led t with
      | some g => .error (.taken t g.winner g.epoch)
      | none => .error (.runner i (.run (.unadmitted o' m (some t))))
    | .error r => .error (.runner i r)
  | .abandon i o =>
    match crun (localHost L base) (sp i) (au i) (k i) (J.cfgs i) (.base (.abandon o)) with
    | .ok c₁ =>
      match ledgerStep L J.led (.abandon i) with
      | .ok d => (propagate L J.led d (setCfg J.cfgs i c₁)).map (JCfg.mk d)
      | .error c => .error (.ledger c)
    | .error r => .error (.runner i r)
  | .own i ev =>
    match ev with
    | .base (.world _) | .base (.dispatch _) | .base (.abandon _) => .error (.notOwn i)
    | ev =>
      match crun (localHost L base) (sp i) (au i) (k i) (J.cfgs i) ev with
      | .ok c₁ => .ok ⟨J.led, setCfg J.cfgs i c₁⟩
      | .error r => .error (.runner i r)

/-! ## The ledger's view, committed -/

section
variable {ι W Tok Fact : Type} [DecidableEq Tok]

/-- **The ledger's view, committed**: the facts and tokens of the schema `keys` at a record, each as
its bit at the shared view (`hostLook` at the local host: the raw world's fact, the token at the
shared mask). A committed value `1` reads as an opening `true`. -/
def viewReading (L : Ledger ι W Tok) (base : W → View Tok Fact) (keys : List (Fact ⊕ Tok)) :
    Obend.Receipt.Reading L.Rec (Fact ⊕ Tok) (Fact ⊕ Tok) where
  C := ⟨keys, fun d k => if Obend.Run.hostLook (localHost L base) d k then 1 else 0⟩
  key := id
  bit _ v := v == 1

/-- **`dated : View`**: the root of the ledger's committed view at a record. -/
def dated (H : Obend.Digest.HashBytes.Hash) (L : Ledger ι W Tok) (base : W → View Tok Fact)
    (keys : List (Fact ⊕ Tok)) (d : L.Rec) : Nat :=
  (viewReading L base keys).C.dated H d

end

/-! ## The members of the joint fold -/

/-- A member of the joint fold: the ledger, or a runner. -/
inductive Mem (ι : Type) where
  | ledger
  | run (i : ι)
  deriving DecidableEq, Repr

/-- A member's rows. -/
abbrev MRow (ι W Tok R : Type) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Fact : Type) : Mem ι → Type
  | .ledger => LRow ι W Tok R
  | .run _ => Event S Hole A Fact R

/-- A member's rest of the accumulator. -/
abbrev MRest (ι : Type) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok Fact : Type) : Mem ι → Type
  | .ledger => Unit
  | .run _ => Obend.Run.Rest S Hole A Tok Fact

/-- A member's refusals. -/
abbrev MClause (ι Tok : Type) : Mem ι → Type
  | .ledger => LClause ι Tok
  | .run _ => Obend.Run.Clause

/-- **The members**: the ledger's admission, and each runner's `Legal` as an audited fold at its
local host (`Obend.Run.Fold.legalAdmission`), all over the ledger's record. -/
def members (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob) {i₀ : Ix}
    (O : ι → Open S Hole A Tok Fact Ob i₀) :
    (m : Mem ι) → Obend.Fold.Admission L.Rec (MRest ι S Hole A Tok Fact m)
      (MRow ι W Tok L.Rec S Hole A Fact m) (Fact ⊕ Tok) (MClause ι Tok m)
  | .ledger => ledgerAdmission L base
  | .run i => Obend.Run.legalAdmission (localHost L base) (sp i) (O i).template

/-- Each member's rest at a joint configuration: nothing for the ledger; for a runner, the rest of
the accumulator its log folds to (`Obend.Run.accOf`, from the start `d₀`). -/
def mrestOf {L : Ledger ι W Tok} (sp : ι → Spec S Tok Fact Ob) {i₀ : Ix} (O : ι → Open S Hole A Tok Fact Ob i₀) (d₀ : L.Rec)
    (J : JCfg L S Hole A P Cand Fact Ob i₀) : (m : Mem ι) → MRest ι S Hole A Tok Fact m
  | .ledger => ()
  | .run i => (Obend.Run.accOf (sp i) (O i).σ d₀ (fun _ _ => []) (J.cfgs i).cfg.log).rest

/-- The joint configurations reachable from `J₀`. -/
inductive JReachable (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) : JCfg L S Hole A P Cand Fact Ob i₀ → Prop
  | init : JReachable L base sp au k J₀ J₀
  | step {J J' : JCfg L S Hole A P Cand Fact Ob i₀} (ev : JEvent ι W S Hole A P Cred Cand Fact L.Rec) :
      JReachable L base sp au k J₀ J → jrun L base sp au k J ev = .ok J' → JReachable L base sp au k J₀ J'

/-- A joint session. -/
def jsession (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix} :
    JCfg L S Hole A P Cand Fact Ob i₀ → List (JEvent ι W S Hole A P Cred Cand Fact L.Rec) →
      JCfg L S Hole A P Cand Fact Ob i₀ × List (Option (JRefusal ι Tok S Hole P Cand Fact))
  | J, [] => (J, [])
  | J, ev :: evs =>
    match jrun L base sp au k J ev with
    | .ok J' => let r := jsession L base sp au k J' evs; (r.1, none :: r.2)
    | .error w => let r := jsession L base sp au k J evs; (r.1, some w :: r.2)

/-- The start: an initial ledger, each runner at its object's start at that ledger. -/
@[expose] def JCfg.init (L : Ledger ι W Tok) {i₀ : Ix} (d₀ : L.Rec) (O : ι → Open S Hole A Tok Fact Ob i₀)
    (stored₀ : ι → (j : Ix) → Hole j → Option Cand) : JCfg L S Hole A P Cand Fact Ob i₀ :=
  ⟨d₀, fun i => CCfg.init (Cfg.init (O i) d₀) (stored₀ i)⟩

end

end Obend.Run.Shared

end
