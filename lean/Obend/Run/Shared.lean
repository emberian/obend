module
/-
# Obend.Run.Shared — several runners over one World, through an atomic commit boundary

`astra/ASTRA-EFFECT-LAWS-20261031.md` §3 (Design B) and §9, built as the composition layer. Any
number of controlled runners (`Obend.Run.Control`, indexed by `ι`) share one authoritative record,
the LEDGER, whose laws are fields (`Ledger`): a commit records a token's consumption and its grant
(winner and epoch) in one step; a move of the raw world and an abandonment leave the consumption and
the grants as they were (the raw world may call a spent token live again; it cannot unspend it). Each
runner's host is built from the ledger (`localHost`): it reads facts from the raw world and a token
as live only while the raw world says so AND the ledger has not consumed it (`sharedLive`, the shared
mask). The joint transition (`jrun`):

- a raw world move is applied to the ledger and propagated to every runner as a world event;
- a dispatch by runner `i` (1) brings `i`'s view to the ledger (a world event), (2) is judged by `i`'s
  own runner at that view (operation facts, decision citations, the token at the shared mask), (3) on
  acceptance records the consumption and the grant in the ledger and the dispatch in `i`'s log, in
  one joint step, and (4) only then is the call exposed; every runner sees the new ledger. A refusal
  for a token another runner holds names the winner and the epoch (`taken`);
- an abandonment is `i`'s own, applied to the ledger by `onAbandon` (durable: nothing is released);
- every other controlled event (`replyTo`, `advance`, `choose`) is `i`'s alone.

The theorems (`Obend.Run.Proofs.Shared`): each runner's log is `Legal` for its own object at its
local host (projection), the grants are exclusive and the consumption is once globally, and the
loser's refusal names the winner and the epoch.
-/
public import Obend.Run.Proofs.Control
@[expose] public section

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

/-- The ledger is DURABLE: an abandonment releases nothing (the call abandoned stays dispatched, its
consumption and its grant stand). A law the exclusion theorems take, kept apart from the structure so
that a ledger that releases on abandonment is a ledger, and the theorems say what it breaks. -/
structure Ledger.Durable {ι W Tok : Type} (L : Ledger ι W Tok) : Prop where
  spent : ∀ d i, L.spent (L.onAbandon d i) = L.spent d
  grants : ∀ d i, L.grants (L.onAbandon d i) = L.grants d

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
def grantOf (L : Ledger ι W Tok) (d : L.Rec) (t : Tok) : Option (Grant ι Tok) :=
  (L.grants d).find? fun g => decide (g.tok = t)

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
  | worldStep
  /-- runner `i` refused, for its own reason -/
  | runner (i : ι) (r : CRefusal S Hole P Cand Tok Fact)
  /-- the token is held: committed to `winner` at `epoch` -/
  | taken (t : Tok) (winner : ι) (epoch : Nat)
  /-- a world move, a dispatch or an abandonment of a runner goes through the joint arm -/
  | notOwn (i : ι)
  /-- a runner did not accept the ledger's move (never, at a joint-reachable configuration) -/
  | propagation (i : ι)

variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]

/-- Every runner sees the ledger's new record (a `#tooth` mutation target): its world event, at
its local host. -/
def propagate (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (d : L.Rec) (cs : ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀) : ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀ :=
  fun i => match crun (localHost L base) (sp i) (au i) (k i) (cs i) (.base (.world d)) with
    | .ok c => c
    | .error _ => cs i

/-- Replace runner `i`'s configuration. -/
def setCfg {i₀ : Ix} (cs : ι → CCfg S Hole A P Cand Tok Fact Ob W i₀) (i : ι)
    (c : CCfg S Hole A P Cand Tok Fact Ob W i₀) : ι → CCfg S Hole A P Cand Tok Fact Ob W i₀ :=
  fun j => if j = i then c else cs j

/-- The ledger after runner `i` dispatched `o`: its token, if any, consumed and granted to `i`. -/
def commitOf (L : Ledger ι W Tok) (sp : Spec S Tok Fact Ob) (d : L.Rec) (i : ι) (o : Σ i, S.Op i) : L.Rec :=
  match sp.consumes o.2 with
  | some t => L.commit d i t
  | none => d

/-- One joint transition. -/
def jrun (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (J : JCfg L S Hole A P Cand Fact Ob i₀) :
    JEvent ι W S Hole A P Cred Cand Fact L.Rec → Except (JRefusal ι Tok S Hole P Cand Fact) (JCfg L S Hole A P Cand Fact Ob i₀)
  | .world w =>
    if L.stepRaw (L.raw J.led) w then
      let d := L.setRaw J.led w
      .ok ⟨d, propagate L base sp au k d J.cfgs⟩
    else .error .worldStep
  | .dispatch i o =>
    match crun (localHost L base) (sp i) (au i) (k i) (J.cfgs i) (.base (.world J.led)) with
    | .error _ => .error (.propagation i)
    | .ok c₁ =>
      match crun (localHost L base) (sp i) (au i) (k i) c₁ (.base (.dispatch o)) with
      | .ok c₂ =>
        let d := commitOf L (sp i) J.led i o
        .ok ⟨d, propagate L base sp au k d (setCfg J.cfgs i c₂)⟩
      | .error (.run (.unadmitted o' m (some t))) =>
        match grantOf L J.led t with
        | some g => .error (.taken t g.winner g.epoch)
        | none => .error (.runner i (.run (.unadmitted o' m (some t))))
      | .error r => .error (.runner i r)
  | .abandon i o =>
    match crun (localHost L base) (sp i) (au i) (k i) (J.cfgs i) (.base (.abandon o)) with
    | .ok c₁ =>
      let d := L.onAbandon J.led i
      .ok ⟨d, propagate L base sp au k d (setCfg J.cfgs i c₁)⟩
    | .error r => .error (.runner i r)
  | .own i ev =>
    match ev with
    | .base (.world _) | .base (.dispatch _) | .base (.abandon _) => .error (.notOwn i)
    | ev =>
      match crun (localHost L base) (sp i) (au i) (k i) (J.cfgs i) ev with
      | .ok c₁ => .ok ⟨J.led, setCfg J.cfgs i c₁⟩
      | .error r => .error (.runner i r)

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
def JCfg.init (L : Ledger ι W Tok) {i₀ : Ix} (d₀ : L.Rec) (O : ι → Open S Hole A Tok Fact Ob i₀)
    (stored₀ : ι → (j : Ix) → Hole j → Option Cand) : JCfg L S Hole A P Cand Fact Ob i₀ :=
  ⟨d₀, fun i => CCfg.init (Cfg.init (O i) d₀) (stored₀ i)⟩

end

end Obend.Run.Shared

end
