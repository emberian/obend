module
/-
# Obend.Run.Reflect — mirrors are capabilities, admitted in the route every action is

Astra (2026-11-01, §3): a `Mirror` (`Obend.Core.Code`) was ordinary data, `{over, depth}`, and
`quoteVia` answered any code-depth mirror it was handed: attenuation of a supplied descriptor, not
authentication of the entitlement to it. Here the descriptor is only a REQUEST. A reflective
request is an operation of a signature (`sig`); what it requires is a fact of the world, the grant
of its principal over its target at its depth (`spec`); it is answered only when admitted by the
admission every runner dispatch passes (`Obend.Slot.Protocol.admitOp`, the runner's
`dispatchGuard`), at the current view, with a one-shot grant's token spent like any token. Grants
are downward closed in depth (`grantsHold`), so a derived descriptor (`Mirror.derive`) is admitted
whenever its parent is (`derived_admitted`), and nothing derived is deeper than its grant.

* `answer_admitted`: an answer means the request was admitted at the view, the view holds the grant
  to its principal over its target at code depth, and the answer is the target's quotation.
* `forged_descriptor_refused`: a code-depth descriptor built directly, with no grant at the view,
  is refused by name, naming the grant it lacks (Astra's probe, which `quoteVia` accepted).
* `metadata_grant_cannot_quote`: a principal granted metadata depth presenting a code descriptor is
  refused, whatever it presents.
* `runner_reflect_admitted`: in any runner whose protocol makes reflective calls, an accepted
  dispatch of one was admitted at the configuration's view (`run_dispatch_admitted`): the runner
  is the route, not a second door beside it.
-/
public import Obend.Core.Code
public import Obend.Run.Runner
public import Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Core.Code
import all Obend.Run.Proofs.Shared
public section
namespace Obend.Run.Reflect
open Obend.Slot Obend.Slot.Protocol
open Obend.Core.Code (Mirror Depth Held MirrorRefusal quoteVia quotation)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-- A reflective request: the principal asking, and the descriptor it presents. -/
structure Request where
  principal : String
  mirror : Mirror
  deriving DecidableEq, Repr

/-- The facts reflection reads: a grant to a principal over a target at a depth. -/
inductive Fact where
  | grant (principal over : String) (depth : Depth)
  deriving DecidableEq, Repr

/-- The reflective service's signature: one operation, the request; the reply is the quotation. -/
@[expose] def sig : Sig Unit := ⟨fun _ => Request, fun _ => Data, fun _ _ => ()⟩

/-- What a request requires: the grant to its principal over its target at its depth. A one-shot
grant names the token it spends (`once`). -/
@[expose] def spec {Tok : Type} (once : Request → Option Tok) : Spec sig Tok Fact Unit :=
  ⟨fun op => once op, fun op => [.grant op.principal op.mirror.over op.mirror.depth], fun _ => []⟩

/-- A world's grants as facts: a grant at a depth holds every shallower one. -/
@[expose] def grantsHold (grants : List (String × String × Depth)) : Fact → Bool
  | .grant p o d => grants.any fun g => g.1 == p && g.2.1 == o && decide (d ≤ g.2.2)

inductive Refusal (Tok : Type) where
  /-- not admitted at the view: the grants that do not hold, and the token that is not live -/
  | unadmitted (request : Request) (missing : List Fact) (dead : Option Tok)
  /-- admitted, and the descriptor is not one quotation answers (no such target, or shallow) -/
  | mirror (refusal : MirrorRefusal)

/-- **Reflection through admission**: the request is admitted by the runner's dispatch guard at the
view, then answered by the kernel's `quoteVia`. -/
@[expose] def answer {Tok : Type} (store : String → Option Held) (version : Nat) (sp : Spec sig Tok Fact Unit)
    (v : View Tok Fact) (req : Request) : Except (Refusal Tok) Data :=
  if dispatchGuard sp v (i := ()) req then
    match quoteVia store version req.mirror with
    | .ok d => .ok d
    | .error e => .error (.mirror e)
  else .error (.unadmitted req ((sp.requires (i := ()) req).filter fun f => !v.holds f)
    ((sp.consumes (i := ()) req).filter fun t => !v.live t))

/-- **An answer was admitted**: the view holds the grant to the request's principal over its target
at code depth (the depth `quoteVia` answers), and the answer is the target's quotation. -/
theorem answer_admitted {Tok : Type} {store : String → Option Held} {version : Nat} {once : Request → Option Tok}
    {v : View Tok Fact} {req : Request} {d : Data} (h : answer store version (spec once) v req = .ok d) :
    admitOp (spec once) v (i := ()) req = true ∧ v.holds (.grant req.principal req.mirror.over .code) = true ∧
      ∃ held, store req.mirror.over = some held ∧ d = quotation version held := by
  unfold answer at h
  split at h
  · rename_i admitted
    split at h
    · rename_i d' hq
      cases h
      obtain ⟨code, held, hs, rfl⟩ := Obend.Core.Code.quoteVia_ok hq
      have guard : admitOp (spec once) v (i := ()) req = true := by simpa [dispatchGuard] using admitted
      refine ⟨guard, ?_, held, hs, rfl⟩
      have := guard
      simp only [admitOp, spec, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at this
      rw [← code]; exact this.1
    · cases h
  · cases h

/-- **A forged descriptor is refused, naming the grant it lacks** (Astra's probe): a code-depth
mirror built directly, presented by a principal the view grants nothing, is not answered. -/
theorem forged_descriptor_refused {Tok : Type} (store : String → Option Held) (version : Nat)
    (once : Request → Option Tok) (live : Tok → Bool) (principal over : String) :
    answer store version (spec once) ⟨grantsHold [], live⟩ ⟨principal, ⟨over, .code⟩⟩ =
      .error (.unadmitted ⟨principal, ⟨over, .code⟩⟩ [.grant principal over .code]
        (((spec once).consumes (i := ()) ⟨principal, ⟨over, .code⟩⟩).filter fun t => !live t)) := by
  simp [answer, dispatchGuard, admitOp, spec, grantsHold, sig]

/-- **A metadata grant cannot quote**: whatever descriptor its holder presents, a principal granted
metadata depth over a target is answered no quotation of it. -/
theorem metadata_grant_cannot_quote {Tok : Type} (store : String → Option Held) (version : Nat)
    (once : Request → Option Tok) (live : Tok → Bool) (principal over : String) (m : Mirror) (d : Data)
    (target : m.over = over) :
    answer store version (spec once) ⟨grantsHold [(principal, over, .metadata)], live⟩ ⟨principal, m⟩ ≠ .ok d := by
  intro h
  obtain ⟨_, granted, _⟩ := answer_admitted h
  subst target
  have shallow : ¬ (Depth.code ≤ Depth.metadata) := by show ¬ (2 ≤ 1); decide
  simp [grantsHold, shallow] at granted

/-- **A derived descriptor is admitted where its parent is** (grants are downward closed), and it
asks no more than the parent's grant. -/
theorem derived_admitted {Tok : Type} {grants : List (String × String × Depth)} {live : Tok → Bool}
    {principal : String} {m : Mirror} (wanted : Depth)
    (parent : grantsHold grants (.grant principal m.over m.depth) = true) :
    grantsHold grants (.grant principal (m.derive wanted).over (m.derive wanted).depth) = true := by
  obtain ⟨same, deeper, _⟩ := Obend.Core.Code.mirror_attenuates m wanted
  simp only [grantsHold, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at parent ⊢
  obtain ⟨g, hg, ⟨hp, ho⟩, hd⟩ := parent
  refine ⟨g, hg, ⟨hp, by rw [same]; exact ho⟩, ?_⟩
  exact decide_eq_true (Obend.Core.Code.Depth.le_trans deeper (of_decide_eq_true hd))

/-- **The runner is the route**: in any runner over the reflective signature, an accepted dispatch
of a request was admitted at the configuration's view, so its principal held the grant over its
target at its depth there. -/
theorem runner_reflect_admitted {Hole : Unit → Type} {A : Unit → Type} {Tok V : Type} [DecidableEq Tok]
    [∀ i, DecidableEq (Hole i)] [DecidableEq (Σ i, sig.Op i)]
    {host : Host V Tok Fact} {once : Request → Option Tok}
    {c c' : Cfg sig Hole A Tok Fact Unit V ()} {o : Σ i, sig.Op i}
    (hr : run host (spec once) c (.dispatch o) = .ok c') :
    (c.admitView host).holds (.grant (o.2 : Request).principal (o.2 : Request).mirror.over
      (o.2 : Request).mirror.depth) = true := by
  have admitted := Obend.Run.Shared.run_dispatch_admitted hr
  simp only [admitOp, spec, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at admitted
  exact admitted.1

end Obend.Run.Reflect

end
