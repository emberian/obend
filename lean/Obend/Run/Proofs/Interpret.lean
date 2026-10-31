module
/-
# Obend.Run.Proofs.Interpret — the reference handler as an instance of the runner

`drive` runs the runner with a handler: dispatch the residual's next call, show it to the handler
only once the runner accepted it, give the handler's reply back as the response event.

- `drive_sound`: whatever a driven run delivers (a result, or a stop at a hole), `interpret` delivers
  from the same residual and handler state. The runner only ever refuses more.
- `drive_complete`: on a protocol judged by `HasProt` (hypotheses `Γ`, tokens `Δ`, each token once),
  at a world where every hypothesis holds and every token of `Δ` is live and unspent, some fuel
  makes the driven run deliver exactly what `interpret` does. The reference handler is the instance:
  the runner adds nothing to a run whose every call is admitted.

The other direction, a run `interpret` delivers and the runner refuses, is the fixture
`Obend.Run.Negotiation.withdrawn_refused`.
-/
public import Obend.Run.Proofs.Invariant
public import Obend.AxiomPin
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Proofs.Invariant
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping

namespace Obend.Run

open Obend.Slot Obend.Slot.Protocol

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob V St : Type}
variable [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]

theorem run_dispatch_res {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i}
    (h : run host sp c (.dispatch o) = .ok c') : c'.res = c.res := by
  have hcl := run_live (fun _ e => by cases e) h
  simp only [run, hcl] at h
  have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
  rw [haw] at h
  cases hinf : c.obj.hist.inflight with
  | some o' => simp [hinf] at h
  | none =>
    simp only [hinf] at h
    rcases hres : c.res with ⟨j, _ | ⟨op, k⟩ | _⟩
    · simp [hres] at h
    · simp only [hres] at h
      by_cases ho : o = ⟨j, op⟩
      · by_cases hg : dispatchGuard sp (c.admitView host) op = true
        · simp only [ho, hg, ↓reduceIte] at h; cases h; rfl
        · simp [ho, hg] at h
      · simp [ho] at h
    · simp [hres] at h

theorem run_respond_res {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {e : Entry S}
    (h : run host sp c (.respond e) = .ok c') : follow c.res e = some c'.res := by
  have hcl := run_live (fun _ e => by cases e) h
  simp only [run, hcl] at h
  cases hinf : c.obj.hist.inflight with
  | none => simp [hinf] at h
  | some o =>
    simp only [hinf] at h
    by_cases ho : (⟨e.1, e.2.1⟩ : Σ i, S.Op i) = o
    · simp only [ho, ↓reduceIte] at h
      cases hf : follow c.res e with
      | none => simp [hf] at h
      | some R => simp only [hf] at h; cases h; rfl
    · simp [ho] at h

theorem drive_call {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {H : Handler S (fun _ => St)}
    {i : Ix} {c c' c'' : Cfg S Hole A Tok Fact Ob V i} {s s' : St} {n : Nat} {j : Ix}
    {op : S.Op j} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)} {r : S.Resp op}
    (hres : c.res = ⟨j, .call op k⟩) (h1 : run host sp c (.dispatch ⟨j, op⟩) = .ok c')
    (hH : H.handle op s = ⟨r, s'⟩) (h2 : run host sp c' (.respond ⟨j, op, r⟩) = .ok c'') :
    drive host sp H (n + 1) c s = drive host sp H n c'' s' := by
  simp only [drive, hres, h1, hH, h2]

/-- **The runner refines `interpret`**: whatever a driven run delivers, `interpret` delivers from the
same residual and state. -/
public theorem drive_sound {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    (H : Handler S (fun _ => St)) {i : Ix} :
    ∀ (n : Nat) (c : Cfg S Hole A Tok Fact Ob V i) (s : St) (r : Result Hole A (fun _ => St)),
      (drive host sp H n c s).result? = some r → interpret H c.res.2 s = r := by
  intro n
  induction n with
  | zero => intro c s r h; simp [drive, Drive.result?] at h
  | succ n ih =>
    intro c s r h
    rcases hres : c.res with ⟨j, a | ⟨op, k⟩ | hl⟩
    · simp only [drive, hres, Drive.result?, Option.some.injEq] at h
      subst h; rfl
    · simp only [drive, hres] at h
      cases h1 : run host sp c (.dispatch ⟨j, op⟩) with
      | error w => simp [h1, Drive.result?] at h
      | ok c' =>
        simp only [h1] at h
        cases hH : H.handle op s with
        | mk r' s' =>
          simp only [hH] at h
          cases h2 : run host sp c' (.respond ⟨j, op, r'⟩) with
          | error w => simp [h2, Drive.result?] at h
          | ok c'' =>
            simp only [h2] at h
            have e1 := run_dispatch_res h1
            have e2 := run_respond_res h2
            rw [e1, hres, follow_call] at e2
            have := ih c'' s' r h
            rw [← Option.some.inj e2] at this
            show (match H.handle op s with | ⟨r, s'⟩ => interpret H (k r) s') = r
            rw [hH]
            exact this
    · simp only [drive, hres, Drive.result?, Option.some.injEq] at h
      subst h; rfl

/-- **The reference handler is an instance**: on a protocol judged at hypotheses `Γ` and tokens `Δ`
(each once), at a world where every hypothesis holds and every token of `Δ` is live and unspent,
a driven run with enough fuel delivers exactly what `interpret` delivers. -/
public theorem drive_complete {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob}
    (H : Handler S (fun _ => St)) {i : Ix} {Ω : Ctx S Hole A Tok Fact Ob} {Γ : List Fact}
    {Q : (j : Ix) → A j → Prop} {Φ : List Ob} :
    ∀ {j : Ix} (P : Prot S Hole A j) (c : Cfg S Hole A Tok Fact Ob V i) (s : St) (Δ : List Tok),
      c.res = ⟨j, P⟩ → c.ended = none → c.obj.hist.inflight = none → HasProt sp Ω Γ Q Φ Δ P →
      (∀ f ∈ Γ, (host.view c.world).holds f = true) →
      (∀ t ∈ Δ, (host.view c.world).live t = true ∧ t ∉ c.spent) → Δ.Nodup →
      ∃ n, (drive host sp H n c s).result? = some (interpret H P s) := by
  intro j P
  induction P with
  | ret a =>
    intro c s Δ hres _ _ _ _ _ _
    exact ⟨1, by simp [drive, hres, Drive.result?]; rfl⟩
  | hole hl =>
    intro c s Δ hres _ _ _ _ _ _
    exact ⟨1, by simp [drive, hres, Drive.result?]; rfl⟩
  | @call j op k ih =>
    intro c s Δ hres hlive hinf hP hΓ hΔ hnd
    have hcl : closedBy c = none := hlive
    -- the dispatch is admitted, and the runner's next configurations
    have hreq : (sp.requires op).all (View.mask (host.view c.world) c.spent).holds = true := by
      have hsub : ∀ f ∈ sp.requires op, f ∈ Γ := by
        cases hP with
        | call _ _ _ hr _ _ => exact hr
        | spend _ _ _ _ _ hr _ _ => exact hr
      exact List.all_eq_true.mpr fun f hf => hΓ f (hsub f hf)
    let c' : Cfg S Hole A Tok Fact Ob V i := { c with
      obj := { c.obj with hist := ⟨c.obj.hist.answered, some ⟨j, op⟩⟩ }
      spent := spendOn sp c.spent op
      res := ⟨j, .call op k⟩
      log := c.log ++ [.dispatch ⟨j, op⟩] }
    have hg : dispatchGuard sp (c.admitView host) op = true → run host sp c (.dispatch ⟨j, op⟩) = .ok c' := by
      intro hg
      have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
      simp only [run, hcl, haw, hinf, hres, ↓reduceIte, hg]
      rfl
    cases hH : H.handle op s with
    | mk r s' =>
      let c'' : Cfg S Hole A Tok Fact Ob V i := { c' with
        obj := { c'.obj with hist := ⟨c'.obj.hist.answered ++ [⟨j, op, r⟩], none⟩ }
        res := ⟨_, k r⟩
        log := c'.log ++ [.respond ⟨j, op, r⟩] }
      have h2 : run host sp c' (.respond ⟨j, op, r⟩) = .ok c'' := by
        have hf : follow c'.res ⟨j, op, r⟩ = some ⟨_, k r⟩ := follow_call op k r
        have hinf' : c'.obj.hist.inflight = some ⟨j, op⟩ := rfl
        have hcl' : closedBy c' = none := hlive
        simp only [run, hcl', hf, hinf', ↓reduceIte]
        rfl
      have hfin : ∀ Δ', HasProt sp Ω Γ Q Φ Δ' (k r) → (∀ t ∈ Δ', (host.view c''.world).live t = true ∧ t ∉ c''.spent) →
          Δ'.Nodup → dispatchGuard sp (c.admitView host) op = true →
          ∃ n, (drive host sp H n c s).result? = some (interpret H (.call op k) s) := by
        intro Δ' hk hΔ' hnd' hgd
        obtain ⟨n, hn⟩ := ih r c'' s' Δ' rfl hlive rfl hk hΓ hΔ' hnd'
        refine ⟨n + 1, ?_⟩
        rw [drive_call hres (hg hgd) hH h2]
        show _ = some (match H.handle op s with | ⟨r, s'⟩ => interpret H (k r) s')
        rw [hH]
        exact hn
      cases hP with
      | call _ _ hc _ _ hk =>
        refine hfin Δ (hk r) (fun t ht => ?_) hnd ?_
        · refine ⟨(hΔ t ht).1, ?_⟩
          show t ∉ c.spent ++ (sp.consumes op).toList
          simp [hc, (hΔ t ht).2]
        · simp only [dispatchGuard, admitOp, Cfg.admitView, hc, Bool.and_true]
          exact hreq
      | spend _ _ t hc ht _ _ hk =>
        refine hfin (Δ.erase t) (hk r) (fun t' ht' => ?_) (hnd.erase t) ?_
        · have hm := (List.Nodup.mem_erase_iff hnd).mp ht'
          refine ⟨(hΔ t' hm.2).1, ?_⟩
          show t' ∉ c.spent ++ (sp.consumes op).toList
          simp [hc, (hΔ t' hm.2).2, hm.1]
        · simp only [dispatchGuard, admitOp, Cfg.admitView, hc, View.mask, Bool.and_eq_true]
          refine ⟨hreq, (hΔ t ht).1, ?_⟩
          simpa using (hΔ t ht).2

-- Completeness rests on the dispatch guard admitting what the judgment and the world support.
#tooth drive_complete by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => false

omit [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] in
/-- **Replanning by a slot**: a resolved replan event installs the body of the first candidate of
the order usable at the current world. -/
public theorem resolveEvent_ok {Cand : Type} {host : Host V Tok Fact} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} {Sl : Slot Fact Cand} {j : Ix} {h : Hole j}
    {body : Cand → Prot S Hole A j} {order : List Cand} {ev : Event S Hole A V}
    (he : resolveEvent host c Sl h body order = .ok ev) :
    ∃ cand rest, Sl.alternatives (host.view c.world).holds order = cand :: rest ∧ cand ∈ order ∧
      Sl.usable (host.view c.world).holds cand = true ∧ ev = .replan h (body cand) := by
  unfold resolveEvent at he
  cases hr : Sl.resolve (host.view c.world).holds body order with
  | error w => rw [hr] at he; cases he
  | ok f =>
    rw [hr] at he
    cases he
    obtain ⟨cand, rest, ha, hm, hu, hf⟩ := resolve_ok hr
    exact ⟨cand, rest, ha, hm, hu, by rw [hf]⟩

omit [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] in
/-- **Replanning by any stored-selection policy with TRANSITION** (`Integrity.transition`: keep a
usable stored selection, otherwise only a usable candidate, the first of the order unless it is
the stored one): the replan event installs a candidate usable at the current world, keeps the
stored one while it is usable, and is the policy's own choice. Nothing here fixes the policy. -/
public theorem resolveEventBy_ok {Cand : Type} [World V Fact] {adv : Advance V Fact Cand}
    (hA : Integrity.transition adv) {i : Ix} {c : Cfg S Hole A Tok Fact Ob V i}
    {Sl : Slot Fact Cand} {j : Ix} {h : Hole j} {body : Cand → Prot S Hole A j}
    {order : List Cand} {stored : Option Cand} :
    (∀ ev, resolveEventBy adv c Sl h body order stored = .ok ev →
      ∃ cand, ev = .replan h (body cand) ∧ Sl.usable (World.holdsAt c.world) cand = true ∧
        (stored = some cand ∨ ∃ rest, Sl.alternatives (World.holdsAt c.world) order = cand :: rest)) ∧
    (∀ cand, stored = some cand → Sl.usable (World.holdsAt c.world) cand = true →
      resolveEventBy adv c Sl h body order stored = .ok (.replan h (body cand))) := by
  obtain ⟨keep, ok, _⟩ := hA Sl c.world order stored
  refine ⟨fun ev he => ?_, fun cand hs hu => ?_⟩
  · unfold resolveEventBy at he
    cases ha : adv.advance Sl c.world order stored with
    | error w => rw [ha] at he; cases he
    | ok cand =>
      rw [ha] at he
      cases he
      exact ⟨cand, rfl, (ok cand ha).1, (ok cand ha).2⟩
  · unfold resolveEventBy
    rw [keep cand hs hu]
    rfl

#assert_axioms drive_sound drive_complete resolveEvent_ok resolveEventBy_ok

end

end Obend.Run
