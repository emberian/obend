module
/-
# Obend.Vault.Transport — a form out in the world, carried across changes of its context

A form (`Obend.Vault.Form`) leaves the vault that issued it and lives on, offline, in another store,
while the vault goes on changing. This module is the relation that says what becomes of it: a
SUPPORTED RESIDUAL COMPUTATION with a transport relation (Γ, C, H, O) ⇒[δ,τ] (Γ', C', H', O'), in
the terms of the research note ember received on 2026-11-05
(`collected-writings/prompts/RESEARCH-GPT-transport.md`). The form is the residual C; the vault's log
(`Obend.Vault.Replay`) is the published history H; the store at the tip is the context Γ'; the
proposals a store sent and has no receipt for are its obligations O; a change of a page, a law or a
grant is a δ; and τ is what this module computes and proves.

**Consumer-relative equality (§1, §8).** A page a form captured is three things: its VALUE (the
fields the form reads, `reads`), its SUPPORT (the rest of its state: its version, its size), and the
AUTHORITY under which the holder may write it (the vault's standing grants, §6), with the LAWS a
write of it is judged by beside them (`lawPrint`). What moved is a list of `Moved`; whether it matters
depends on who reads (`Moved.matters`): a DISPLAY sees values only (`display_fresh_iff`); an EFFECT,
which lands a fill, also needs the laws it was transported under and the authority to write, and is
the finer equality (`effect_fresh_display_fresh`). Support that merely changed hands (the same values
asserted by a later version) is a change for neither, and nothing is redone: the form as it went out
admits exactly what its fresh capture admits (`admitsAt_recapture`), its residual is the fresh
capture's (`residual_recapture`), and the vault's judge of the fresh capture is the form's own
admission at the vault's context (`judge_recapture_iff`). A captured page whose file is gone and whose
history is kept is not known to be gone: the form WAITS (`Moved.gone _ true`), it is not refused.

**Transport across a change of the laws (§4).** A form may declare a CONTINUITY CONTRACT when it is
issued: the values of its one natural hole it OFFERS, and those it PROMISES whatever becomes of the
laws while it is out. When the laws over its pages move, `transport` judges every offered value under
the new laws and the form CONTINUES (every value admitted), is REPAIRED (the offer narrows to what is
admitted, the residual kept, nothing recaptured), or is REFUSED by its contract (a promised value is
no longer admitted). `transport_sound`: a transported form's fills are exactly the fills the fresh
capture under the new context admits, intersected with the offer; every promised value is among them;
its residual is the fresh capture's. `transport_refused` names the promised value refused;
`transport_continues_iff`.

**Authority with many supports (§6).** The grants a vault issued and revoked are a two-phase set: a
grant stands until revoked, and a revocation is never undone. A form is supported by every standing
grant its holder holds; revoking one of two supports leaves it standing with no one seeing its
authority absent (`handoff_no_absence`, Garnock-Jones's transfer without a spurious absence, §5.6 of
the dissertation). Two replicas' grants join, and a revocation made on either side stands after
(`merge_revocation_wins`, `merge_live_comm`, `mem_live_revoke`).

**Obligations and the identity of an external effect (§7).** A fill is a proposal with the identity of
its INTENT (`mintIntent`: the form's digest, the holder, the fill, and the filler's count of fills),
outstanding in the filler's store until a receipt for it is confirmed (`effectsOf` checks the receipt
against what was sent). The vault that lands it keeps the landing by its intent: the same proposal
sent again is a duplicate by identity, not by content (`duplicateOf`; at the deployed machine,
`Obend.Vault.Replay.judge_refuses_duplicate`, `judge_by_identity`, `outstanding_kept`, `landed_kept`,
`obligations_survive_crash`).

**What is not here.** The contract covers a form with one natural hole, and its offer is a finite
list of values (each is judged by the kernel when it is offered and when the form is transported).
Retention, the right to forget a prefix of the log under a declared contract, is the next quest. A
form issued by one replica is transported by that replica; forms and their issues are not merged
between replicas (grants and landings are). A receipt binds a proposal's content, not the vault that
signed it: there are no signatures. Migration-time relinking stays out of scope, as in
`Obend.Vault.Replay`.
-/
public import Obend.Vault.Form
@[expose] public section

namespace Obend.Vault.Transport

set_option autoImplicit false

open Obend.Core.Data (Data)
open Obend.Vault.Form
open Obend.Vault.Rehydration (MembraneViewer)

/-! ## 1. What a form reads: its values -/

/-- The fields an expression reads. -/
def nfields : NExpr → List String
  | .lit _ | .hole _ => []
  | .field _ f => [f]
  | .add x y | .sub x y => nfields x ++ nfields y

/-- **The fields a form reads**: each move's field, and every field its amounts read. A page's VALUE,
for the form, is these fields of its state; the rest of the state (its version, its size, fields the
form does not read) is the page's SUPPORT. -/
def reads (f : Form) : List String := f.moves.flatMap fun m => m.asset :: nfields m.amount

/-- Two knowledges agree on the fields `F`: they know the same pages, and each page's fields `F`
alike. -/
def AgreeOn (F : List String) (k k' : Known) : Prop :=
  ∀ n, (k n).isSome = (k' n).isSome ∧ ∀ x ∈ F, (k n).map (natAt · x) = (k' n).map (natAt · x)

theorem nfields_subst (a : Assignment) : ∀ e : NExpr, nfields (e.subst a) = nfields e
  | .lit _ => rfl
  | .hole h => by simp only [NExpr.subst]; split <;> rfl
  | .field _ _ => rfl
  | .add x y => by simp [NExpr.subst, nfields, nfields_subst a x, nfields_subst a y]
  | .sub x y => by simp [NExpr.subst, nfields, nfields_subst a x, nfields_subst a y]

theorem eval_agree {F : List String} {k k' : Known} (hk : AgreeOn F k k') :
    ∀ e : NExpr, (∀ x ∈ nfields e, x ∈ F) → e.eval k = e.eval k'
  | .lit _, _ => rfl
  | .hole _, _ => rfl
  | .field (.page n) f, h => by
    simp only [NExpr.eval]
    exact (hk n).2 f (h f (by simp [nfields]))
  | .field (.hole _) _, _ => rfl
  | .add x y, h => by
    simp only [NExpr.eval]
    rw [eval_agree hk x (fun z hz => h z (by simp [nfields, hz])),
      eval_agree hk y (fun z hz => h z (by simp [nfields, hz]))]
  | .sub x y, h => by
    simp only [NExpr.eval]
    rw [eval_agree hk x (fun z hz => h z (by simp [nfields, hz])),
      eval_agree hk y (fun z hz => h z (by simp [nfields, hz]))]

theorem peval_agree {F : List String} {k k' : Known} (hk : AgreeOn F k k') :
    ∀ e : NExpr, (∀ x ∈ nfields e, x ∈ F) → e.peval k = e.peval k'
  | .lit _, _ => rfl
  | .hole _, _ => rfl
  | .field (.page n) f, h => by
    simp only [NExpr.peval]
    have ⟨hs, hv⟩ := hk n
    have hf := hv f (h f (by simp [nfields]))
    cases h1 : k n <;> cases h2 : k' n <;> simp_all
  | .field (.hole _) _, _ => rfl
  | .add x y, h => by
    simp only [NExpr.peval]
    rw [peval_agree hk x (fun z hz => h z (by simp [nfields, hz])),
      peval_agree hk y (fun z hz => h z (by simp [nfields, hz]))]
  | .sub x y, h => by
    simp only [NExpr.peval]
    rw [peval_agree hk x (fun z hz => h z (by simp [nfields, hz])),
      peval_agree hk y (fun z hz => h z (by simp [nfields, hz]))]

/-- What a leg is, its states before aside: the field, the pages, the amount, the values after. -/
def LegPair.view (p : LegPair) : String × String × String × Nat × Nat × Nat :=
  (p.asset, p.src, p.dst, p.amount, p.srcAfter, p.dstAfter)

/-- A residual move reads only the fields `F`. -/
def RFields (F : List String) (r : RMove) : Prop :=
  r.asset ∈ F ∧ (∀ x ∈ nfields r.amount, x ∈ F) ∧ (∀ x ∈ nfields r.debit, x ∈ F) ∧
    (∀ x ∈ nfields r.credit, x ∈ F)

/-- **A move's legs read only values**: at two knowledges that agree on the fields it reads, a
move evaluates alike (or is refused alike), the states before aside. -/
theorem pair_agree {F : List String} {k k' : Known} (hk : AgreeOn F k k') (r : RMove)
    (hr : RFields F r) : (r.pair k).map LegPair.view = (r.pair k').map LegPair.view := by
  obtain ⟨ha, hm, hd, hc⟩ := hr
  unfold RMove.pair
  rw [eval_agree hk _ hm, eval_agree hk _ hd, eval_agree hk _ hc]
  split
  · rfl
  · rfl
  · rename_i s d _ _
    obtain ⟨hs1, hs2⟩ := hk s
    obtain ⟨hd1, hd2⟩ := hk d
    have hsa := hs2 r.asset ha
    cases h1 : k s <;> cases h2 : k' s <;> simp only [h1, h2, Option.isSome] at hs1 <;>
      cases h3 : k d <;> cases h4 : k' d <;> simp only [h3, h4, Option.isSome] at hd1 <;>
      simp only [h1, h2, Option.map] at hsa <;> try rfl
    all_goals
      rename_i ps ps' pd pd'
      cases r.amount.eval k' <;> cases r.debit.eval k' <;> cases r.credit.eval k' <;>
        simp_all [Except.map, LegPair.view]

theorem pairsOf_agree {F : List String} {k k' : Known} (hk : AgreeOn F k k') :
    ∀ rs : List RMove, (∀ r ∈ rs, RFields F r) →
      (pairsOf k rs).map (·.map LegPair.view) = (pairsOf k' rs).map (·.map LegPair.view)
  | [], _ => rfl
  | r :: rs, h => by
    have hp := pair_agree hk r (h r (by simp))
    have ih := pairsOf_agree hk rs (fun x hx => h x (by simp [hx]))
    simp only [pairsOf]
    cases h1 : r.pair k <;> cases h2 : r.pair k' <;> rw [h1, h2] at hp <;>
      simp only [Except.map, Except.error.injEq, reduceCtorEq, Except.ok.injEq] at hp
    · simp [hp, bind, Except.bind, Except.map]
    · rename_i p p'
      cases h3 : pairsOf k rs <;> cases h4 : pairsOf k' rs <;> rw [h3, h4] at ih <;>
        simp only [Except.map, Except.error.injEq, reduceCtorEq, Except.ok.injEq] at ih <;>
        simp [bind, Except.bind, Except.map, pure, Except.pure, hp, ih]

/-! ## 2. The fresh capture of the same cells, and what it admits -/

/-- **The fresh capture** of a form's cells at the store `live`: the same pages, each at its state
there (one the store no longer has kept as captured). It is what `captureFrom` makes of the same
situation when no page entered or left it; the form's moves, holes and grants are its own. -/
def recapture (live : VaultStore) (f : Form) : Form :=
  { f with cells := f.cells.map fun c => { c with state := (live c.name).getD c.state } }

/-- **The form's values hold at `live`**: every page it captured is there, and reads alike at every
field the form reads. Its support (the rest of each state) may have moved. -/
def ValuesHold (live : VaultStore) (f : Form) : Prop :=
  ∀ c ∈ f.cells, ∃ d, live c.name = some d ∧ ∀ x ∈ reads f, natAt d x = natAt c.state x

theorem recapture_known (live : VaultStore) (f : Form) (n : String) :
    (recapture live f).known n = (f.cells.find? (·.name == n)).map fun c => (live c.name).getD c.state := by
  simp only [recapture, Form.known, List.find?_map, Option.map_map]
  rfl

theorem agree_known {live : VaultStore} {f : Form} (hv : ValuesHold live f) :
    AgreeOn (reads f) f.known (recapture live f).known := by
  intro n
  rw [recapture_known]
  simp only [Form.known]
  cases h : f.cells.find? (·.name == n) with
  | none => simp
  | some c =>
    obtain ⟨d, hd, hx⟩ := hv c (List.mem_of_find?_eq_some h)
    refine ⟨rfl, fun x hxF => ?_⟩
    simp [hd, hx x hxF]

theorem agree_knownLive {live : VaultStore} {f : Form} (hv : ValuesHold live f) :
    AgreeOn (reads f) (f.knownLive live) ((recapture live f).knownLive live) := by
  intro n
  have ⟨hs, hx⟩ := agree_known hv n
  simp only [Form.knownLive]
  cases h1 : f.known n <;> cases h2 : (recapture live f).known n <;> simp_all

theorem recapture_scope (live : VaultStore) (f : Form) : (recapture live f).scope = f.scope := by
  simp [recapture, Form.scope, List.map_map]

/-- Every move of a form, unfolded, reads only the form's fields. -/
theorem unfold_fields (f : Form) : ∀ m ∈ f.moves, RFields (reads f) m.unfold := by
  intro m hm
  have hin : ∀ x, x = m.asset ∨ x ∈ nfields m.amount → x ∈ reads f := by
    intro x hx
    simp only [reads, List.mem_flatMap, List.mem_cons]
    exact ⟨m, hm, hx⟩
  refine ⟨hin _ (.inl rfl), fun x hx => hin x (.inr hx), fun x hx => ?_, fun x hx => ?_⟩ <;>
    simp only [Move.unfold, nfields, List.mem_append, List.mem_singleton] at hx <;>
    rcases hx with hx | hx <;> first | exact hin x (.inl hx) | exact hin x (.inr hx)

/-- **The residual is kept**: where the form's values hold, the fresh capture's residual is the
form's. Nothing the form computed before it went out is redone, and a fill computed from the copy
that went out is the fill of the fresh capture. -/
theorem residual_recapture {live : VaultStore} {f : Form} (hv : ValuesHold live f) :
    (recapture live f).residual (recapture live f).known = f.residual f.known := by
  have hk := agree_known hv
  simp only [Form.residual, recapture]
  apply List.map_congr_left
  intro m hm
  obtain ⟨_, hmf, hd, hc⟩ := unfold_fields f m hm
  simp only [RMove.peval]
  have e1 := peval_agree hk _ hmf
  have e2 := peval_agree hk _ hd
  have e3 := peval_agree hk _ hc
  simp only [recapture] at e1 e2 e3
  rw [e1, e2, e3]

theorem fill_recapture {live : VaultStore} {f : Form} (hv : ValuesHold live f) (a : Assignment) :
    (recapture live f).fill a = f.fill a := by
  simp only [Form.fill, residual_recapture hv]

theorem checkMoves_congr {f g : Form} (h : f.scope = g.scope) (v : MembraneViewer) (holder : String) :
    ∀ rs : List RMove, checkMoves f v holder rs = checkMoves g v holder rs
  | [] => rfl
  | r :: rs => by
    have hp : ∀ p, checkPage f v holder p = checkPage g v holder p := by
      intro p; cases p <;> simp [checkPage, h]
    simp only [checkMoves, hp, checkMoves_congr h v holder rs]

/-- The membrane's gate reads a form's scope and its grants, nothing else. -/
theorem gate_congr {f g : Form} (hs : f.scope = g.scope) (hg : f.grants = g.grants)
    (root : MembraneViewer) (hops : List Grant) (rs : List RMove) :
    gate root f hops rs = gate root g hops rs := by
  simp only [gate, hs, hg, checkMoves_congr hs]

/-- The writes a turn makes: each leg's page, its field, and the field's value after. What the
kernel judges of a fill's turn is these (`legWritesOf` reads nothing else of a leg). -/
def writesOf (ds : List CellDelta) : List (String × Option String × Nat) :=
  ds.map fun d => (d.cell, d.touchedFields.head?, natAt d.postState (d.touchedFields.head?.getD ""))

theorem writesOf_pairDeltas (tid : ByteArray) : ∀ ps : List LegPair,
    writesOf (pairDeltas tid ps) =
      ps.flatMap fun p => [(p.src, some p.asset, p.srcAfter), (p.dst, some p.asset, p.dstAfter)]
  | [] => rfl
  | p :: ps => by
    have ih := writesOf_pairDeltas tid ps
    simp only [writesOf] at ih ⊢
    simp [pairDeltas, ih, LegPair.srcDelta, LegPair.dstDelta, natAt_putNat]

theorem cells_pairDeltas (tid : ByteArray) : ∀ ps : List LegPair,
    (pairDeltas tid ps).map CellDelta.cell = ps.flatMap fun p => [p.src, p.dst]
  | [] => rfl
  | p :: ps => by
    simp [pairDeltas, cells_pairDeltas tid ps, LegPair.srcDelta, LegPair.dstDelta]

theorem flatMap_view {β : Type} (g : String × String × String × Nat × Nat × Nat → List β) :
    ∀ {ps qs : List LegPair}, ps.map LegPair.view = qs.map LegPair.view →
      ps.flatMap (fun p => g (LegPair.view p)) = qs.flatMap (fun p => g (LegPair.view p))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, q :: qs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.flatMap_cons, h.1, flatMap_view g h.2]

/-- What an admission says to the kernel: who holds the final grant, and the writes of its turn. -/
def Admitted.said (ad : Admitted) : String × List (String × Option String × Nat) :=
  (ad.holder, writesOf ad.turn.writeCells)

/-- **Admission reads values**: two forms with one scope, one chain and one fill, at knowledges
whose fills evaluate alike (states before aside), are admitted alike, with the same holder and the
same writes, or refused alike. -/
theorem admit_agree {f g : Form} (hs : f.scope = g.scope) (hg : f.grants = g.grants)
    {a : Assignment} (hfill : f.fill a = g.fill a) (root : MembraneViewer) (hops : List Grant)
    {k k' : Known}
    (hp : (pairsOf k (f.fill a)).map (·.map LegPair.view) = (pairsOf k' (g.fill a)).map (·.map LegPair.view))
    (tid : ByteArray) (occ : Data) :
    (admit root f hops k a tid occ).map Admitted.said = (admit root g hops k' a tid occ).map Admitted.said := by
  unfold admit
  rw [gate_congr hs hg root hops (f.fill a), hfill]
  rw [hfill] at hp
  split
  · rfl
  · cases h1 : pairsOf k (g.fill a) <;> cases h2 : pairsOf k' (g.fill a) <;> rw [h1, h2] at hp <;>
      simp only [Except.map, Except.error.injEq, reduceCtorEq, Except.ok.injEq] at hp
    · simp [hp]
    · rename_i ps qs
      have hc : (pairDeltas tid ps).map CellDelta.cell = (pairDeltas tid qs).map CellDelta.cell := by
        rw [cells_pairDeltas, cells_pairDeltas]
        exact flatMap_view (fun v => [v.2.1, v.2.2.1]) hp
      have hw : writesOf (pairDeltas tid ps) = writesOf (pairDeltas tid qs) := by
        rw [writesOf_pairDeltas, writesOf_pairDeltas]
        exact flatMap_view (fun v => [(v.2.1, some v.1, v.2.2.2.2.1), (v.2.2.1, some v.1, v.2.2.2.2.2)]) hp
      simp only
      by_cases hn : ((pairDeltas tid ps).map CellDelta.cell).Nodup
      · have hn' : ((pairDeltas tid qs).map CellDelta.cell).Nodup := hc ▸ hn
        simp [hn, hn', Except.map, Admitted.said, pairsTurn, hw]
      · have hn' : ¬ ((pairDeltas tid qs).map CellDelta.cell).Nodup := hc ▸ hn
        simp [hn', Except.map, hc]

/-! ## 3. A context, and the fills it admits -/

/-- **A context** a form is judged in: the store's page states, and the laws, which judge the writes
of an admitted fill (by holder) and read nothing of a leg but its write (`local`). -/
structure Ctx where
  live : VaultStore
  laws : String → List CellDelta → Bool
  local_ : ∀ h ds ds', writesOf ds = writesOf ds' → laws h ds = laws h ds'

/-- **What a context admits of a fill**: the membrane's gate and the form's resources at the
context's states (`admit`), then the context's laws on the writes. -/
def admitsAt (Γ : Ctx) (g : Form) (hops : List Grant) (a : Assignment) : Bool :=
  match admit (ownerViewer g) g hops (g.knownLive Γ.live) a ByteArray.empty (.label g.name) with
  | .ok ad => Γ.laws ad.holder ad.turn.writeCells
  | .error _ => false

/-- **The form as it went out admits what its fresh capture admits**, wherever its values hold:
its support may have moved (a page rewritten with the same values, a version later), and nothing
of the capture needs redoing. -/
theorem admitsAt_recapture (Γ : Ctx) {f : Form} (hv : ValuesHold Γ.live f) (hops : List Grant)
    (a : Assignment) : admitsAt Γ (recapture Γ.live f) hops a = admitsAt Γ f hops a := by
  have hs := recapture_scope Γ.live f
  have hfill := fill_recapture hv a
  have hp : (pairsOf ((recapture Γ.live f).knownLive Γ.live) ((recapture Γ.live f).fill a)).map (·.map LegPair.view) =
      (pairsOf (f.knownLive Γ.live) (f.fill a)).map (·.map LegPair.view) := by
    have e1 := eval_fill_eq_subst_residual (Form.known_agrees f Γ.live) f a
    have e2 := eval_fill_eq_subst_residual (Form.known_agrees (recapture Γ.live f) Γ.live) (recapture Γ.live f) a
    simp only [Form.fill] at e1 e2 ⊢
    rw [e1, e2]
    have hm : (recapture Γ.live f).moves = f.moves := rfl
    rw [hm]
    refine (pairsOf_agree (agree_knownLive hv) _ ?_).symm
    intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨m, hm, rfl⟩ := hr
    obtain ⟨h1, h2, h3, h4⟩ := unfold_fields f m hm
    refine ⟨h1, ?_, ?_, ?_⟩ <;> intro x hx <;>
      simp only [RMove.subst, Move.unfold, nfields, nfields_subst] at hx <;>
      first
        | exact h2 x hx
        | exact h3 x (by simpa [Move.unfold, nfields] using hx)
        | exact h4 x (by simpa [Move.unfold, nfields] using hx)
  have hroot : ownerViewer (recapture Γ.live f) = ownerViewer f := by
    simp only [ownerViewer, hs]
  have hname : (recapture Γ.live f).name = f.name := rfl
  have ha := admit_agree hs rfl hfill (ownerViewer f) hops hp ByteArray.empty (.label f.name)
  unfold admitsAt
  rw [hroot, hname]
  cases h1 : admit (ownerViewer f) (recapture Γ.live f) hops ((recapture Γ.live f).knownLive Γ.live) a
      ByteArray.empty (.label f.name) <;>
    cases h2 : admit (ownerViewer f) f hops (f.knownLive Γ.live) a ByteArray.empty (.label f.name) <;>
    rw [h1, h2] at ha <;> simp only [Except.map, reduceCtorEq, Except.ok.injEq, Admitted.said, Prod.mk.injEq] at ha
  all_goals first
    | rfl
    | (simp only; rw [ha.1]; exact Γ.local_ _ _ _ ha.2)

/-! ## 4. The continuity contract, and transport across a change of the laws -/

/-- **A continuity contract**, declared when a form is issued: its one natural hole, the values it
OFFERS (the fills it admits), and the values it PROMISES (what the filler was told stays fillable
whatever becomes of the laws while the form is out). A well-formed contract promises only what it
offers. -/
structure Contract where
  hole : String
  offer : List Nat
  promise : List Nat
deriving DecidableEq, Repr

def Contract.fill (K : Contract) (x : Nat) : Assignment := { nats := [(K.hole, x)] }

/-- The fills of a form under a contract, in a context: the values it offers that the context
admits. -/
def Fills (Γ : Ctx) (g : Form) (K : Contract) (x : Nat) : Prop :=
  x ∈ K.offer ∧ admitsAt Γ g [] (K.fill x) = true

/-- What becomes of a form when the laws change while it is out. -/
inductive Verdict where
  /-- the new laws admit every value it offers -/
  | continues
  /-- they do not, and every promised value is still admitted: the offer narrows to what they
  admit, the form re-residualized without a recapture -/
  | repaired (before after : List Nat)
  /-- a promised value is no longer admitted: the contract refuses the change -/
  | refused (x : Nat)
deriving DecidableEq, Repr

/-- **Transport a form across a change of its context** to `Γ`: judge each offered value in `Γ`
(the form as it went out; `admitsAt_recapture` says that is the fresh capture's judgment), then
continue, narrow, or refuse by the contract. -/
def transport (Γ : Ctx) (K : Contract) (f : Form) : Verdict × Contract :=
  let adm := K.offer.filter fun x => admitsAt Γ f [] (K.fill x)
  if adm = K.offer then (.continues, K)
  else match K.promise.find? (fun x => !adm.contains x) with
    | some x => (.refused x, K)
    | none => (.repaired K.offer adm, { K with offer := adm })

/-- **`transport_sound`**: wherever the form's values hold at the new context, a transported form's
fills are exactly the fills the fresh capture under the new context admits, intersected with the
offer the contract made; every promised value is among them; and the residual the copy that went out
carries is the fresh capture's (nothing is recaptured or recomputed). -/
theorem transport_sound {Γ : Ctx} {K K' : Contract} {f : Form} {v : Verdict}
    (h : transport Γ K f = (v, K')) (hv : ValuesHold Γ.live f) (hK : ∀ x ∈ K.promise, x ∈ K.offer)
    (hok : ∀ x, v ≠ .refused x) :
    (∀ x, Fills Γ f K' x ↔ (admitsAt Γ (recapture Γ.live f) [] (K.fill x) = true ∧ x ∈ K.offer)) ∧
      (∀ x ∈ K.promise, Fills Γ f K' x) ∧
      (recapture Γ.live f).residual (recapture Γ.live f).known = f.residual f.known := by
  refine ⟨?_, ?_, residual_recapture hv⟩ <;> (try simp only [admitsAt_recapture Γ hv]) <;>
    unfold transport at h <;> simp only at h
  · intro x
    split at h
    · rename_i heq
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold Fills
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · split at h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm (hok _)
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        unfold Fills
        simp only [List.mem_filter]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, h1⟩
  · intro x hx
    split at h
    · rename_i heq
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hxo := hK x hx
      rw [← heq] at hxo
      exact ⟨heq ▸ hxo, (List.mem_filter.1 hxo).2⟩
    · split at h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm (hok _)
      · rename_i hfind
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hin : (K.offer.filter fun x => admitsAt Γ f [] (K.fill x)).contains x = true := by
          have := List.find?_eq_none.1 hfind x hx
          simpa using this
        have hm := List.contains_iff_mem.1 hin
        exact ⟨hm, (List.mem_filter.1 hm).2⟩

/-- **A refusal names what the contract promised**: the value is promised, and the fresh capture
under the new laws does not admit it; the form and its contract are left as they were. -/
theorem transport_refused {Γ : Ctx} {K K' : Contract} {f : Form} {x : Nat}
    (h : transport Γ K f = (.refused x, K')) (hv : ValuesHold Γ.live f)
    (hK : ∀ x ∈ K.promise, x ∈ K.offer) :
    x ∈ K.promise ∧ admitsAt Γ (recapture Γ.live f) [] (K.fill x) = false ∧ K' = K := by
  unfold transport at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · rename_i y hfind
      simp only [Prod.mk.injEq, Verdict.refused.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hy := List.mem_of_find?_eq_some hfind
      refine ⟨hy, ?_, rfl⟩
      have hnot := List.find?_some hfind
      rw [admitsAt_recapture Γ hv]
      cases hadm : admitsAt Γ f [] (K.fill y)
      · rfl
      · have hmem : y ∈ K.offer.filter (fun x => admitsAt Γ f [] (K.fill x)) :=
          List.mem_filter.2 ⟨hK y hy, hadm⟩
        simp [hmem] at hnot
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h

/-- **The form continues exactly when the new laws admit every value it offers.** -/
theorem transport_continues_iff (Γ : Ctx) (K : Contract) {f : Form} (hv : ValuesHold Γ.live f) :
    (transport Γ K f).1 = .continues ↔ ∀ x ∈ K.offer, admitsAt Γ (recapture Γ.live f) [] (K.fill x) = true := by
  simp only [admitsAt_recapture Γ hv]
  unfold transport
  simp only
  split
  · rename_i heq
    simp only [true_iff]
    intro x hx
    rw [← heq] at hx
    exact (List.mem_filter.1 hx).2
  · rename_i hne
    constructor
    · intro h; split at h <;> simp at h
    · intro hall
      exact absurd (List.filter_eq_self.2 fun x hx => hall x hx) hne

/-! ## 5. The kernel's laws are a context, and the vault's judge is `admitsAt` -/

/-- **The kernel judges the writes, and nothing else of a leg**: two turns with the same writes have
the same text written at every page. -/
theorem legWritesOf_local (H : Obend.Digest.HashBytes.Hash) (s : Store) (poster : String) :
    ∀ ds ds' : List CellDelta, writesOf ds = writesOf ds' → legWritesOf H s poster ds = legWritesOf H s poster ds'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [writesOf] at h
  | _ :: _, [], h => by simp [writesOf] at h
  | d :: ds, d' :: ds', h => by
    simp only [writesOf, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hc, hh, hv⟩, hr⟩ := h
    have ih := legWritesOf_local H s poster ds ds' (by simpa [writesOf] using hr)
    rw [legWritesOf.eq_2, legWritesOf.eq_2, hc, hh, ih]
    cases hp : s.page? d'.cell with
    | none => simp only
    | some p =>
      simp only
      cases hcur : p.current <;> cases hrd : p.render? <;> cases hf : d'.touchedFields.head? <;> simp only
      rw [hh, hf] at hv
      simp only [Option.getD_some] at hv
      rw [hv]

/-- What the kernel says of a turn's legs, landed for the form `f` by `holder`: each written as its
page's text (`legWritesOf`), the turn judged at once (`commitTurn`), and landed (`landedTurn`). -/
def kernelLaws (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) (holder : String) (ds : List CellDelta) :
    Bool :=
  match legWritesOf H s holder ds with
  | .error _ => false
  | .ok ws =>
    match commitTurn s.entries s.entries ws .owner s.turn holder s.environment with
    | .error _ => false
    | .ok prs =>
      match landedTurn f [] (.label f.name) prs with
      | .ok _ => true
      | .error _ => false

/-- **The vault's context**: its pages' states, and its kernel's laws. -/
def kernelCtx (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) : Ctx where
  live := stateStore s.entries
  laws := kernelLaws H s f
  local_ := fun h ds ds' hw => by simp only [kernelLaws, legWritesOf_local H s h ds ds' hw]

theorem landedTurn_ok_any (f : Form) (pins pins' : Footprint) (occ occ' : Data) (prs : List Prepared) :
    (match landedTurn f pins occ prs with | .ok _ => true | .error _ => false) =
      (match landedTurn f pins' occ' prs with | .ok _ => true | .error _ => false) := by
  unfold landedTurn
  by_cases hn : ((prs.map (landedDelta f.assets)).map CellDelta.cell).Nodup
  · simp only [hn, ↓reduceDIte]
    by_cases hb : f.assets.all (fun A => sumAssetDelta (prs.map (landedDelta f.assets)) A == 0) = true
    · simp only [hb, ↓reduceDIte]
    · simp only [hb, Bool.false_eq_true, ↓reduceDIte]
  · simp only [hn, ↓reduceDIte]

theorem admit_pins {root : MembraneViewer} {g : Form} {hops : List Grant} {k : Known} {a : Assignment}
    {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root g hops k a tid occ = .ok ad) :
    ad.turn.readPins = g.pinsOf ad.pairs := by
  unfold admit at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
      · cases h

theorem firstStale_live {live : VaultStore} :
    ∀ fp : Footprint, (∀ q ∈ fp, ∃ d, q.observed = some d ∧ live q.cell = some d) → Footprint.firstStale? live fp = none
  | [], _ => rfl
  | q :: fp, h => by
    obtain ⟨d, hq, hl⟩ := h q (by simp)
    simp only [Footprint.firstStale?, hq, hl, Obend.Law.termEq_refl_local, ite_true]
    exact firstStale_live fp fun q' hq' => h q' (by simp [hq'])

/-- **The fresh capture's pins hold** at the store it was taken from. -/
theorem recapture_pins_hold {live : VaultStore} {f : Form} (hv : ValuesHold live f) (ps : List LegPair) :
    admitFootprint live ((recapture live f).pinsOf ps) = .ok () := by
  unfold admitFootprint
  rw [firstStale_live]
  intro q hq
  simp only [Form.pinsOf, List.mem_filterMap] at hq
  obtain ⟨c, _, hc⟩ := hq
  rw [recapture_known] at hc
  cases hfind : f.cells.find? (·.name == c) with
  | none => simp [hfind] at hc
  | some cell =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hc
    subst hc
    have hname : cell.name = c := by simpa using List.find?_some hfind
    obtain ⟨d, hd, _⟩ := hv cell (List.mem_of_find?_eq_some hfind)
    exact ⟨d, by simp [hd], by rw [← hname]; exact hd⟩

/-- **The vault's judge is the model's admission**: wherever a form's values hold at a store, the
store's judge of the fresh capture (`judgeProposal`: gate, resources, pins, the kernel's laws, the
landing) succeeds exactly when the kernel's context admits the fill of the form as it went out. -/
theorem judge_recapture_iff (H : Obend.Digest.HashBytes.Hash) (s : Store) {f : Form}
    (hv : ValuesHold (stateStore s.entries) f) (hops : List Grant) (a : Assignment) :
    (match judgeProposal H s (recapture (stateStore s.entries) f) hops a with | .ok _ => true | .error _ => false) =
      admitsAt (kernelCtx H s f) f hops a := by
  rw [← admitsAt_recapture (kernelCtx H s f) hv]
  unfold judgeProposal admitsAt
  simp only [kernelCtx]
  cases had : admit (ownerViewer (recapture (stateStore s.entries) f)) (recapture (stateStore s.entries) f) hops
      ((recapture (stateStore s.entries) f).knownLive (stateStore s.entries)) a ByteArray.empty
      (.label (recapture (stateStore s.entries) f).name) with
  | error e => simp only
  | ok ad =>
    simp only
    rw [admit_pins had, recapture_pins_hold hv]
    simp only [kernelLaws]
    cases hw : legWritesOf H s ad.holder ad.turn.writeCells with
    | error e => simp only
    | ok ws =>
      simp only
      cases hc : commitTurn s.entries s.entries ws .owner s.turn ad.holder s.environment with
      | error e => simp only
      | ok prs =>
        simp only
        have e := landedTurn_ok_any (recapture (stateStore s.entries) f)
          ((recapture (stateStore s.entries) f).pinsOf ad.pairs) [] ad.turn.occasion (.label f.name) prs
        have e2 : landedTurn (recapture (stateStore s.entries) f) [] (.label f.name) prs =
            landedTurn f [] (.label f.name) prs := rfl
        rw [e2] at e
        cases hl : landedTurn (recapture (stateStore s.entries) f)
            ((recapture (stateStore s.entries) f).pinsOf ad.pairs) ad.turn.occasion prs <;>
          simp only [hl] at e ⊢ <;> exact e

/-! ## 6. Authority with many supports, and its merge -/

/-- A grant the vault issued and keeps standing until it is revoked, by its name. -/
structure Standing where
  id : String
  grant : Grant
deriving DecidableEq, Repr

/-- **The grants a vault issued**, and those it revoked: a grow-only set of each (a two-phase set).
Revocation is the one act that takes authority away, and it is never undone. -/
structure Grants where
  standing : List Standing := []
  revoked : List String := []
deriving DecidableEq, Repr

/-- The grants that stand: issued, and not revoked. -/
def Grants.live (G : Grants) : List Standing := G.standing.filter fun s => !G.revoked.contains s.id

def Grants.issue (G : Grants) (s : Standing) : Grants := { G with standing := G.standing ++ [s] }

def Grants.revoke (G : Grants) (r : String) : Grants := { G with revoked := G.revoked ++ [r] }

/-- **Two replicas' grants, joined**: every grant either issued, every revocation either made. -/
def Grants.merge (a b : Grants) : Grants :=
  ⟨a.standing ++ b.standing.filter (fun s => !a.standing.contains s),
    a.revoked ++ b.revoked.filter (fun r => !a.revoked.contains r)⟩

theorem mem_live (G : Grants) (s : Standing) : s ∈ G.live ↔ s ∈ G.standing ∧ s.id ∉ G.revoked := by
  simp [Grants.live]

theorem mem_live_merge (a b : Grants) (s : Standing) :
    s ∈ (a.merge b).live ↔ (s ∈ a.standing ∨ s ∈ b.standing) ∧ s.id ∉ a.revoked ∧ s.id ∉ b.revoked := by
  simp only [mem_live, Grants.merge, List.mem_append, List.mem_filter]
  by_cases hsa : s ∈ a.standing <;> by_cases hra : s.id ∈ a.revoked <;> by_cases hrb : s.id ∈ b.revoked <;>
    simp [hsa, hra, hrb]

/-- **Revocation wins the merge**: a grant revoked on either side stands on neither after. An old
branch that rejoins brings back no authority revoked since it left. -/
theorem merge_revocation_wins (a b : Grants) {r : String} (hr : r ∈ a.revoked ∨ r ∈ b.revoked) :
    ∀ s ∈ (a.merge b).live, s.id ≠ r := by
  intro s hs heq
  have ⟨_, ha, hb⟩ := (mem_live_merge a b s).1 hs
  subst heq
  rcases hr with h | h
  · exact ha h
  · exact hb h

/-- The merge is a join: the grants that stand do not depend on which side merges which. -/
theorem merge_live_comm (a b : Grants) (s : Standing) : s ∈ (a.merge b).live ↔ s ∈ (b.merge a).live := by
  rw [mem_live_merge, mem_live_merge]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h3, h2⟩

/-- Revocation takes away the one grant, and nothing else. -/
theorem mem_live_revoke (G : Grants) (r : String) (s : Standing) :
    s ∈ (G.revoke r).live ↔ s ∈ G.live ∧ s.id ≠ r := by
  simp only [mem_live, Grants.revoke, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun h => h2 (.inl h)⟩, fun h => h2 (.inr h)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, fun h => h.elim h2 h3⟩

/-- The grants that stand for one holder: the SUPPORTS of what it does. -/
def Grants.supports (G : Grants) (holder : String) : List Standing :=
  G.live.filter (·.grant.holder == holder)

/-- **The pages no standing grant lets the holder write.** Authority holds when there are none. -/
def uncovered (sups : List Standing) (scope pages : List String) : List String :=
  pages.filter fun n => !sups.any fun s => mayWrite (s.grant.viewer scope) n

/-- **No spurious absence** (Syndicate's transfer, Garnock-Jones §5.6): when every page has a support
other than the one revoked, the holder's authority holds before the revocation and after it; no one
looking in between sees it absent. -/
theorem handoff_no_absence (G : Grants) (r holder : String) (scope pages : List String)
    (h : ∀ n ∈ pages, ∃ s ∈ G.supports holder, s.id ≠ r ∧ mayWrite (s.grant.viewer scope) n = true) :
    uncovered (G.supports holder) scope pages = [] ∧ uncovered ((G.revoke r).supports holder) scope pages = [] := by
  constructor <;> simp only [uncovered, List.filter_eq_nil_iff, Bool.not_eq_true', List.any_eq_false] <;> intro n hn <;> obtain ⟨s, hs, hne, hw⟩ := h n hn <;> intro hall
  · exact absurd hw (by simpa using hall s hs)
  · have hs' : s ∈ (G.revoke r).supports holder := by
      simp only [Grants.supports, List.mem_filter] at hs ⊢
      exact ⟨(mem_live_revoke G r s).2 ⟨hs.1, hne⟩, hs.2⟩
    exact absurd hw (by simpa using hall s hs')

/-! ## 7. Obligations, and the identity of an external effect -/

/-- **An outstanding obligation** of the store that filled a form: the proposal it sent, by the
identity of its intent, not yet confirmed by the receipt of the store that judges it. -/
structure Obligation where
  intent : String
  form : String
  digest : String
  vault : String
  holder : String
  fill : Assignment
deriving DecidableEq, Repr

/-- **A landing** in the store that judged a proposal: its intent, the form, the holder, the pages it
wrote, the grants that stood behind it, and its receipt's place in the chain (from 1). -/
structure Landing where
  intent : String
  form : String
  holder : String
  pages : List String
  supports : List String
  receipt : Nat
deriving DecidableEq, Repr

/-- **The identity of an intent**: the form's digest, the holder, the fill, and the filler's count of
fills, digested. Two fills alike in content are two intents; a proposal sent again is one. -/
def mintIntent (H : Obend.Digest.HashBytes.Hash) (digest holder : String) (a : Assignment) (n : Nat) : String :=
  hex16 (digestNat H ("intent " ++ digest ++ " " ++ holder ++ " " ++ (assignmentJson a).compress ++ " " ++ toString n))

/-- The landing an intent already has here, if any. -/
def duplicateOf (landed : List Landing) (intent : String) : Option Landing := landed.find? (·.intent == intent)

theorem duplicateOf_iff (landed : List Landing) (intent : String) :
    (duplicateOf landed intent).isSome ↔ intent ∈ landed.map (·.intent) := by
  simp [duplicateOf, List.find?_isSome]

/-! ## 8. Consumer-relative equality -/

/-- What moved under a form since it was issued (or last transported). -/
inductive Moved where
  /-- a field the form reads -/
  | value (page field : String) (was now : Nat)
  /-- a captured page is not here; `tomb`: its file is gone and its history kept, so it may return -/
  | gone (page : String) (tomb : Bool)
  /-- the rest of a captured page's state: the same values, asserted by another version -/
  | support (page diff : String)
  /-- the laws a write of the page is judged by -/
  | law (page : String)
  /-- no standing grant lets the holder write the page -/
  | authority (page : String)
deriving DecidableEq, Repr

/-- Who reads a form: a DISPLAY shows it; an EFFECT lands its fill. -/
inductive Consumer where
  | display
  | effect
deriving DecidableEq, Repr

/-- Whether a move is a change for a consumer. A display reads values; an effect also needs the laws
it was transported under and the authority to write. A support that changed hands is a change for
neither. -/
def Moved.matters : Consumer → Moved → Bool
  | .display, .value .. | .display, .gone .. => true
  | .display, _ => false
  | .effect, .support .. => false
  | .effect, _ => true

/-- The form is as it was, for the consumer. -/
def freshFor (c : Consumer) (ms : List Moved) : Bool := !ms.any (Moved.matters c)

/-- **What is fresh for an effect is fresh for a display**: the effect's equality is the finer one. -/
theorem effect_fresh_display_fresh (ms : List Moved) (h : freshFor .effect ms = true) :
    freshFor .display ms = true := by
  simp only [freshFor, Bool.not_eq_true', List.any_eq_false] at h ⊢
  intro m hm
  have := h m hm
  cases m <;> simp_all [Moved.matters]

/-- **A display ignores support, laws and authority**: only a value or a page gone is a change to it. -/
theorem display_fresh_iff (ms : List Moved) :
    freshFor .display ms = true ↔ ∀ m ∈ ms, ∀ p f w n t, m ≠ .value p f w n ∧ m ≠ .gone p t := by
  simp only [freshFor, Bool.not_eq_true', List.any_eq_false]
  constructor
  · intro h m hm p f w n t
    have := h m hm
    constructor <;> rintro rfl <;> simp [Moved.matters] at this
  · intro h m hm
    cases m with
    | value p f w n => exact absurd rfl (h _ hm p f w n false).1
    | gone p t => exact absurd rfl (h _ hm p "" 0 0 t).2
    | _ => simp [Moved.matters]

/-! ## 9. The vault's side: the laws over a page, a form's basis, what moved -/

/-- **The laws a write of a page is judged by**, each by name and text: its own and its kinds'
(`lawsFor`), and the laws over links of every page that links to it. The page law is the form's
editable implementation; this is its fingerprint. -/
def lawPrint (s : Store) (n : String) : List String :=
  match s.page? n with
  | none => []
  | some p =>
    let es := s.entries
    let own := match p.current with
      | some G => ((lawsFor es n G).toOption.getD []).map fun l => l.1 ++ ": " ++ l.2.2
      | none => []
    own ++ es.flatMap fun e =>
      if e.name != n && (linkTargets e.graph).contains p.id then
        (((lawsFor es e.name e.graph).toOption.getD []).filter fun l => isLinkLaw l.2.2).map
          fun l => l.1 ++ ": " ++ l.2.2
      else []

/-- **A form's basis**: the laws over each page it captured. -/
def basisOf (s : Store) (f : Form) : List (String × List String) := f.cells.map fun c => (c.name, lawPrint s c.name)

/-- What the vault keeps of a form it issued: its continuity contract, and the basis it was issued
or last transported under. -/
structure Issue where
  form : String
  contract : Option Contract := none
  basis : List (String × List String) := []
deriving DecidableEq, Repr

/-- The captured pages whose laws are not the basis's. -/
def lawMoves (s : Store) (f : Form) (basis : List (String × List String)) : List Moved :=
  (basisOf s f).filterMap fun (n, now) => if basis.lookup n == some now then none else some (.law n)

/-- The form's values hold, decided. -/
def valuesHoldB (live : VaultStore) (f : Form) : Bool :=
  f.cells.all fun c => match live c.name with
    | some d => (reads f).all fun x => natAt d x == natAt c.state x
    | none => false

theorem valuesHoldB_sound {live : VaultStore} {f : Form} (h : valuesHoldB live f = true) : ValuesHold live f := by
  intro c hc
  have := List.all_eq_true.1 h c hc
  cases hl : live c.name with
  | none => simp [hl] at this
  | some d =>
    simp only [hl, List.all_eq_true, beq_iff_eq] at this
    exact ⟨d, rfl, this⟩

/-- What moved under the pages a form captured: a value it reads, a page gone, or only its support. -/
def cellMoves (s : Store) (f : Form) : List Moved :=
  let live := stateStore s.entries
  f.cells.flatMap fun c =>
    match live c.name with
    | none => [.gone c.name (s.tombs.any (·.name == c.name))]
    | some d =>
      let vs := (reads f).eraseDups.filterMap fun x =>
        if natAt d x == natAt c.state x then none else some (Moved.value c.name x (natAt c.state x) (natAt d x))
      if !vs.isEmpty then vs
      else if Obend.Law.termEq d.term c.state.term then []
      else [.support c.name (stateDiffText (some c.state) (some d))]

/-- No value moved and no page is gone: the form's values hold. -/
theorem valuesHold_of_cellMoves {s : Store} {f : Form}
    (h : (cellMoves s f).all (fun m => match m with | .value .. | .gone .. => false | _ => true) = true) :
    ValuesHold (stateStore s.entries) f := by
  intro c hc
  have hall := List.all_eq_true.1 h
  cases hl : stateStore s.entries c.name with
  | none =>
    have := hall (.gone c.name (s.tombs.any (·.name == c.name)))
      (List.mem_flatMap.2 ⟨c, hc, by simp [hl]⟩)
    simp at this
  | some d =>
    refine ⟨d, rfl, fun x hx => ?_⟩
    by_cases hne : natAt d x = natAt c.state x
    · exact hne
    exfalso
    have hmem : Moved.value c.name x (natAt c.state x) (natAt d x) ∈ cellMoves s f := by
      refine List.mem_flatMap.2 ⟨c, hc, ?_⟩
      simp only [hl]
      have hv : Moved.value c.name x (natAt c.state x) (natAt d x) ∈ (reads f).eraseDups.filterMap fun x =>
          if natAt d x == natAt c.state x then none else some (Moved.value c.name x (natAt c.state x) (natAt d x)) :=
        List.mem_filterMap.2 ⟨x, List.mem_eraseDups.2 hx, by simp [hne]⟩
      have hne' : ((reads f).eraseDups.filterMap fun x =>
          if natAt d x == natAt c.state x then none else some (Moved.value c.name x (natAt c.state x) (natAt d x))).isEmpty = false := by
        cases hh : ((reads f).eraseDups.filterMap fun x =>
          if natAt d x == natAt c.state x then none else some (Moved.value c.name x (natAt c.state x) (natAt d x))) with
        | nil => rw [hh] at hv; cases hv
        | cons _ _ => rfl
      simp only [hne', Bool.not_false, ite_true]
      exact hv
    have := hall _ hmem
    simp at this

/-- The holder a form was issued to: the holder of its first grant. -/
def holderOf (f : Form) : String := ((f.grants.head?).map (·.holder)).getD "owner"

/-- **The grants that stand behind a form**: the standing grants its holder holds, and the grant it
was captured under when the vault never issued it by name (a form from before the vault kept grants). -/
def supportsFor (G : Grants) (f : Form) : List Standing :=
  let own := G.supports (holderOf f)
  match f.grants.head? with
  | some g => if G.standing.any (·.id == f.name) || G.revoked.contains f.name then own else own ++ [⟨f.name, g⟩]
  | none => own

/-- The pages a form's moves name (its holes aside). -/
def formPages (f : Form) : List String :=
  ((f.moves.flatMap fun m => [m.src, m.dst]).filterMap fun | .page n => some n | .hole _ => none).eraseDups

/-- The pages a fill writes. -/
def fillPages (f : Form) (a : Assignment) : List String :=
  (((f.fill a).flatMap fun r => [r.src, r.dst]).filterMap fun | .page n => some n | .hole _ => none).eraseDups

/-- The pages no standing grant lets the form's holder write. -/
def authorityMoves (G : Grants) (f : Form) (pages : List String) : List Moved :=
  (uncovered (supportsFor G f) f.scope pages).map .authority

/-- A list of naturals, said as runs: `1..50`, `1..30, 40..50`. -/
def runsText (xs : List Nat) : String :=
  let rec go : List Nat → Option (Nat × Nat) → List String
    | [], none => []
    | [], some (a, b) => [if a == b then toString a else toString a ++ ".." ++ toString b]
    | x :: rest, none => go rest (some (x, x))
    | x :: rest, some (a, b) =>
      if x == b + 1 then go rest (some (a, x))
      else (if a == b then toString a else toString a ++ ".." ++ toString b) :: go rest (some (x, x))
  if xs.isEmpty then "nothing" else ", ".intercalate (go xs none)

/-- `LO..HI` or `N`, as the values. -/
def parseRange (t : String) : Option (List Nat) :=
  match t.splitOn ".." with
  | [a] => a.toNat?.map ([·])
  | [a, b] => do
    let lo ← a.toNat?
    let hi ← b.toNat?
    if lo ≤ hi then some ((List.range (hi + 1 - lo)).map (lo + ·)) else none
  | _ => none

def Moved.text : Moved → String
  | .value p x w n => p ++ " " ++ x ++ " " ++ toString w ++ " → " ++ toString n
  | .gone p true => p ++ " is not here now: its file is gone, its history kept"
  | .gone p false => p ++ " is not here"
  | .support p d => p ++ " (" ++ d ++ ")"
  | .law p => p
  | .authority p => p

/-- The effects a receipt names for a proposal: its form's digest, its fill, its holder
(`receiptFor`'s). The store that sent the proposal checks a receipt by it. -/
def effectsOf (H : Obend.Digest.HashBytes.Hash) (o : Obligation) : Nat :=
  digestNat H (Lean.Json.mkObj [("form", o.digest), ("fill", assignmentJson o.fill), ("by", o.holder)]).compress

/-! ## 10. On the wire -/

open Lean (Json toJson fromJson?)

def natsJson (xs : List Nat) : Json := Json.arr (xs.map toJson).toArray
def natsOf (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM fun e => e.getNat?
def strsJson (xs : List String) : Json := Json.arr (xs.map Json.str).toArray
def strsOf (j : Json) : Except String (List String) := do (← j.getArr?).toList.mapM fun e => e.getStr?

def contractJson (K : Contract) : Json :=
  Json.mkObj [("hole", K.hole), ("offer", natsJson K.offer), ("promise", natsJson K.promise)]

def contractOf (j : Json) : Except String Contract := do
  return ⟨← j.getObjValAs? String "hole", ← natsOf (← j.getObjVal? "offer"), ← natsOf (← j.getObjVal? "promise")⟩

def issueJson (i : Issue) : Json :=
  Json.mkObj [("form", i.form), ("contract", match i.contract with | some K => contractJson K | none => Json.null),
    ("basis", Json.arr (i.basis.map fun (n, ls) => Json.arr #[Json.str n, strsJson ls]).toArray)]

def issueOf (j : Json) : Except String Issue := do
  let form ← j.getObjValAs? String "form"
  let contract ← match ← j.getObjVal? "contract" with
    | .null => pure none
    | c => some <$> contractOf c
  let basis ← (← j.getObjValAs? (Array Json) "basis").toList.mapM fun e => do
    return (← (← e.getArrVal? 0).getStr?, ← strsOf (← e.getArrVal? 1))
  return ⟨form, contract, basis⟩

def standingJson (s : Standing) : Json := Json.mkObj [("id", s.id), ("grant", grantJson s.grant)]
def standingOf (j : Json) : Except String Standing := do
  return ⟨← j.getObjValAs? String "id", ← grantOf (← j.getObjVal? "grant")⟩

def grantsJson (G : Grants) : Json :=
  Json.mkObj [("standing", Json.arr (G.standing.map standingJson).toArray), ("revoked", strsJson G.revoked)]
def grantsOf (j : Json) : Except String Grants := do
  return ⟨← (← j.getObjValAs? (Array Json) "standing").toList.mapM standingOf, ← strsOf (← j.getObjVal? "revoked")⟩

def landingJson (l : Landing) : Json :=
  Json.mkObj [("intent", l.intent), ("form", l.form), ("by", l.holder), ("pages", strsJson l.pages),
    ("supports", strsJson l.supports), ("receipt", toJson l.receipt)]
def landingOf (j : Json) : Except String Landing := do
  return ⟨← j.getObjValAs? String "intent", ← j.getObjValAs? String "form", ← j.getObjValAs? String "by",
    ← strsOf (← j.getObjVal? "pages"), ← strsOf (← j.getObjVal? "supports"), ← j.getObjValAs? Nat "receipt"⟩

def obligationJson (o : Obligation) : Json :=
  Json.mkObj [("intent", o.intent), ("form", o.form), ("digest", o.digest), ("vault", o.vault), ("by", o.holder),
    ("fill", assignmentJson o.fill)]
def obligationOf (j : Json) : Except String Obligation := do
  return ⟨← j.getObjValAs? String "intent", ← j.getObjValAs? String "form", ← j.getObjValAs? String "digest",
    ← j.getObjValAs? String "vault", ← j.getObjValAs? String "by", ← assignmentOf (← j.getObjVal? "fill")⟩

end Obend.Vault.Transport

end
