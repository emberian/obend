module
/-
# Obend.Run.Fork — a World fork for offline work, and the one door back: `stitch`

`review/VISION-CLAUDE-20261031.md` §2.1 item 5 and §7.4 (branch-and-stitch: a branch holds no
capability to main, its effects cannot leak, the only door is settlement; the I-confluent part
merges by union, conflicts are objects). Over the shared runners (`Obend.Run.Shared`):

- A FORK (`Fork`) is taken at the main ledger's epoch (its height). It holds no token of the shared
  ledger: it mints its own (`mint`, refused `notMine` for a shared token), spends only its own
  (`spend`, refused `notMine` for any other), and never holds a ledger record, so nothing it does
  reaches main (`fork_owns_no_shared`, `fork_spend_notMine`).
- Its rows are of two kinds. A MONOTONE row (`grow`) adds a fact to a grow-only set: I-confluent, it
  merges by union. A BOUNDED row (`defer`) is a main-side step that cannot run in the fork: in the
  joint instance, runner `i`'s dispatch of an operation. It ESCALATES: the fork records it, unjudged,
  and it is judged at the stitch.
- `stitch` is the one door. The monotone facts merge by union with main's (`stitch_union`; two forks
  stitched in either order give the same facts, `stitch_union_comm`). The escalated rows are REPLAYED
  in order through main's own step at stitch time (`replay`); in the joint instance (`jstitch`) that
  step is the joint transition `jrun` on `.dispatch i o`, so each row is judged by runner `i`'s
  controlled runner (`crun`: its protocol, its law and decision citations at main's current World,
  its selection control and authority) and then committed by the ledger's own row. A refused row is a
  CONFLICT, returned as a section (the row and the refusal), never dropped and never forced
  (`stitch_accounts`). The stitch is ATOMIC (`stitch_atomic`, through `settle`): if any escalated row
  is refused, main is unchanged and every refusal is returned; otherwise main moves to the replayed
  configuration, which is a joint run from main (`stitch_is_commit`).
- `stitch_exclusive`: stitching keeps the ledger's exclusion (no token granted twice).
  `stitch_double_spend`: a ticket the main ledger granted while the fork was offline, escalated by
  the fork, is a conflict naming the winner and the epoch of the grant.
-/
public import Obend.Run.Proofs.Shared
public section

namespace Obend.Run.Fork

open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared

section
variable {ι W Tok M E : Type} [DecidableEq Tok]

/-- A fork: the main epoch it was taken at, the tokens it minted, its own consumption, the monotone
facts it grew, and the bounded rows it escalated, unjudged. -/
structure Fork (Tok M E : Type) where
  epoch : Nat
  own : List Tok
  spentHere : List Tok
  grown : List M
  escalated : List E

/-- A row of a fork. -/
inductive FRow (ι Tok M E : Type) where
  /-- add a fact to the grow-only set (monotone: merges by union) -/
  | grow (m : M)
  /-- mint a token of the fork's own -/
  | mint (t : Tok)
  /-- spend one of the fork's own tokens -/
  | spend (i : ι) (t : Tok)
  /-- a main-side step the fork cannot run: bounded, it escalates to the stitch -/
  | defer (e : E)

/-- Why a fork refused a row. -/
inductive FRefusal (Tok : Type) where
  /-- the token is not the fork's: a fork holds no token of the shared ledger -/
  | notMine (t : Tok)
  /-- the fork's own token is spent already -/
  | spentHere (t : Tok)
  /-- a deferred row consumes one of the fork's own tokens: spend it -/
  | ownToken (t : Tok)
  deriving DecidableEq, Repr

/-- A fork taken at the main record `d`: nothing of its own yet. -/
def Fork.at (L : Ledger ι W Tok) (d : L.Rec) : Fork Tok M E := ⟨L.height d, [], [], [], []⟩

/-- One row of a fork. `shared t`: the token is the shared ledger's; `tokOf e`: the token a deferred
row would consume. -/
def forkStep (shared : Tok → Bool) (tokOf : E → Option Tok) (F : Fork Tok M E) :
    FRow ι Tok M E → Except (FRefusal Tok) (Fork Tok M E)
  | .grow m => .ok { F with grown := F.grown ++ [m] }
  | .mint t => if shared t then .error (.notMine t) else .ok { F with own := F.own ++ [t] }
  | .spend _ t =>
    if t ∈ F.own then
      if t ∈ F.spentHere then .error (.spentHere t) else .ok { F with spentHere := F.spentHere ++ [t] }
    else .error (.notMine t)
  | .defer e =>
    match tokOf e with
    | some t => if t ∈ F.own then .error (.ownToken t) else .ok { F with escalated := F.escalated ++ [e] }
    | none => .ok { F with escalated := F.escalated ++ [e] }

/-- The forks reachable from a fork. -/
inductive FReachable (shared : Tok → Bool) (tokOf : E → Option Tok) (F₀ : Fork Tok M E) : Fork Tok M E → Prop
  | init : FReachable shared tokOf F₀ F₀
  | step {F F' : Fork Tok M E} (r : FRow ι Tok M E) :
      FReachable shared tokOf F₀ F → forkStep shared tokOf F r = .ok F' → FReachable shared tokOf F₀ F'

/-- **A fork holds no token of the shared ledger**: every token a fork taken at a record owns is
one it minted, and none is shared. -/
theorem fork_owns_no_shared {shared : Tok → Bool} {tokOf : E → Option Tok} {L : Ledger ι W Tok} {d : L.Rec}
    {F : Fork Tok M E} (h : FReachable (ι := ι) shared tokOf (Fork.at L d) F) : ∀ t ∈ F.own, shared t = false := by
  induction h with
  | init => intro t ht; cases ht
  | step r _ hs ih =>
    intro t ht
    cases r with
    | grow m => simp only [forkStep] at hs; cases hs; exact ih t ht
    | mint t' =>
      simp only [forkStep] at hs; split at hs
      · cases hs
      · rename_i hsh; cases hs
        rcases List.mem_append.1 ht with ht | ht
        · exact ih t ht
        · simp at ht; subst ht; simpa using hsh
    | spend i t' =>
      simp only [forkStep] at hs; split at hs
      · split at hs
        · cases hs
        · cases hs; exact ih t ht
      · cases hs
    | defer e =>
      simp only [forkStep] at hs; split at hs
      · split at hs
        · cases hs
        · cases hs; exact ih t ht
      · cases hs; exact ih t ht

/-- **A fork's write to a shared token is refused `notMine`**: whatever the fork did, spending a
token of the shared ledger in the fork is refused. -/
theorem fork_spend_notMine {shared : Tok → Bool} {tokOf : E → Option Tok} {L : Ledger ι W Tok} {d : L.Rec}
    {F : Fork Tok M E} (h : FReachable (ι := ι) shared tokOf (Fork.at L d) F) (i : ι) {t : Tok}
    (ht : shared t = true) :
    forkStep shared tokOf F (.spend i t) = .error (.notMine t) := by
  have : t ∉ F.own := fun hm => by rw [fork_owns_no_shared h t hm] at ht; cases ht
  simp [forkStep, this]

end

/-! ## The stitch, over any main step -/

section
variable {St E R M : Type} [DecidableEq M]

/-- Replay the escalated rows in order through main's step: an accepted row moves the tentative
state, a refused one is a conflict section (the row and the refusal) and moves nothing. -/
def replay (step : St → E → Except R St) : St → List E → St × List (E × R)
  | s, [] => (s, [])
  | s, e :: rest =>
    match step s e with
    | .ok s' => replay step s' rest
    | .error r => let x := replay step s rest; (x.1, (e, r) :: x.2)

/-- The rows the replay accepted. -/
def accepted (step : St → E → Except R St) : St → List E → List E
  | _, [] => []
  | s, e :: rest =>
    match step s e with
    | .ok s' => e :: accepted step s' rest
    | .error _ => accepted step s rest

/-- The atomic settlement (a `#tooth` mutation target): the replayed state only if nothing was
refused, else main as it was. -/
def settle (main tentative : St) (conflicts : List (E × R)) : St :=
  if conflicts.isEmpty then tentative else main

/-- Union of grow-only sets: main's, then the fork's not already there. -/
def union (xs ys : List M) : List M := xs ++ ys.filter fun y => !decide (y ∈ xs)

/-- **The one door**: main's state and its monotone facts, stitched with a fork through main's step. -/
def stitch {Tok : Type} (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) :
    (St × List M) × List (E × R) :=
  let r := replay step main.1 F.escalated
  ((settle main.1 r.1 r.2, union main.2 F.grown), r.2)

theorem mem_union {xs ys : List M} {x : M} : x ∈ union xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  unfold union
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact .inl h
    · exact .inr (List.mem_filter.1 h).1
  · rintro (h | h)
    · exact List.mem_append.2 (.inl h)
    · by_cases hx : x ∈ xs
      · exact List.mem_append.2 (.inl hx)
      · exact List.mem_append.2 (.inr (List.mem_filter.2 ⟨h, by simp [hx]⟩))

variable {Tok : Type}

/-- **Monotone rows merge by union**, whatever the escalated rows did. -/
theorem stitch_union (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) (x : M) :
    x ∈ (stitch step main F).1.2 ↔ x ∈ main.2 ∨ x ∈ F.grown := mem_union

/-- **Two forks' monotone rows commute**: stitched in either order, the same facts. -/
theorem stitch_union_comm (step : St → E → Except R St) (main : St × List M) (F G : Fork Tok M E) (x : M) :
    x ∈ (stitch step (stitch step main F).1 G).1.2 ↔ x ∈ (stitch step (stitch step main G).1 F).1.2 := by
  simp only [stitch_union]
  constructor <;> rintro ((h | h) | h) <;> simp [h]

/-- What every accepted step keeps, the replay keeps. -/
theorem replay_keeps (step : St → E → Except R St) (P : St → Prop)
    (keep : ∀ s e s', P s → step s e = .ok s' → P s') : ∀ (es : List E) (s : St), P s → P (replay step s es).1
  | [], _, h => h
  | e :: rest, s, h => by
    simp only [replay]
    cases hs : step s e with
    | ok s' => exact replay_keeps step P keep rest s' (keep s e s' h hs)
    | error r => exact replay_keeps step P keep rest s h

/-- What every accepted step keeps, the stitch keeps (settled or not). -/
theorem stitch_keeps (step : St → E → Except R St) (P : St → Prop)
    (keep : ∀ s e s', P s → step s e = .ok s' → P s') (main : St × List M) (F : Fork Tok M E) (h : P main.1) :
    P (stitch step main F).1.1 := by
  simp only [stitch, settle]
  split
  · exact replay_keeps step P keep _ _ h
  · exact h

/-- Replaying a concatenation is replaying the second part from where the first ended. -/
theorem replay_append (step : St → E → Except R St) : ∀ (pre rest : List E) (s : St),
    replay step s (pre ++ rest) =
      ((replay step (replay step s pre).1 rest).1, (replay step s pre).2 ++ (replay step (replay step s pre).1 rest).2)
  | [], rest, s => rfl
  | e :: pre, rest, s => by
    simp only [List.cons_append, replay]
    cases hs : step s e with
    | ok s' => exact replay_append step pre rest s'
    | error r => simp only [replay_append step pre rest s, List.cons_append]

theorem accepted_all (step : St → E → Except R St) : ∀ (es : List E) (s : St),
    (replay step s es).2 = [] → accepted step s es = es
  | [], _, _ => rfl
  | e :: rest, s, h => by
    simp only [replay] at h
    simp only [accepted]
    cases hs : step s e with
    | ok s' => rw [hs] at h; simp only [accepted_all step rest s' h]
    | error r => rw [hs] at h; cases h

/-- **Conflicts are sections**: every escalated row is accepted or returned as a conflict with its
refusal; none is dropped. -/
theorem stitch_accounts (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) :
    ∀ e ∈ F.escalated, e ∈ accepted step main.1 F.escalated ∨ ∃ r, (e, r) ∈ (stitch step main F).2 := by
  show ∀ e ∈ F.escalated, _ ∨ ∃ r, (e, r) ∈ (replay step main.1 F.escalated).2
  generalize main.1 = s
  generalize F.escalated = es
  induction es generalizing s with
  | nil => intro e h; cases h
  | cons x rest ih =>
    intro e he
    simp only [accepted, replay]
    cases hs : step s x with
    | ok s' =>
      rcases List.mem_cons.1 he with rfl | he
      · exact .inl (List.mem_cons_self ..)
      · rcases ih s' e he with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
    | error r =>
      rcases List.mem_cons.1 he with rfl | he
      · exact .inr ⟨r, List.mem_cons_self ..⟩
      · rcases ih s e he with h | ⟨r', h⟩
        · exact .inl h
        · exact .inr ⟨r', List.mem_cons_of_mem _ h⟩

/-- **The stitch is atomic**: either nothing was refused, every escalated row was accepted, and main
moved to the replayed state; or something was refused, the refusals are the conflicts returned, and
main is exactly as it was. -/
theorem stitch_atomic (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) :
    ((stitch step main F).2 = [] ∧ accepted step main.1 F.escalated = F.escalated ∧
        (stitch step main F).1.1 = (replay step main.1 F.escalated).1) ∨
      ((stitch step main F).2 ≠ [] ∧ (stitch step main F).1.1 = main.1) := by
  simp only [stitch, settle]
  cases h : (replay step main.1 F.escalated).2 with
  | nil => exact .inl ⟨rfl, accepted_all step _ _ h, by simp⟩
  | cons c cs => exact .inr ⟨by simp, by simp⟩

end

/-! ## The joint stitch: escalated dispatches judged by the runners and committed by the ledger -/

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W M : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)] [DecidableEq M]

/-- An escalated row of the joint instance: runner `i` dispatches `o`. -/
abbrev Deferred (ι : Type) (S : Sig Ix) := ι × (Σ i, S.Op i)

/-- The token an escalated dispatch would consume. -/
def tokOf (sp : ι → Spec S Tok Fact Ob) (e : Deferred ι S) : Option Tok := (sp e.1).consumes e.2.2

/-- Main's step on an escalated row (a `#tooth` mutation target): the joint transition on runner
`i`'s dispatch, at main's current configuration. -/
def jstep (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (J : JCfg L S Hole A P Cand Fact Ob i₀) (e : Deferred ι S) :
    Except (JRefusal ι Tok S Hole P Cand Fact) (JCfg L S Hole A P Cand Fact Ob i₀) :=
  jrun L base sp au k J (.dispatch e.1 e.2)

/-- **The joint stitch.** -/
def jstitch (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M) (F : Fork Tok M (Deferred ι S)) :=
  stitch (jstep L base sp au k) main F

variable {L : Ledger ι W Tok} {base : W → View Tok Fact} {sp : ι → Spec S Tok Fact Ob}
variable {au : ι → Authority P Cred} {k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j}

/-- **The stitch is a commit through the joint transition**: a stitched main is reached from main by
joint transitions (the accepted escalated dispatches), so from any start main is reached from, the
stitched main is reached too, and every theorem of a joint run holds of it (the ledger's own fold,
`joint_ledger_fold`; projection; exclusion; consensus). -/
theorem stitch_is_commit {i₀ : Ix} {J₀ : JCfg L S Hole A P Cand Fact Ob i₀}
    (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M) (F : Fork Tok M (Deferred ι S))
    (h : JReachable L base sp au k J₀ main.1) :
    JReachable L base sp au k J₀ (jstitch L base sp au k main F).1.1 :=
  stitch_keeps (jstep L base sp au k) (JReachable L base sp au k J₀) (fun _ e _ hs hst => .step (.dispatch e.1 e.2) hs hst) main F h

/-- The ledger's exclusion at a record: its consumption is its grants, granted once each. -/
def Exclusive (L : Ledger ι W Tok) (d : L.Rec) : Prop :=
  L.spent d = (L.grants d).map Grant.tok ∧ ((L.grants d).map Grant.tok).Nodup

omit [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
  [DecidableEq M] in
theorem commit_exclusive (L : Ledger ι W Tok) {d d' : L.Rec} {i : ι} {t : Tok} (hx : Exclusive L d)
    (h : ledgerStep L d (.commit i t) = .ok d') : Exclusive L d' := by
  simp only [ledgerStep] at h
  split at h
  · split at h <;> cases h
  · rename_i hfresh
    cases h
    refine ⟨?_, ?_⟩
    · rw [L.commit_spent, L.commit_grants, hx.1]; simp
    · rw [L.commit_grants, List.map_append, List.nodup_append]
      refine ⟨hx.2, by simp, ?_⟩
      intro a ha b hb e
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb; subst e
      exact hfresh (by rw [hx.1]; exact ha)

omit [DecidableEq M] in
/-- An accepted escalated dispatch moves the ledger by its own row: a commit of the token it
consumes, or nothing. -/
theorem jstep_ledger {i₀ : Ix} {J J' : JCfg L S Hole A P Cand Fact Ob i₀} {e : Deferred ι S}
    (h : jstep L base sp au k J e = .ok J') : ledgerStep L J.led (ledgerRowOf L (sp e.1) J.led e.1 e.2) = .ok J'.led := by
  simp only [jstep, jrun] at h
  split at h
  · split at h
    · rename_i d hd
      rw [propagate_allowed _ (ledgerStep_allowed L hd)] at h; simp only [Except.map] at h
      cases h; exact hd
    · cases h
  · split at h <;> cases h
  · cases h

omit [DecidableEq M] in
theorem jstep_exclusive {i₀ : Ix} {J J' : JCfg L S Hole A P Cand Fact Ob i₀} {e : Deferred ι S}
    (hx : Exclusive L J.led) (h : jstep L base sp au k J e = .ok J') : Exclusive L J'.led := by
  have hl := jstep_ledger h
  cases ht : (sp e.1).consumes e.2.2 with
  | some t =>
    have : ledgerRowOf L (sp e.1) J.led e.1 e.2 = .commit e.1 t := by simp [ledgerRowOf, ht]
    rw [this] at hl
    exact commit_exclusive L hx hl
  | none => rw [(ledgerStep_rowOf hl).2 ht]; exact hx

omit [DecidableEq M] in
theorem jstep_grants {i₀ : Ix} {J J' : JCfg L S Hole A P Cand Fact Ob i₀} {e : Deferred ι S}
    {g : Grant ι Tok} (hg : g ∈ L.grants J.led) (h : jstep L base sp au k J e = .ok J') : g ∈ L.grants J'.led := by
  have hl := jstep_ledger h
  cases ht : (sp e.1).consumes e.2.2 with
  | some t => rw [(ledgerStep_rowOf hl).1 t ht, L.commit_grants]; exact List.mem_append.2 (.inl hg)
  | none => rw [(ledgerStep_rowOf hl).2 ht]; exact hg

/-- **Stitching keeps the exclusion**: no token is granted twice after any stitch. -/
theorem stitch_exclusive {i₀ : Ix} (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M)
    (F : Fork Tok M (Deferred ι S)) (hx : Exclusive L main.1.led) :
    Exclusive L (jstitch L base sp au k main F).1.1.led :=
  stitch_keeps (jstep L base sp au k) (fun J => Exclusive L J.led) (fun _ _ _ hs hst => jstep_exclusive hs hst) main F hx

/-- **A double-spent ticket across fork and main is refused, naming the epoch**: if the main ledger
granted `t = g.tok` (to `g.winner`, at `g.epoch`) while the fork was offline, the fork's escalated
dispatch consuming `t` is a conflict naming the winner and the epoch, whatever came before it in the
stitch, provided runner `i` is at that call when its turn comes (otherwise its runner refuses it
first, for its own reason, and that refusal is the conflict, `stitch_accounts`). -/
theorem stitch_double_spend {i₀ : Ix} {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
    {stored₀ : ι → (j : Ix) → Hole j → Option Cand} (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
    (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M)
    (hm : JReachable L base sp au k (JCfg.init L d₀ O stored₀) main.1)
    (F : Fork Tok M (Deferred ι S)) (pre rest : List (Deferred ι S)) (i : ι) {j : Ix} {op : S.Op j}
    (hF : F.escalated = pre ++ (i, ⟨j, op⟩) :: rest)
    {kk : (r : S.Resp op) → Prot S Hole A (S.next op r)}
    (hres : (((replay (jstep L base sp au k) main.1 pre).1).cfgs i).cfg.res = ⟨j, .call op kk⟩)
    (hinf : (((replay (jstep L base sp au k) main.1 pre).1).cfgs i).cfg.obj.hist.inflight = none)
    (hend : (((replay (jstep L base sp au k) main.1 pre).1).cfgs i).cfg.ended = none)
    {g : Grant ι Tok} (hg : g ∈ L.grants main.1.led) (ht : (sp i).consumes op = some g.tok) :
    ((i, ⟨j, op⟩), .taken g.tok g.winner g.epoch) ∈ (jstitch L base sp au k main F).2 := by
  show _ ∈ (replay (jstep L base sp au k) main.1 F.escalated).2
  rw [hF, replay_append]
  apply List.mem_append.2; right
  have hreach := replay_keeps (jstep L base sp au k) (JReachable L base sp au k (JCfg.init L d₀ O stored₀))
    (fun _ e _ hs hst => .step (.dispatch e.1 e.2) hs hst) pre main.1 hm
  have hg' := replay_keeps (jstep L base sp au k) (fun J => g ∈ L.grants J.led)
    (fun _ _ _ hs hst => jstep_grants hs hst) pre main.1 hg
  have hstep : jstep L base sp au k (replay (jstep L base sp au k) main.1 pre).1 (i, ⟨j, op⟩) =
      .error (.taken g.tok g.winner g.epoch) :=
    loser_refused_names_winner_and_epoch hs₀ hg₀ hreach i hres hinf hend ht hg' rfl
  simp only [replay, hstep]
  exact List.mem_cons_self ..

end

end Obend.Run.Fork

end
