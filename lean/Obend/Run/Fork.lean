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

/-- **Monotone union is idempotent**: stitching the same fork's grown facts twice yields the exact same fact membership. -/
theorem stitch_union_idem (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) (x : M) :
    x ∈ (stitch step (stitch step main F).1 F).1.2 ↔ x ∈ (stitch step main F).1.2 := by
  simp only [stitch_union]
  constructor
  · rintro ((h | h) | h)
    · exact .inl h
    · exact .inr h
    · exact .inr h
  · rintro (h | h)
    · exact .inl (.inl h)
    · exact .inr h

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

/-- The conflicts a stitch returns are the replay's. -/
theorem stitch_conflicts (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) :
    (stitch step main F).2 = (replay step main.1 F.escalated).2 := by simp only [stitch]

/-- Replayed rows that fail at every state where `P` holds are conflicts, when every row replayed
keeps `P` where accepted. -/
theorem replay_conflicts {St E R : Type} (step : St → E → Except R St) (P : St → Prop) (Q : E → Prop) :
    ∀ (es : List E), (∀ s e s', e ∈ es → P s → step s e = .ok s' → P s') →
      (∀ s e, e ∈ es → P s → Q e → ∃ c, step s e = .error c) →
      ∀ (s : St), P s → ∀ e ∈ es, Q e → ∃ c, (e, c) ∈ (replay step s es).2
  | [], _, _, _, _, e, he, _ => by cases he
  | x :: rest, keep, fails, s, hs, e, he, hq => by
    have keep' : ∀ s e s', e ∈ rest → P s → step s e = .ok s' → P s' :=
      fun s e s' h => keep s e s' (List.mem_cons_of_mem _ h)
    have fails' : ∀ s e, e ∈ rest → P s → Q e → ∃ c, step s e = .error c :=
      fun s e h => fails s e (List.mem_cons_of_mem _ h)
    simp only [replay]
    cases hx : step s x with
    | ok s' =>
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨c, hc⟩ := fails s e List.mem_cons_self hs hq; rw [hc] at hx; cases hx
      · exact replay_conflicts step P Q rest keep' fails' s' (keep s x s' List.mem_cons_self hs hx) e he hq
    | error c =>
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨c, List.mem_cons_self ..⟩
      · obtain ⟨c', hc'⟩ := replay_conflicts step P Q rest keep' fails' s hs e he hq
        exact ⟨c', List.mem_cons_of_mem _ hc'⟩

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

/-! ## Per-cone independent non-aborting settlement (`settleByCone`, `stitchByCone`, `jstitchByCone`)

`settle` above is all-or-nothing across the entire escalated list: a single conflicting row in one
causal cone aborts every accepted row in disjoint cones. `settleByCone` partitions escalated rows
into causal-cone buckets (`coneBuckets coneOf`) and settles each cone independently:
- If a cone's replay produces zero conflicts, that cone **commits** even when subsequent disjoint
  cones conflict (`settleByConeBuckets_clean_head_commits`, `settleByConeBuckets_clean_proj_survives`).
- If a cone's replay produces conflicts, **only that cone** rolls back to its pre-cone state,
  preserving per-cone atomicity (`settleByConeBuckets_conflict_rolls_back_cone`) and returning every
  refusal witness (`settleByCone_conflict_sound`).
- Every state invariant preserved by `step` (including `JReachable` and `Exclusive`) is preserved
  across `stitchByCone` and `jstitchByCone` (`jstitchByCone_is_commit`, `jstitchByCone_exclusive`). -/

section PerConeSettlement

/-- Deduplicate causal cone IDs in encounter order. -/
def dedupCones {ConeId : Type} [DecidableEq ConeId] : List ConeId → List ConeId
  | [] => []
  | c :: rest => c :: (dedupCones rest).filter (fun x => !decide (x = c))

theorem mem_dedupCones {ConeId : Type} [DecidableEq ConeId] {cs : List ConeId} {x : ConeId} :
    x ∈ dedupCones cs ↔ x ∈ cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [dedupCones, List.mem_cons, List.mem_filter, ih]
    by_cases hxc : x = c
    · subst hxc; simp
    · simp [hxc]

theorem nodup_dedupCones {ConeId : Type} [DecidableEq ConeId] :
    ∀ (cs : List ConeId), (dedupCones cs).Nodup
  | [] => List.Pairwise.nil
  | c :: rest => by
    simp only [dedupCones, List.nodup_cons]
    refine ⟨?_, (nodup_dedupCones rest).filter _⟩
    intro hc
    have hne := (List.mem_filter.mp hc).2
    simp at hne

/-- Partition `es` into per-cone buckets `(c, rows_of_c)` in encounter order. -/
def coneBuckets {ConeId E : Type} [DecidableEq ConeId] (coneOf : E → ConeId) (es : List E) :
    List (ConeId × List E) :=
  (dedupCones (es.map coneOf)).map (fun c => (c, es.filter (fun e => decide (coneOf e = c))))

theorem mem_coneBuckets_of_mem {ConeId E : Type} [DecidableEq ConeId]
    (coneOf : E → ConeId) {es : List E} {e : E} (he : e ∈ es) :
    ∃ bucket ∈ coneBuckets coneOf es, bucket.1 = coneOf e ∧ e ∈ bucket.2 := by
  refine ⟨(coneOf e, es.filter (fun x => decide (coneOf x = coneOf e))), ?_, rfl, ?_⟩
  · simp only [coneBuckets, List.mem_map]
    exact ⟨coneOf e, (mem_dedupCones).mpr (List.mem_map_of_mem he), rfl⟩
  · exact List.mem_filter.mpr ⟨he, by simp⟩

/-- Per-cone settlement decision (`#tooth` mutation target): commits `tentative` iff this cone's
    own replay produced zero conflicts; otherwise rolls back only this cone to `s`. -/
def settleConeOutcome {St E R : Type} (s tentative : St) (conflicts : List (E × R)) : Bool × St :=
  if conflicts.isEmpty then (true, tentative) else (false, s)

/-- Sequentially settle pre-partitioned causal cone buckets: clean cones commit while conflicting
    cones roll back locally without aborting earlier or later disjoint cones. -/
def settleByConeBuckets {ConeId St E R : Type} (step : St → E → Except R St) :
    St → List (ConeId × List E) → St × List ConeId × List (ConeId × List (E × R))
  | s, [] => (s, [], [])
  | s, (c, es) :: rest =>
    let r := replay step s es
    let dec := settleConeOutcome s r.1 r.2
    let tail := settleByConeBuckets step dec.2 rest
    if dec.1 then
      (tail.1, c :: tail.2.1, tail.2.2)
    else
      (tail.1, tail.2.1, (c, r.2) :: tail.2.2)

/-- Settle escalated rows partitioned by `coneOf`. -/
def settleByCone {ConeId St E R : Type} [DecidableEq ConeId]
    (coneOf : E → ConeId) (step : St → E → Except R St) (s : St) (es : List E) :
    St × List ConeId × List (ConeId × List (E × R)) :=
  settleByConeBuckets step s (coneBuckets coneOf es)

/-- Per-cone non-aborting stitch over any main step. -/
def stitchByCone {ConeId St E R M Tok : Type} [DecidableEq ConeId] [DecidableEq M]
    (coneOf : E → ConeId) (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) :
    (St × List M) × List ConeId × List (ConeId × List (E × R)) :=
  let res := settleByCone coneOf step main.1 F.escalated
  ((res.1, union main.2 F.grown), res.2.1, res.2.2)

theorem settleByConeBuckets_keeps {ConeId St E R : Type} (step : St → E → Except R St) (P : St → Prop)
    (keep : ∀ s e s', P s → step s e = .ok s' → P s') :
    ∀ (bs : List (ConeId × List E)) (s : St), P s → P (settleByConeBuckets step s bs).1
  | [], _, hs => hs
  | (c, es) :: rest, s, hs => by
    by_cases hc : (replay step s es).2.isEmpty = true
    · simp only [settleByConeBuckets, settleConeOutcome, hc, ↓reduceIte]
      exact settleByConeBuckets_keeps step P keep rest (replay step s es).1
        (replay_keeps step P keep es s hs)
    · have hf : (replay step s es).2.isEmpty = false := Bool.eq_false_iff.mpr hc
      simp only [settleByConeBuckets, settleConeOutcome, hf, Bool.false_eq_true, ↓reduceIte]
      exact settleByConeBuckets_keeps step P keep rest s hs

theorem stitchByCone_keeps {ConeId St E R M Tok : Type} [DecidableEq ConeId] [DecidableEq M]
    (coneOf : E → ConeId) (step : St → E → Except R St) (P : St → Prop)
    (keep : ∀ s e s', P s → step s e = .ok s' → P s')
    (main : St × List M) (F : Fork Tok M E) (h : P main.1) :
    P (stitchByCone coneOf step main F).1.1 :=
  settleByConeBuckets_keeps step P keep (coneBuckets coneOf F.escalated) main.1 h

theorem stitchByCone_union {ConeId St E R M Tok : Type} [DecidableEq ConeId] [DecidableEq M]
    (coneOf : E → ConeId) (step : St → E → Except R St) (main : St × List M) (F : Fork Tok M E) (x : M) :
    x ∈ (stitchByCone coneOf step main F).1.2 ↔ x ∈ main.2 ∨ x ∈ F.grown := mem_union

/-- **Clean cones commit despite sibling conflicts**: if the head cone `(c, es)` replays with zero
    conflicts, `c` is committed and its post-state seeds the remaining buckets regardless of whether
    any subsequent disjoint cone in `rest` conflicts and rolls back. -/
theorem settleByConeBuckets_clean_head_commits {ConeId St E R : Type}
    (step : St → E → Except R St) (s : St) (c : ConeId) (es : List E) (rest : List (ConeId × List E))
    (hClean : (replay step s es).2 = []) :
    c ∈ (settleByConeBuckets step s ((c, es) :: rest)).2.1 ∧
    (settleByConeBuckets step s ((c, es) :: rest)).1 =
      (settleByConeBuckets step (replay step s es).1 rest).1 := by
  refine ⟨?_, ?_⟩
  · simp only [settleByConeBuckets, settleConeOutcome, hClean, List.isEmpty_nil, ↓reduceIte]
    exact List.mem_cons_self ..
  · simp only [settleByConeBuckets, settleConeOutcome, hClean, List.isEmpty_nil, ↓reduceIte]

/-- **Disjoint-cone state survival**: when subsequent buckets `rest` frame-preserve `proj : St → V`,
    a conflict-free cone `(c, es)` preserves its exact committed projection `proj (replay step s es).1`
    in the final settled state even if every bucket in `rest` aborts with conflicts. -/
theorem settleByConeBuckets_frame_keeps {ConeId St E R V : Type}
    (step : St → E → Except R St) (proj : St → V) :
    ∀ (bs : List (ConeId × List E)) (s : St),
      (∀ b ∈ bs, ∀ e ∈ b.2, ∀ s₁ s₂, step s₁ e = .ok s₂ → proj s₂ = proj s₁) →
      proj (settleByConeBuckets step s bs).1 = proj s
  | [], _, _ => rfl
  | (c, es) :: rest, s, hFrame => by
    have hReplayProj : ∀ (xs : List E) (st : St),
        (∀ x ∈ xs, ∀ s₁ s₂, step s₁ x = .ok s₂ → proj s₂ = proj s₁) →
        proj (replay step st xs).1 = proj st := by
      intro xs
      induction xs with
      | nil => intro _ _; rfl
      | cons x tl ih =>
        intro st hF
        simp only [replay]
        cases hx : step st x with
        | ok st' =>
          rw [ih st' (fun y hy => hF y (List.mem_cons_of_mem _ hy))]
          exact hF x List.mem_cons_self st st' hx
        | error _ => exact ih st (fun y hy => hF y (List.mem_cons_of_mem _ hy))
    have hRestFrame : ∀ b ∈ rest, ∀ e ∈ b.2, ∀ s₁ s₂, step s₁ e = .ok s₂ → proj s₂ = proj s₁ :=
      fun b hb => hFrame b (List.mem_cons_of_mem _ hb)
    by_cases hc : (replay step s es).2.isEmpty = true
    · simp only [settleByConeBuckets, settleConeOutcome, hc, ↓reduceIte]
      rw [settleByConeBuckets_frame_keeps step proj rest _ hRestFrame]
      exact hReplayProj es s (hFrame (c, es) List.mem_cons_self)
    · have hf : (replay step s es).2.isEmpty = false := Bool.eq_false_iff.mpr hc
      simp only [settleByConeBuckets, settleConeOutcome, hf, Bool.false_eq_true, ↓reduceIte]
      exact settleByConeBuckets_frame_keeps step proj rest s hRestFrame

theorem settleByConeBuckets_clean_proj_survives {ConeId St E R V : Type}
    (step : St → E → Except R St) (proj : St → V)
    (s : St) (c : ConeId) (es : List E) (rest : List (ConeId × List E))
    (hClean : (replay step s es).2 = [])
    (hDisjoint : ∀ b ∈ rest, ∀ e ∈ b.2, ∀ s₁ s₂, step s₁ e = .ok s₂ → proj s₂ = proj s₁) :
    proj (settleByConeBuckets step s ((c, es) :: rest)).1 = proj (replay step s es).1 := by
  rw [(settleByConeBuckets_clean_head_commits step s c es rest hClean).2]
  exact settleByConeBuckets_frame_keeps step proj rest (replay step s es).1 hDisjoint

/-- **Per-cone atomic rollback**: if a cone's replay produces at least one conflict, none of its
    partial mutations leak into the continuation state, and its conflicts are recorded verbatim. -/
theorem settleByConeBuckets_conflict_rolls_back_cone {ConeId St E R : Type}
    (step : St → E → Except R St) (s : St) (c : ConeId) (es : List E) (rest : List (ConeId × List E))
    (hConf : (replay step s es).2 ≠ []) :
    (c, (replay step s es).2) ∈ (settleByConeBuckets step s ((c, es) :: rest)).2.2 ∧
    (settleByConeBuckets step s ((c, es) :: rest)).1 = (settleByConeBuckets step s rest).1 := by
  have hFalse : (replay step s es).2.isEmpty = false := List.isEmpty_eq_false_iff.mpr hConf
  refine ⟨?_, ?_⟩
  · simp only [settleByConeBuckets, settleConeOutcome, hFalse, Bool.false_eq_true, ↓reduceIte]
    exact List.mem_cons_self ..
  · simp only [settleByConeBuckets, settleConeOutcome, hFalse, Bool.false_eq_true, ↓reduceIte]

/-- **Anti-narrowing refusal witness (`replay_error_witness`)**: every `(e, r)` in `replay`'s
    conflict list came from a genuine failed `step s_mid e = .error r` on an element `e ∈ es`. -/
theorem replay_conflict_witness {St E R : Type} (step : St → E → Except R St) :
    ∀ (es : List E) (s : St) {e : E} {r : R},
      (e, r) ∈ (replay step s es).2 → e ∈ es ∧ ∃ s_mid, step s_mid e = .error r
  | [], _, _, _, h => by cases h
  | x :: rest, s, e, r, h => by
    simp only [replay] at h
    cases hx : step s x with
    | ok s' =>
      rw [hx] at h
      obtain ⟨hmem, sm, hsm⟩ := replay_conflict_witness step rest s' h
      exact ⟨List.mem_cons_of_mem _ hmem, sm, hsm⟩
    | error rx =>
      rw [hx] at h
      rcases List.mem_cons.mp h with heq | hrest
      · cases heq
        exact ⟨List.mem_cons_self .., s, hx⟩
      · obtain ⟨hmem, sm, hsm⟩ := replay_conflict_witness step rest s hrest
        exact ⟨List.mem_cons_of_mem _ hmem, sm, hsm⟩

/-- **Conflict conservation & anti-narrowing (`settleByConeBuckets_conflict_sound`)**: every aborted
    cone bucket in `settleByConeBuckets` is non-empty and every reported `(e, r)` genuinely failed
    `step` on a row belonging to that bucket. -/
theorem settleByConeBuckets_conflict_sound {ConeId St E R : Type} (step : St → E → Except R St) :
    ∀ (bs : List (ConeId × List E)) (s : St) {c : ConeId} {confs : List (E × R)},
      (c, confs) ∈ (settleByConeBuckets step s bs).2.2 →
      confs ≠ [] ∧ ∃ es, (c, es) ∈ bs ∧ ∀ e r, (e, r) ∈ confs → e ∈ es ∧ ∃ s_mid, step s_mid e = .error r
  | [], _, _, _, h => by cases h
  | (c₀, es₀) :: rest, s, c, confs, h => by
    by_cases hc : (replay step s es₀).2.isEmpty = true
    · simp only [settleByConeBuckets, settleConeOutcome, hc, ↓reduceIte] at h
      obtain ⟨hne, es, hes, hsound⟩ :=
        settleByConeBuckets_conflict_sound step rest (replay step s es₀).1 h
      exact ⟨hne, es, List.mem_cons_of_mem _ hes, hsound⟩
    · have hf : (replay step s es₀).2.isEmpty = false := Bool.eq_false_iff.mpr hc
      simp only [settleByConeBuckets, settleConeOutcome, hf, Bool.false_eq_true, ↓reduceIte] at h
      rcases List.mem_cons.mp h with heq | htail
      · cases heq
        refine ⟨List.isEmpty_eq_false_iff.mp hf, es₀, List.mem_cons_self .., ?_⟩
        intro e r her
        exact replay_conflict_witness step es₀ s her
      · obtain ⟨hne, es, hes, hsound⟩ := settleByConeBuckets_conflict_sound step rest s htail
        exact ⟨hne, es, List.mem_cons_of_mem _ hes, hsound⟩

/-- **Two-cone independent commit + localized conflict (`settleByCone_two_disjoint_first_commits`)**:
    for two distinct causal cones `c₁ ≠ c₂`, if `e₁` (in `c₁`) succeeds on `s` while `e₂` (in `c₂`)
    fails on the post-state `s₁`, `settleByCone` commits `c₁` (reaching `s₁`) and records `c₂` as
    conflicted without aborting `c₁`. -/
theorem settleByCone_two_disjoint_first_commits {ConeId St E R : Type} [DecidableEq ConeId]
    (coneOf : E → ConeId) (step : St → E → Except R St)
    (s s₁ : St) (e₁ e₂ : E) (r₂ : R)
    (hne : coneOf e₁ ≠ coneOf e₂)
    (hOk₁ : step s e₁ = .ok s₁)
    (hErr₂ : step s₁ e₂ = .error r₂) :
    let res := settleByCone coneOf step s [e₁, e₂]
    res.1 = s₁ ∧ coneOf e₁ ∈ res.2.1 ∧ (coneOf e₂, [(e₂, r₂)]) ∈ res.2.2 := by
  have hBuckets : coneBuckets coneOf [e₁, e₂] = [(coneOf e₁, [e₁]), (coneOf e₂, [e₂])] := by
    simp [coneBuckets, dedupCones, hne, Ne.symm hne]
  dsimp only [settleByCone]
  rw [hBuckets]
  simp [settleByConeBuckets, settleConeOutcome, replay, hOk₁, hErr₂]

end PerConeSettlement

section JointPerConeStitch
variable {ConeId Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W M : Type}
variable [DecidableEq ConeId] [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]
variable [DecidableEq Tok] [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)] [DecidableEq M]

/-- **Per-cone non-aborting joint stitch**: independent causal cones commit through `jstep` even
    when a disjoint cone's escalated dispatch fails. -/
def jstitchByCone (coneOf : Deferred ι S → ConeId)
    (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M) (F : Fork Tok M (Deferred ι S)) :=
  stitchByCone coneOf (jstep L base sp au k) main F

variable {L : Ledger ι W Tok} {base : W → View Tok Fact} {sp : ι → Spec S Tok Fact Ob}
variable {au : ι → Authority P Cred} {k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j}

/-- **Per-cone joint stitch is a valid joint commit**: every state reached by `jstitchByCone` is
    reachable from `J₀` by accepted `jrun` dispatches. -/
theorem jstitchByCone_is_commit {i₀ : Ix} {J₀ : JCfg L S Hole A P Cand Fact Ob i₀}
    (coneOf : Deferred ι S → ConeId)
    (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M) (F : Fork Tok M (Deferred ι S))
    (h : JReachable L base sp au k J₀ main.1) :
    JReachable L base sp au k J₀ (jstitchByCone coneOf L base sp au k main F).1.1 :=
  stitchByCone_keeps coneOf (jstep L base sp au k) (JReachable L base sp au k J₀)
    (fun _ e _ hs hst => .step (.dispatch e.1 e.2) hs hst) main F h

/-- **Per-cone joint stitch preserves ledger exclusion**: no shared token is ever double-granted
    across committed cones. -/
theorem jstitchByCone_exclusive {i₀ : Ix} (coneOf : Deferred ι S → ConeId)
    (main : JCfg L S Hole A P Cand Fact Ob i₀ × List M)
    (F : Fork Tok M (Deferred ι S)) (hx : Exclusive L main.1.led) :
    Exclusive L (jstitchByCone coneOf L base sp au k main F).1.1.led :=
  stitchByCone_keeps coneOf (jstep L base sp au k) (fun J => Exclusive L J.led)
    (fun _ _ _ hs hst => jstep_exclusive hs hst) main F hx

end JointPerConeStitch

end Obend.Run.Fork

end
