module
/-
# Obend.Run.Fork — a World fork for offline work, and the one door back: `stitch`

`review/VISION-CLAUDE-20261031.md` §2.1 item 5 and §7.4 (branch-and-stitch: a branch holds no
capability to main, its effects cannot leak, the only door is settlement; the I-confluent part
merges by union, conflicts are objects). Over a shared ledger (`Obend.Run.Shared.Ledger`):

- A FORK (`Fork`) is taken at the main ledger's epoch (its height). It holds no token of the shared
  ledger: it mints its own (`mint`, refused `notMine` for a shared token), spends only its own
  (`spend`, refused `notMine` for any other), and never holds a ledger record, so nothing it does
  reaches main (`fork_owns_no_shared`, `fork_spend_notMine`).
- Its rows are of two kinds. A MONOTONE row (`grow`) adds a fact to a grow-only set: I-confluent, it
  merges by union. A BOUNDED row on a shared token (`defer`) cannot run in the fork; it ESCALATES: the
  fork records it, and it runs at the stitch.
- `stitch` is the one door. The monotone facts merge by union with main's (`stitch_union`; two forks
  stitched in either order give the same facts, `stitch_union_comm`). Each escalated row is a COMMIT
  through the shared step, the ledger member's own row (`ledgerStep`, `.commit`): the accepted ones
  are exactly a run of the ledger's audited fold (`stitch_is_commit`). A refused one is a CONFLICT,
  returned as a section (the row and the ledger's clause), never dropped and never forced
  (`stitch_accounts`: every escalated row is committed or a conflict).
- `stitch_exclusive`: stitching keeps the ledger's exclusion (no token granted twice).
  `stitch_double_spend`: a ticket the main ledger granted while the fork was offline, escalated by
  the fork, is a conflict naming the winner and the epoch of the grant.
-/
public import Obend.Run.Proofs.Shared
@[expose] public section

namespace Obend.Run.Fork

open Obend.Slot Obend.Slot.Protocol Obend.Run.Shared

section
variable {ι W Tok M : Type} [DecidableEq Tok] [DecidableEq M]

/-- A fork: the main epoch it was taken at, the tokens it minted, its own consumption, the monotone
facts it grew, and the bounded rows it escalated (the client and the shared token). -/
structure Fork (ι Tok M : Type) where
  epoch : Nat
  own : List Tok
  spentHere : List Tok
  grown : List M
  escalated : List (ι × Tok)

/-- A row of a fork. -/
inductive FRow (ι Tok M : Type) where
  /-- add a fact to the grow-only set (monotone: merges by union) -/
  | grow (m : M)
  /-- mint a token of the fork's own -/
  | mint (t : Tok)
  /-- spend one of the fork's own tokens -/
  | spend (i : ι) (t : Tok)
  /-- client `i` means to spend the shared token `t`: bounded, it escalates to the stitch -/
  | defer (i : ι) (t : Tok)

/-- Why a fork refused a row. -/
inductive FRefusal (Tok : Type) where
  /-- the token is not the fork's: a fork holds no token of the shared ledger -/
  | notMine (t : Tok)
  /-- the fork's own token is spent already -/
  | spentHere (t : Tok)
  /-- a deferred row names one of the fork's own tokens: spend it -/
  | ownToken (t : Tok)
  deriving DecidableEq, Repr

/-- A fork taken at the main record `d`: nothing of its own yet. -/
def Fork.at (L : Ledger ι W Tok) (d : L.Rec) : Fork ι Tok M := ⟨L.height d, [], [], [], []⟩

/-- One row of a fork. `shared t`: the token is the shared ledger's. -/
def forkStep (shared : Tok → Bool) (F : Fork ι Tok M) : FRow ι Tok M → Except (FRefusal Tok) (Fork ι Tok M)
  | .grow m => .ok { F with grown := F.grown ++ [m] }
  | .mint t => if shared t then .error (.notMine t) else .ok { F with own := F.own ++ [t] }
  | .spend _ t =>
    if t ∈ F.own then
      if t ∈ F.spentHere then .error (.spentHere t) else .ok { F with spentHere := F.spentHere ++ [t] }
    else .error (.notMine t)
  | .defer i t => if t ∈ F.own then .error (.ownToken t) else .ok { F with escalated := F.escalated ++ [(i, t)] }

/-- The forks reachable from a fork. -/
inductive FReachable (shared : Tok → Bool) (F₀ : Fork ι Tok M) : Fork ι Tok M → Prop
  | init : FReachable shared F₀ F₀
  | step {F F' : Fork ι Tok M} (r : FRow ι Tok M) :
      FReachable shared F₀ F → forkStep shared F r = .ok F' → FReachable shared F₀ F'

/-- **A fork holds no token of the shared ledger**: every token a fork taken at a record owns is
one it minted, and none is shared. -/
theorem fork_owns_no_shared {shared : Tok → Bool} {L : Ledger ι W Tok} {d : L.Rec} {F : Fork ι Tok M}
    (h : FReachable shared (Fork.at L d) F) : ∀ t ∈ F.own, shared t = false := by
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
    | defer i t' =>
      simp only [forkStep] at hs; split at hs
      · cases hs
      · cases hs; exact ih t ht

/-- **A fork's write to a shared token is refused `notMine`**: whatever the fork did, spending a
token of the shared ledger in the fork is refused. -/
theorem fork_spend_notMine {shared : Tok → Bool} {L : Ledger ι W Tok} {d : L.Rec} {F : Fork ι Tok M}
    (h : FReachable shared (Fork.at L d) F) (i : ι) {t : Tok} (ht : shared t = true) :
    forkStep shared F (.spend i t) = .error (.notMine t) := by
  have : t ∉ F.own := fun hm => by rw [fork_owns_no_shared h t hm] at ht; cases ht
  simp [forkStep, this]

/-! ## The stitch -/

/-- A conflict: the escalated row and the ledger's refusal of it, kept as a section. -/
abbrev Conflict (ι Tok : Type) := ι × Tok × LClause ι Tok

/-- The escalated rows, each a commit through the ledger's own step; a refused one is a conflict. -/
def stitchRows (L : Ledger ι W Tok) (d : L.Rec) : List (ι × Tok) → L.Rec × List (Conflict ι Tok)
  | [] => (d, [])
  | (i, t) :: rest =>
    match ledgerStep L d (.commit i t) with
    | .ok d' => stitchRows L d' rest
    | .error c => let r := stitchRows L d rest; (r.1, (i, t, c) :: r.2)

/-- The rows the stitch committed. -/
def committed (L : Ledger ι W Tok) (d : L.Rec) : List (ι × Tok) → List (ι × Tok)
  | [] => []
  | (i, t) :: rest =>
    match ledgerStep L d (.commit i t) with
    | .ok d' => (i, t) :: committed L d' rest
    | .error _ => committed L d rest

/-- Union of grow-only sets: main's, then the fork's not already there. -/
def union (xs ys : List M) : List M := xs ++ ys.filter fun y => !decide (y ∈ xs)

/-- **The one door**: the main record and its monotone facts, stitched with a fork. -/
def stitch (L : Ledger ι W Tok) (main : L.Rec × List M) (F : Fork ι Tok M) :
    (L.Rec × List M) × List (Conflict ι Tok) :=
  let r := stitchRows L main.1 F.escalated
  ((r.1, union main.2 F.grown), r.2)

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

/-- **Monotone rows merge by union.** -/
theorem stitch_union (L : Ledger ι W Tok) (main : L.Rec × List M) (F : Fork ι Tok M) (x : M) :
    x ∈ (stitch L main F).1.2 ↔ x ∈ main.2 ∨ x ∈ F.grown := mem_union

/-- **Two forks' monotone rows commute**: stitched in either order, the same facts. -/
theorem stitch_union_comm (L : Ledger ι W Tok) (main : L.Rec × List M) (F G : Fork ι Tok M) (x : M) :
    x ∈ (stitch L (stitch L main F).1 G).1.2 ↔ x ∈ (stitch L (stitch L main G).1 F).1.2 := by
  simp only [stitch_union]
  constructor <;> rintro ((h | h) | h) <;> simp [h]

/-- **The stitch is a commit through the shared step**: the committed rows, as the ledger's own
commit rows, are a run of the ledger's audited fold from the main record to the stitched one. -/
theorem stitch_is_commit {Fact : Type} (L : Ledger ι W Tok) (base : W → View Tok Fact) :
    ∀ (rows : List (ι × Tok)) (d : L.Rec),
      ((committed L d rows).map fun p => LRow.commit p.1 p.2).foldlM (ledgerAdmission L base).step (d, ()) =
        .ok ((stitchRows L d rows).1, ())
  | [], d => rfl
  | (i, t) :: rest, d => by
    simp only [committed, stitchRows]
    cases hs : ledgerStep L d (.commit i t) with
    | ok d' =>
      simp only [List.map_cons, List.foldlM_cons]
      have : (ledgerAdmission L base).step (d, ()) (.commit i t) = .ok (d', ()) := by
        show (ledgerStep L d (.commit i t)).map _ = _; rw [hs]; rfl
      rw [this]
      exact stitch_is_commit L base rest d'
    | error c => exact stitch_is_commit L base rest d

/-- **Conflicts are sections**: every escalated row is committed or returned as a conflict with the
ledger's clause; none is dropped. -/
theorem stitch_accounts (L : Ledger ι W Tok) :
    ∀ (rows : List (ι × Tok)) (d : L.Rec), ∀ p ∈ rows,
      p ∈ committed L d rows ∨ ∃ c, (p.1, p.2, c) ∈ (stitchRows L d rows).2
  | [], _, _, h => by cases h
  | (i, t) :: rest, d, p, hp => by
    simp only [committed, stitchRows]
    cases hs : ledgerStep L d (.commit i t) with
    | ok d' =>
      rcases List.mem_cons.1 hp with rfl | hp
      · exact .inl (List.mem_cons_self ..)
      · rcases stitch_accounts L rest d' p hp with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
    | error c =>
      rcases List.mem_cons.1 hp with rfl | hp
      · exact .inr ⟨c, List.mem_cons_self ..⟩
      · rcases stitch_accounts L rest d p hp with h | ⟨c', h⟩
        · exact .inl h
        · exact .inr ⟨c', List.mem_cons_of_mem _ h⟩

/-- The ledger's exclusion at a record: its consumption is its grants, granted once each. -/
def Exclusive (L : Ledger ι W Tok) (d : L.Rec) : Prop :=
  L.spent d = (L.grants d).map Grant.tok ∧ ((L.grants d).map Grant.tok).Nodup

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

/-- **Stitching keeps the exclusion**: no token is granted twice after any stitch. -/
theorem stitch_exclusive (L : Ledger ι W Tok) :
    ∀ (rows : List (ι × Tok)) (d : L.Rec), Exclusive L d → Exclusive L (stitchRows L d rows).1
  | [], _, hx => hx
  | (i, t) :: rest, d, hx => by
    simp only [stitchRows]
    cases hs : ledgerStep L d (.commit i t) with
    | ok d' => exact stitch_exclusive L rest d' (commit_exclusive L hx hs)
    | error c => exact stitch_exclusive L rest d hx

theorem grantOf_of_mem (L : Ledger ι W Tok) {d : L.Rec} (hx : Exclusive L d) {g : Grant ι Tok}
    (hg : g ∈ L.grants d) : grantOf L d g.tok = some g := by
  unfold grantOf
  cases hf : (L.grants d).find? (fun g' => decide (g'.tok = g.tok)) with
  | none =>
    have := List.find?_eq_none.1 hf g hg
    simp at this
  | some g' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [decide_eq_true_eq] at h2
    rw [nodup_map_inj hx.2 g' h1 g hg h2]

/-- **A double-spent ticket across fork and main is refused, naming the epoch**: if the main ledger
granted `t` (to `g.winner`, at `g.epoch`) while the fork was offline, the fork's escalated spend of
`t` is a conflict naming the winner and the epoch, whatever came before it in the stitch. -/
theorem stitch_double_spend (L : Ledger ι W Tok) :
    ∀ (pre : List (ι × Tok)) (d : L.Rec) (i : ι) (rest : List (ι × Tok)) {g : Grant ι Tok},
      Exclusive L d → g ∈ L.grants d →
      (i, g.tok, .taken g.tok g.winner g.epoch) ∈ (stitchRows L d (pre ++ (i, g.tok) :: rest)).2
  | [], d, i, rest, g, hx, hg => by
    simp only [List.nil_append, stitchRows]
    have hsp : g.tok ∈ L.spent d := by rw [hx.1]; exact List.mem_map.2 ⟨g, hg, rfl⟩
    simp only [ledgerStep, hsp, ↓reduceIte, grantOf_of_mem L hx hg]
    exact List.mem_cons_self ..
  | (j, u) :: pre, d, i, rest, g, hx, hg => by
    simp only [List.cons_append, stitchRows]
    cases hs : ledgerStep L d (.commit j u) with
    | ok d' =>
      have hg' : g ∈ L.grants d' := by
        simp only [ledgerStep] at hs; split at hs
        · split at hs <;> cases hs
        · cases hs; rw [L.commit_grants]; exact List.mem_append.2 (.inl hg)
      exact stitch_double_spend L pre d' i rest (commit_exclusive L hx hs) hg'
    | error c => exact List.mem_cons_of_mem _ (stitch_double_spend L pre d i rest hx hg)

end

end Obend.Run.Fork

end
