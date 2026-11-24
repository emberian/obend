module
/-
# Obend.Vault.SemidirectGsp — Stratified Semidirect GSP Multi-Locus Objects, Bounded Escrow Leases & Per-Cone Settlement

Mechanizes the 4-stratum **Stratified Semidirect GSP (`SS-GSP`)** multi-locus object substrate:

1. **Causal-Ancestry Semidirect Product ($C_{\text{data}} \rtimes_\triangleright C_{\text{acl}}$, Weidner–Miller–Meiklejohn):**
   - `SortedNullifierSet`: unboxed `Array Digest256` of 32-byte (`BitVec 256`) capability lineage
     nullifiers with $O(\log N)$ binary-search lookup (`Obend.Core.SortedArray.search`) and direct
     `Array` insertion (`insertNullifierExec`, zero `.toList.toArray` round-trips), proved equivalent
     to linear list membership (`contains_eq_spec`, `0` narrow scalar digests).
   - `CausalStamp`: multi-locus replica vector clock paired with a 256-bit `cSHAKE256` causal-cone
     anchor (`dagAnchor : Digest256`), inducing strict partial causal precedence `t' ≺c t`
     (`causallyLt_irrefl`, `causallyLt_asymm`, `causallyLt_trans`, `concurrent_divergent_ticks`).
   - `actRevoke (rev : Revocation) (op : SignedDataOp)`: annihilates a live `op` to `.noop` **if and
     only if** `rev.nul ∈ op.hdr.nullifiers` and `¬(op.hdr.stamp ≺c rev.stamp)` (`actRevoke_noop_iff`).
   - Proves:
     * **Causally-prior preservation (`causally_prior_write_survives_revocation`):** a replica's own
       write causally preceding its own later revocation survives settlement (curing `Branch.lean:81`).
     * **Concurrent/post-revocation annihilation (`concurrent_write_annihilated`,
       `post_revocation_write_annihilated`):** any concurrent or causally-later write under a revoked
       capability is deterministically annihilated at every replica with zero coordination.
     * **Exact Commutativity & Associativity (`semidirectMerge_comm`, `semidirectMerge_assoc`):**
       replica state merge is strictly order-independent (`=` in the kernel, curing `Branch.lean:84`).
     * **General Semidirect Diamond (`SemidirectRDT`, `semidirect_diamond_converges`):** Weidner's
       abstract `reord` + `act_comm` convergence law instantiated for `add ⋊ scale`.

2. **CISE / `Mandate` Bounded Sub-Object Escrow Leases (`Amber` Offline Debits & Credits):**
   - Each replica `r` holds an explicit `EscrowSlice` (`granted`, `creditedLocally`, `spentLocally`,
     `returned`) carved from a shared `ResourcePool` (bridged to `Obend.Vault.Mandate.Mandate.delegate`
     via `carveEscrowViaMandate_conserves`).
   - Proves **`multi_locus_escrow_nonneg_and_conserved`** across arbitrary multi-turn `ValidEscrowTrace`s:
     replicas execute bounded offline **debits** (`spend ≤ slice.remaining`) and **credits** with
     **zero coordinator round-trips** (`w'.pool = w.pool`), maintaining genuine signed integer
     non-negativity (`0 ≤ globalBalanceInt`), exact live conservation
     (`pool.unallocated + sumNat (slices.map remaining) = pool.total_conserved slices`), and offline
     subset merge preservation (`mergeEscrowSlices_preserves_valid_and_nonneg`), paired with
     open-world anti-narrowing completeness (`escrow_skip_implies_contract_violation`).

3. **MixT / Gallifrey 4-Level Consistency-as-Integrity Grading + Burckhardt GSP (`confirmed · pending`):**
   - 4-element lattice `ConsistencyGrade` (`bluePure < blueSemidirect < amberEscrow < redQuorum`) and
     composite object method IFC checker `checkMethodIfc` tracking both explicit guard taint and
     implicit branch-PC taint, with proved semantic non-interference
     (`ifc_unendorsed_strong_noninterference`) and explicit flush endorsement (`endorseViaFlush`).
   - Burckhardt GSP `GspReplicaState` (`confirmed · pending`) with `rebasePending`, Read-My-Writes
     (`gsp_local_post_read_my_writes`), permutation-invariant quiescent convergence from distinct
     local pending queues and arrival orders (`gsp_rebase_quiescent_agreement`), causal-stability
     tombstone compaction into `SortedNullifierSet` (`compactFinalizedTombstones_exact`), per-cone
     non-aborting settlement (`Obend.Run.Fork.settleByCone`), and coupled multi-turn protocol
     soundness (`apex_semidirect_gsp_multi_turn_sound`).
-/
public import Obend.Core.Digest
public import Obend.Core.SortedArray
public import Obend.Vault.Mandate
public import Obend.Run.Fork
public import Obend.Logic.EnvHarness

public section

namespace Obend.Vault.SemidirectGsp

open Obend.Core.Digest (Digest256 digest256)
open Obend.Core.SortedArray (SortedBy search findSpec search_eq_spec search_sound)
open Obend.Vault.Mandate (Mandate Principal Auth Caveat attenuates delegate_conserves delegate_child_attenuates)
open Obend.Run.Fork (settleByCone settleByCone_two_disjoint_first_commits)
open Obend.Logic.EnvHarness (UniversalEnvHarness)

set_option autoImplicit false

/-! ## 0. Allocation-Free Canonical Strict Comparators & Sorted Extensionality -/

/-- Compose two `Ordering` comparisons lexicographically. -/
def lexOrd (o₁ o₂ : Ordering) : Ordering :=
  match o₁ with
  | .eq => o₂
  | o => o

/-- A comparator inducing an irreflexive, transitive, trichotomous strict linear order. -/
structure LawfulCmp {α : Type} (cmp : α → α → Ordering) : Prop where
  refl  : ∀ a, cmp a a = .eq
  eq_of : ∀ a b, cmp a b = .eq → a = b
  swap  : ∀ a b, cmp a b = .gt ↔ cmp b a = .lt
  trans : ∀ a b c, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt

theorem LawfulCmp.lt_irrefl {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp) (a : α) :
    (cmp a a == .lt) = false := by
  rw [hc.refl a]; rfl

theorem LawfulCmp.lt_trans {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp) {a b c : α}
    (h1 : (cmp a b == .lt) = true) (h2 : (cmp b c == .lt) = true) :
    (cmp a c == .lt) = true := by
  simp only [beq_iff_eq] at h1 h2 ⊢
  exact hc.trans a b c h1 h2

theorem LawfulCmp.trichotomy {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp) (a b : α) :
    (cmp a b == .lt) = true ∨ a = b ∨ (cmp b a == .lt) = true := by
  cases h : cmp a b with
  | lt => exact .inl rfl
  | eq => exact .inr (.inl (hc.eq_of a b h))
  | gt =>
    have hba : cmp b a = .lt := (hc.swap a b).mp h
    exact .inr (.inr (beq_iff_eq.mpr hba))

def cmpNat (a b : Nat) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

theorem lawfulCmp_nat : LawfulCmp cmpNat where
  refl a := by simp [cmpNat]
  eq_of a b h := by
    unfold cmpNat at h
    split at h
    · cases h
    · split at h
      · cases h
      · omega
  swap a b := by
    unfold cmpNat
    split
    · rename_i hlt
      have hn : ¬ (b < a) := by omega
      simp [hlt, hn]
    · rename_i hnlt
      split
      · rename_i hgt; simp [hgt]
      · rename_i hngt; simp [hnlt, hngt]
  trans a b c h1 h2 := by
    unfold cmpNat at h1 h2 ⊢
    split at h1
    · split at h2
      · rename_i hab hbc
        have hac : a < c := Nat.lt_trans hab hbc
        simp [hac]
      · split at h2 <;> cases h2
    · split at h1 <;> cases h1

def cmpInt (a b : Int) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

theorem lawfulCmp_int : LawfulCmp cmpInt where
  refl a := by simp [cmpInt]
  eq_of a b h := by
    unfold cmpInt at h
    split at h
    · cases h
    · split at h
      · cases h
      · omega
  swap a b := by
    unfold cmpInt
    split
    · rename_i hlt
      have hn : ¬ (b < a) := by omega
      simp [hlt, hn]
    · rename_i hnlt
      split
      · rename_i hgt; simp [hgt]
      · rename_i hngt; simp [hnlt, hngt]
  trans a b c h1 h2 := by
    unfold cmpInt at h1 h2 ⊢
    split at h1
    · split at h2
      · rename_i hab hbc
        have hac : a < c := Int.lt_trans hab hbc
        simp [hac]
      · split at h2 <;> cases h2
    · split at h1 <;> cases h1

def cmpBy {α β : Type} (f : α → β) (cmp : β → β → Ordering) (a b : α) : Ordering :=
  cmp (f a) (f b)

theorem lawfulCmp_by {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    {cmp : β → β → Ordering} (hc : LawfulCmp cmp) : LawfulCmp (cmpBy f cmp) where
  refl a := hc.refl (f a)
  eq_of a b h := hf a b (hc.eq_of (f a) (f b) h)
  swap a b := hc.swap (f a) (f b)
  trans a b c h1 h2 := hc.trans (f a) (f b) (f c) h1 h2

def cmpUInt64 : UInt64 → UInt64 → Ordering := cmpBy UInt64.toNat cmpNat
theorem lawfulCmp_uint64 : LawfulCmp cmpUInt64 :=
  lawfulCmp_by UInt64.toNat (fun _ _ h => UInt64.toNat_inj.mp h) lawfulCmp_nat

def cmpDigest256 : Digest256 → Digest256 → Ordering := cmpBy BitVec.toNat cmpNat
theorem lawfulCmp_digest256 : LawfulCmp cmpDigest256 :=
  lawfulCmp_by BitVec.toNat (fun _ _ h => BitVec.eq_of_toNat_eq h) lawfulCmp_nat

def cmpProd {α β : Type} (cmpA : α → α → Ordering) (cmpB : β → β → Ordering)
    (x y : α × β) : Ordering :=
  lexOrd (cmpA x.1 y.1) (cmpB x.2 y.2)

theorem lawfulCmp_prod {α β : Type} {cmpA : α → α → Ordering} {cmpB : β → β → Ordering}
    (ha : LawfulCmp cmpA) (hb : LawfulCmp cmpB) : LawfulCmp (cmpProd cmpA cmpB) where
  refl x := by simp [cmpProd, lexOrd, ha.refl, hb.refl]
  eq_of x y h := by
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    unfold cmpProd lexOrd at h
    cases h1 : cmpA x1 y1 <;> rw [h1] at h
    · cases h
    · exact Prod.ext (ha.eq_of _ _ h1) (hb.eq_of _ _ h)
    · cases h
  swap x y := by
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
    unfold cmpProd lexOrd
    cases h1 : cmpA x1 y1 with
    | lt =>
      have hyx : cmpA y1 x1 ≠ .lt ∧ cmpA y1 x1 ≠ .eq := by
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have := ha.trans x1 y1 x1 h1 hc; rw [ha.refl] at this; cases this
        · have heq := ha.eq_of y1 x1 hc; subst heq; rw [ha.refl] at h1; cases h1
      cases h2 : cmpA y1 x1 <;> simp_all
    | eq =>
      have heq := ha.eq_of x1 y1 h1; subst heq
      rw [ha.refl]
      exact hb.swap x2 y2
    | gt =>
      have hyx : cmpA y1 x1 = .lt := (ha.swap x1 y1).mp h1
      rw [hyx]; simp
  trans x y z h1 h2 := by
    rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩; rcases z with ⟨z1, z2⟩
    unfold cmpProd lexOrd at h1 h2 ⊢
    cases hxy : cmpA x1 y1 <;> rw [hxy] at h1
    · cases hyz : cmpA y1 z1 <;> rw [hyz] at h2
      · rw [ha.trans x1 y1 z1 hxy hyz]
      · have heq := ha.eq_of y1 z1 hyz; subst heq; rw [hxy]
      · cases h2
    · have heq := ha.eq_of x1 y1 hxy; subst heq
      dsimp only at h1 h2 ⊢
      cases hyz : cmpA x1 z1 with
      | lt => rfl
      | eq => rw [hyz] at h2; exact hb.trans x2 y2 z2 h1 h2
      | gt => rw [hyz] at h2; cases h2
    · cases h1

def cmpList {α : Type} (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => lexOrd (cmp x y) (cmpList cmp xs ys)

theorem lawfulCmp_list {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp) :
    LawfulCmp (cmpList cmp) where
  refl xs := by
    induction xs with
    | nil => rfl
    | cons x tl ih => simp [cmpList, lexOrd, hc.refl, ih]
  eq_of xs ys h := by
    induction xs generalizing ys with
    | nil => cases ys <;> first | rfl | cases h
    | cons x tl ih =>
      cases ys with
      | nil => cases h
      | cons y ytl =>
        unfold cmpList lexOrd at h
        cases hxy : cmp x y <;> rw [hxy] at h
        · cases h
        · rw [hc.eq_of x y hxy, ih ytl h]
        · cases h
  swap xs ys := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp [cmpList]
    | cons x tl ih =>
      cases ys with
      | nil => simp [cmpList]
      | cons y ytl =>
        unfold cmpList lexOrd
        cases hxy : cmp x y with
        | lt =>
          cases hyx : cmp y x with
          | lt => have := hc.trans x y x hxy hyx; rw [hc.refl] at this; cases this
          | eq => have he := hc.eq_of y x hyx; subst he; rw [hc.refl] at hxy; cases hxy
          | gt => simp
        | eq =>
          have he := hc.eq_of x y hxy; subst he
          rw [hc.refl]
          exact ih ytl
        | gt =>
          rw [(hc.swap x y).mp hxy]; simp
  trans xs ys zs h1 h2 := by
    induction xs generalizing ys zs with
    | nil =>
      cases ys with
      | nil => cases h1
      | cons _ _ =>
        cases zs with
        | nil => cases h2
        | cons _ _ => rfl
    | cons x tl ih =>
      cases ys with
      | nil => cases h1
      | cons y ytl =>
        cases zs with
        | nil => cases h2
        | cons z ztl =>
          unfold cmpList lexOrd at h1 h2 ⊢
          cases hxy : cmp x y <;> rw [hxy] at h1
          · cases hyz : cmp y z <;> rw [hyz] at h2
            · rw [hc.trans x y z hxy hyz]
            · have he := hc.eq_of y z hyz; subst he; rw [hxy]
            · cases h2
          · have he := hc.eq_of x y hxy; subst he
            dsimp only at h1 h2 ⊢
            cases hyz : cmp x z with
            | lt => rfl
            | eq => rw [hyz] at h2; exact ih ytl ztl h1 h2
            | gt => rw [hyz] at h2; cases h2
          · cases h1

/-- Two strictly-sorted lists over an irreflexive transitive order are equal iff they have the same elements. -/
theorem pairwise_lt_ext {α : Type} {lt : α → α → Bool}
    (hirr : ∀ a, lt a a = false)
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true) :
    ∀ {xs ys : List α},
      xs.Pairwise (fun a b => lt a b = true) →
      ys.Pairwise (fun a b => lt a b = true) →
      (∀ x, x ∈ xs ↔ x ∈ ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | x :: _, [], _, _, hmem => absurd ((hmem x).mp List.mem_cons_self) List.not_mem_nil
  | [], y :: _, _, _, hmem => absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
  | x :: xs, y :: ys, hpx, hpy, hmem => by
    obtain ⟨hx_lt, hpx'⟩ := List.pairwise_cons.mp hpx
    obtain ⟨hy_lt, hpy'⟩ := List.pairwise_cons.mp hpy
    have hxy : x = y := by
      rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h1 | h1
      · exact h1
      · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self) with h2 | h2
        · exact h2.symm
        · have := htrans y x y (hy_lt x h1) (hx_lt y h2)
          rw [hirr y] at this; cases this
    subst hxy
    congr 1
    refine pairwise_lt_ext hirr htrans hpx' hpy' (fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz)) with rfl | hzy
      · have := hx_lt z hz; rw [hirr z] at this; cases this
      · exact hzy
    · rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz)) with rfl | hzx
      · have := hy_lt z hz; rw [hirr z] at this; cases this
      · exact hzx

/-- Sorted set insertion deduplicating by a `LawfulCmp` comparator. -/
def insertByCmp {α : Type} (cmp : α → α → Ordering) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    match cmp x y with
    | .lt => x :: y :: ys
    | .eq => y :: ys
    | .gt => y :: insertByCmp cmp x ys

theorem mem_insertByCmp {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp)
    (x z : α) (ys : List α) :
    z ∈ insertByCmp cmp x ys ↔ z = x ∨ z ∈ ys := by
  induction ys with
  | nil => simp [insertByCmp]
  | cons y tl ih =>
    unfold insertByCmp
    cases hxy : cmp x y with
    | lt => simp only [List.mem_cons] <;> grind
    | eq =>
      have he := hc.eq_of x y hxy; subst he
      simp only [List.mem_cons] <;> grind
    | gt =>
      simp only [List.mem_cons, ih] <;> grind

theorem pairwise_insertByCmp {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp)
    (x : α) (ys : List α) (hp : ys.Pairwise (fun a b => (cmp a b == .lt) = true)) :
    (insertByCmp cmp x ys).Pairwise (fun a b => (cmp a b == .lt) = true) := by
  induction ys with
  | nil => simp [insertByCmp]
  | cons y tl ih =>
    obtain ⟨hy, htl⟩ := List.pairwise_cons.mp hp
    unfold insertByCmp
    cases hxy : cmp x y with
    | lt =>
      have hlt : (cmp x y == .lt) = true := beq_iff_eq.mpr hxy
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨hy, htl⟩⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hztl
      · exact hlt
      · exact hc.lt_trans hlt (hy z hztl)
    | eq => exact List.pairwise_cons.mpr ⟨hy, htl⟩
    | gt =>
      have hyx : (cmp y x == .lt) = true := beq_iff_eq.mpr ((hc.swap x y).mp hxy)
      refine List.pairwise_cons.mpr ⟨?_, ih htl⟩
      intro z hz
      rcases (mem_insertByCmp hc x z tl).mp hz with rfl | hztl
      · exact hyx
      · exact hy z hztl

/-! ## 1. 256-Bit Capability Nullifiers & `Spec ↔ Exec` Binary-Search Array Set -/

/-- Full-width 256-bit capability lineage nullifier (`BitVec 256`, 32 bytes; zero `Nat` digests). -/
abbrev CapNullifier := Digest256

def insertNullifierStep (k : CapNullifier) (st : Array CapNullifier × Bool)
    (x : CapNullifier) : Array CapNullifier × Bool :=
  if st.2 then (st.1.push x, true)
  else match cmpDigest256 k x with
    | .lt => ((st.1.push k).push x, true)
    | .eq => (st.1.push x, true)
    | .gt => (st.1.push x, false)

/-- Direct `Array` nullifier insertion: $O(\log N)$ binary-search fast path on duplicates, else
    single pre-sized `Array.mkEmpty (a.size + 1)` pass with zero `.toList`/`.toArray` round-trips. -/
def insertNullifierExec (a : Array CapNullifier) (k : CapNullifier) : Array CapNullifier :=
  if (search BitVec.toNat a k.toNat (a.size + 1) 0 a.size).isSome then a
  else
    let res := a.foldl (insertNullifierStep k) (Array.mkEmpty (a.size + 1), false)
    if res.2 then res.1 else res.1.push k

private theorem foldl_insertStep_placed (k : CapNullifier) (xs : List CapNullifier)
    (acc : Array CapNullifier) :
    let res := xs.foldl (insertNullifierStep k) (acc, true)
    (if res.2 then res.1 else res.1.push k).toList = acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x tl ih =>
    simp only [List.foldl_cons, insertNullifierStep, ↓reduceIte]
    rw [ih (acc.push x)]
    simp [List.append_assoc]

private theorem foldl_insertStep_unplaced (k : CapNullifier) (xs : List CapNullifier)
    (acc : Array CapNullifier) :
    let res := xs.foldl (insertNullifierStep k) (acc, false)
    (if res.2 then res.1 else res.1.push k).toList =
      acc.toList ++ insertByCmp cmpDigest256 k xs := by
  induction xs generalizing acc with
  | nil => simp [insertByCmp]
  | cons x tl ih =>
    simp only [List.foldl_cons, insertNullifierStep, Bool.false_eq_true, ↓reduceIte, insertByCmp]
    cases hcmp : cmpDigest256 k x with
    | lt =>
      rw [foldl_insertStep_placed k tl ((acc.push k).push x)]
      simp [List.append_assoc]
    | eq =>
      rw [foldl_insertStep_placed k tl (acc.push x)]
      simp [List.append_assoc]
    | gt =>
      rw [ih (acc.push x)]
      simp [List.append_assoc]

private theorem insertByCmp_mem_self {α : Type} {cmp : α → α → Ordering} (hc : LawfulCmp cmp)
    (k : α) : ∀ {xs : List α},
      xs.Pairwise (fun a b => (cmp a b == .lt) = true) →
      k ∈ xs → insertByCmp cmp k xs = xs
  | [], _, h => by cases h
  | x :: tl, hp, hmem => by
    obtain ⟨hx, htl⟩ := List.pairwise_cons.mp hp
    unfold insertByCmp
    rcases List.mem_cons.mp hmem with rfl | hktl
    · rw [hc.refl]
    · have hlt : (cmp x k == .lt) = true := hx k hktl
      have hgt : cmp k x = .gt := (hc.swap k x).mpr (beq_iff_eq.mp hlt)
      rw [hgt, insertByCmp_mem_self hc k htl hktl]

theorem insertNullifierExec_toList (a : Array CapNullifier)
    (hSorted : a.toList.Pairwise (fun x y => (cmpDigest256 x y == .lt) = true))
    (k : CapNullifier) :
    (insertNullifierExec a k).toList = insertByCmp cmpDigest256 k a.toList := by
  unfold insertNullifierExec
  cases hs : (search BitVec.toNat a k.toNat (a.size + 1) 0 a.size) with
  | some found =>
    simp only [Option.isSome_some, ↓reduceIte]
    obtain ⟨i, hi, hxi, hkey⟩ := search_sound BitVec.toNat a k.toNat _ _ _ found hs
    have hfk : found = k := BitVec.eq_of_toNat_eq hkey
    rw [hfk] at hxi
    have hmem : k ∈ a.toList := by
      rw [Array.mem_toList_iff, Array.mem_iff_getElem]
      exact ⟨i, hi, hxi⟩
    exact (insertByCmp_mem_self lawfulCmp_digest256 k hSorted hmem).symm
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ← Array.foldl_toList]
    simpa using foldl_insertStep_unplaced k a.toList (Array.mkEmpty (a.size + 1))

/-- Unboxed sorted array of 256-bit capability nullifiers with $O(\log N)$ binary-search lookup. -/
structure SortedNullifierSet where
  data   : Array CapNullifier
  sorted : data.toList.Pairwise (fun a b => (cmpDigest256 a b == .lt) = true)
  deriving DecidableEq, Repr

@[expose] def SortedNullifierSet.empty : SortedNullifierSet := ⟨#[], List.Pairwise.nil⟩

def SortedNullifierSet.spec (s : SortedNullifierSet) (k : CapNullifier) : Prop :=
  k ∈ s.data.toList

/-- $O(\log N)$ binary search over 256-bit nullifiers via `Obend.Core.SortedArray.search`. -/
@[expose] def SortedNullifierSet.contains (s : SortedNullifierSet) (k : CapNullifier) : Bool :=
  (search BitVec.toNat s.data k.toNat (s.data.size + 1) 0 s.data.size).isSome

/-- Direct `Array` sorted insertion without `.toList.toArray` round-trip. -/
def SortedNullifierSet.insert (s : SortedNullifierSet) (k : CapNullifier) : SortedNullifierSet :=
  ⟨insertNullifierExec s.data k, by
    rw [insertNullifierExec_toList s.data s.sorted k]
    exact pairwise_insertByCmp lawfulCmp_digest256 k s.data.toList s.sorted⟩

def SortedNullifierSet.ofList (ks : List CapNullifier) : SortedNullifierSet :=
  ks.foldl SortedNullifierSet.insert SortedNullifierSet.empty

private theorem cmpDigest256_lt_iff_toNat_lt (a b : CapNullifier) :
    (cmpDigest256 a b == .lt) = true ↔ a.toNat < b.toNat := by
  unfold cmpDigest256 cmpBy cmpNat
  split
  · rename_i h; simp [h]
  · rename_i hn
    split <;> simp [hn]

/-- **`Spec ↔ Exec` Bridge**: $O(\log N)$ binary search over `SortedNullifierSet` equals linear
    list membership on all 256-bit capability nullifiers. -/
theorem SortedNullifierSet.contains_eq_spec (s : SortedNullifierSet) (k : CapNullifier) :
    s.contains k = true ↔ k ∈ s.data.toList := by
  have hs : SortedBy BitVec.toNat s.data := by
    intro i j hi hj hij
    have hp := (List.pairwise_iff_getElem.mp s.sorted) i j (by simpa) (by simpa) hij
    exact (cmpDigest256_lt_iff_toNat_lt _ _).mp (by simpa using hp)
  unfold SortedNullifierSet.contains
  rw [search_eq_spec BitVec.toNat s.data hs k.toNat]
  simp only [findSpec, List.isSome_find?, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨x, hx, he⟩
    have hxk : x = k := BitVec.eq_of_toNat_eq he
    simpa [hxk] using hx
  · intro hk
    exact ⟨k, hk, rfl⟩

@[simp] theorem SortedNullifierSet.mem_insert (s : SortedNullifierSet) (k x : CapNullifier) :
    x ∈ (s.insert k).data.toList ↔ x = k ∨ x ∈ s.data.toList := by
  dsimp only [SortedNullifierSet.insert]
  rw [insertNullifierExec_toList s.data s.sorted k]
  exact mem_insertByCmp lawfulCmp_digest256 k x s.data.toList

theorem SortedNullifierSet.contains_insert_self (s : SortedNullifierSet) (k : CapNullifier) :
    (s.insert k).contains k = true := by
  rw [contains_eq_spec, mem_insert]
  exact .inl rfl

theorem SortedNullifierSet.contains_insert_of_contains (s : SortedNullifierSet) (k x : CapNullifier)
    (h : s.contains x = true) : (s.insert k).contains x = true := by
  rw [contains_eq_spec] at h ⊢
  rw [mem_insert]
  exact .inr h

/-! ## 2. Causal-Ancestry Vector Clocks (`CausalStamp`) & Strict Partial Order (`≺c`) -/

/-- Multi-locus causal stamp: replica sequence entries paired with a 256-bit causal-cone digest anchor. -/
structure CausalStamp where
  entries   : List (Nat × Nat)
  dagAnchor : Digest256
  deriving DecidableEq, Repr

def CausalStamp.genesis : CausalStamp := ⟨[], 0#256⟩

/-- Sequence count observed for `replica` in `t` (`0` if unseen). -/
def CausalStamp.get (t : CausalStamp) (replica : Nat) : Nat :=
  (t.entries.lookup replica).getD 0

private def setClockEntry (replica seq : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(replica, seq)]
  | (r, k) :: rest =>
    if r == replica then (replica, seq) :: rest
    else (r, k) :: setClockEntry replica seq rest

private theorem lookup_setClockEntry_self (replica seq : Nat) :
    ∀ (xs : List (Nat × Nat)), (setClockEntry replica seq xs).lookup replica = some seq
  | [] => by simp [setClockEntry]
  | (r, k) :: rest => by
    unfold setClockEntry
    by_cases hr : r = replica
    · subst hr; simp
    · have hb : (r == replica) = false := beq_eq_false_iff_ne.mpr hr
      have hb2 : (replica == r) = false := beq_eq_false_iff_ne.mpr (Ne.symm hr)
      simp [List.lookup, hb, hb2, lookup_setClockEntry_self replica seq rest]

private theorem lookup_setClockEntry_ne {replica other : Nat} (hne : other ≠ replica) (seq : Nat) :
    ∀ (xs : List (Nat × Nat)), (setClockEntry replica seq xs).lookup other = xs.lookup other
  | [] => by
    have hb : (other == replica) = false := beq_eq_false_iff_ne.mpr hne
    simp [setClockEntry, List.lookup, hb]
  | (r, k) :: rest => by
    unfold setClockEntry
    by_cases hr : r = replica
    · subst hr
      have hb : (other == r) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.lookup, hb]
    · have hb : (r == replica) = false := beq_eq_false_iff_ne.mpr hr
      simp only [hb, Bool.false_eq_true, ↓reduceIte, List.lookup]
      cases other == r
      · exact lookup_setClockEntry_ne hne seq rest
      · rfl

/-- Advance `replica`'s causal clock by 1 and domain-bind `eventTag` into `dagAnchor` via `digest256`. -/
def CausalStamp.tick (t : CausalStamp) (replica : Nat) (eventTag : Digest256) : CausalStamp where
  entries   := setClockEntry replica (t.get replica + 1) t.entries
  dagAnchor := digest256 t.dagAnchor eventTag

theorem CausalStamp.get_tick_self (t : CausalStamp) (r : Nat) (tag : Digest256) :
    (t.tick r tag).get r = t.get r + 1 := by
  simp [CausalStamp.tick, CausalStamp.get, lookup_setClockEntry_self]

theorem CausalStamp.get_tick_ne (t : CausalStamp) {r r' : Nat} (hne : r' ≠ r) (tag : Digest256) :
    (t.tick r tag).get r' = t.get r' := by
  simp [CausalStamp.tick, CausalStamp.get, lookup_setClockEntry_ne hne]

/-- Decidable causal dominance `t₁ ≤c t₂` (`∀ r, t₁.get r ≤ t₂.get r`). -/
@[expose] def causallyLe (t₁ t₂ : CausalStamp) : Bool :=
  (t₁.entries.map Prod.fst).all (fun r => decide (t₁.get r ≤ t₂.get r))

/-- Decidable strict causal precedence `t₁ ≺c t₂` (`t₁ ≤c t₂ ∧ ∃ r, t₁.get r < t₂.get r`). -/
@[expose] def causallyLt (t₁ t₂ : CausalStamp) : Bool :=
  causallyLe t₁ t₂ && (t₂.entries.map Prod.fst).any (fun r => decide (t₁.get r < t₂.get r))

scoped macro:50 a:term:51 " ≺c " b:term:51 : term => `(causallyLt $a $b = true)

/-- Causal concurrency: neither stamp causally precedes the other. -/
def CausalConcurrent (t₁ t₂ : CausalStamp) : Prop :=
  ¬(t₁ ≺c t₂) ∧ ¬(t₂ ≺c t₁)

private theorem lookup_some_mem_fst {α β : Type} [BEq α] [LawfulBEq α]
    {xs : List (α × β)} {k : α} {v : β} (h : xs.lookup k = some v) :
    k ∈ xs.map Prod.fst := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    cases hbeq : (k == hd.1) <;> rw [hbeq] at h
    · exact List.mem_cons_of_mem _ (ih h)
    · have heq : k = hd.1 := beq_iff_eq.mp hbeq
      subst heq
      exact List.mem_cons_self

theorem causallyLe_iff (t₁ t₂ : CausalStamp) :
    causallyLe t₁ t₂ = true ↔ ∀ r : Nat, t₁.get r ≤ t₂.get r := by
  unfold causallyLe
  simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq]
  constructor
  · intro hall r
    unfold CausalStamp.get
    cases hlk : t₁.entries.lookup r with
    | none => exact Nat.zero_le _
    | some _ =>
      obtain ⟨p, hp, hrf⟩ := List.mem_map.mp (lookup_some_mem_fst hlk)
      have hle := hall r ⟨p, hp, hrf⟩
      simpa [CausalStamp.get, hlk] using hle
  · intro hall r _
    exact hall r

theorem causallyLt_iff (t₁ t₂ : CausalStamp) :
    (t₁ ≺c t₂) ↔ (∀ r : Nat, t₁.get r ≤ t₂.get r) ∧ (∃ r : Nat, t₁.get r < t₂.get r) := by
  unfold causallyLt
  simp only [Bool.and_eq_true, causallyLe_iff, List.any_eq_true, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨hle, r, _, hlt⟩
    exact ⟨hle, r, hlt⟩
  · rintro ⟨hle, r, hlt⟩
    refine ⟨hle, r, ?_, hlt⟩
    cases hlk : t₂.entries.lookup r with
    | none =>
      have hz : t₂.get r = 0 := by simp [CausalStamp.get, hlk]
      omega
    | some _ =>
      exact List.mem_map.mp (lookup_some_mem_fst hlk)

theorem causallyLt_irrefl (t : CausalStamp) : ¬(t ≺c t) := by
  rw [causallyLt_iff]
  rintro ⟨_, r, hlt⟩
  exact Nat.lt_irrefl _ hlt

theorem causallyLt_asymm {t₁ t₂ : CausalStamp} (h : t₁ ≺c t₂) : ¬(t₂ ≺c t₁) := by
  rw [causallyLt_iff] at h ⊢
  rcases h with ⟨hle12, r, hlt12⟩
  rintro ⟨hle21, _⟩
  have := hle21 r
  omega

theorem causallyLt_trans {t₁ t₂ t₃ : CausalStamp} (h12 : t₁ ≺c t₂) (h23 : t₂ ≺c t₃) :
    t₁ ≺c t₃ := by
  rw [causallyLt_iff] at h12 h23 ⊢
  rcases h12 with ⟨hle12, r, hlt12⟩
  rcases h23 with ⟨hle23, _⟩
  refine ⟨fun q => Nat.le_trans (hle12 q) (hle23 q), r, Nat.lt_of_lt_of_le hlt12 (hle23 r)⟩

theorem causallyLe_causallyLt_trans {t₁ t₂ t₃ : CausalStamp}
    (h12 : causallyLe t₁ t₂ = true) (h23 : t₂ ≺c t₃) : t₁ ≺c t₃ := by
  rw [causallyLe_iff] at h12
  rw [causallyLt_iff] at h23 ⊢
  rcases h23 with ⟨hle23, r, hlt23⟩
  exact ⟨fun q => Nat.le_trans (h12 q) (hle23 q), r, Nat.lt_of_le_of_lt (h12 r) hlt23⟩

/-- Local `tick` strictly advances causal ancestry (`t ≺c t.tick r tag`). -/
theorem tick_causallyLt (t : CausalStamp) (r : Nat) (tag : Digest256) :
    t ≺c t.tick r tag := by
  rw [causallyLt_iff]
  refine ⟨fun q => ?_, r, ?_⟩
  · by_cases hq : q = r
    · subst hq; rw [CausalStamp.get_tick_self]; omega
    · rw [CausalStamp.get_tick_ne t hq tag]; exact Nat.le_refl _
  · rw [CausalStamp.get_tick_self]; omega

/-- Divergent offline ticks by distinct replicas are strictly causally concurrent (`∥c`). -/
theorem concurrent_divergent_ticks (t : CausalStamp) {r₁ r₂ : Nat} (hne : r₁ ≠ r₂)
    (tag₁ tag₂ : Digest256) :
    CausalConcurrent (t.tick r₁ tag₁) (t.tick r₂ tag₂) := by
  refine ⟨fun h12 => ?_, fun h21 => ?_⟩
  · have hle := ((causallyLt_iff _ _).mp h12).1 r₁
    rw [CausalStamp.get_tick_self, CausalStamp.get_tick_ne t hne tag₂] at hle
    omega
  · have hle := ((causallyLt_iff _ _).mp h21).1 r₂
    rw [CausalStamp.get_tick_self, CausalStamp.get_tick_ne t (Ne.symm hne) tag₁] at hle
    omega

/-! ## 3. Weidner–Miller–Meiklejohn Semidirect RDT Law & Causal Revocation Engine -/

/-- General algebraic law of an op-based Semidirect Product $M_1 \rtimes_\triangleright M_2$
    (Weidner–Miller–Meiklejohn, ICFP/PaPoC 2020). -/
structure SemidirectRDT (State M₁ M₂ : Type) where
  apply₁   : M₁ → State → State
  apply₂   : M₂ → State → State
  act      : M₂ → M₁ → M₁
  comm₁    : ∀ (a b : M₁) (σ : State), apply₁ b (apply₁ a σ) = apply₁ a (apply₁ b σ)
  comm₂    : ∀ (u v : M₂) (σ : State), apply₂ v (apply₂ u σ) = apply₂ u (apply₂ v σ)
  reord    : ∀ (m₁ : M₁) (m₂ : M₂) (σ : State),
    apply₂ m₂ (apply₁ m₁ σ) = apply₁ (act m₂ m₁) (apply₂ m₂ σ)
  act_comm : ∀ (u v : M₂) (m : M₁), act u (act v m) = act v (act u m)

/-- **Weidner Semidirect Diamond Convergence**: applying `(m₁` then `m₂)` at Replica A and
    `(m₂` then `act m₂ m₁)` at Replica B reaches the exact same state with zero coordination. -/
theorem semidirect_diamond_converges {State M₁ M₂ : Type} (S : SemidirectRDT State M₁ M₂)
    (m₁ : M₁) (m₂ : M₂) (σ : State) :
    S.apply₂ m₂ (S.apply₁ m₁ σ) = S.apply₁ (S.act m₂ m₁) (S.apply₂ m₂ σ) :=
  S.reord m₁ m₂ σ

/-- Concrete arithmetic semidirect instance `add(d) ⋊ scale(k)` (`k * (σ + d) = k*σ + k*d`). -/
def addScaleSemidirectRDT : SemidirectRDT Int Int Int where
  apply₁ d σ := σ + d
  apply₂ k σ := k * σ
  act k d := k * d
  comm₁ a b σ := by omega
  comm₂ u v σ := by
    simp only [← Int.mul_assoc]
    rw [Int.mul_comm v u]
  reord d k σ := by rw [Int.mul_add, Int.add_comm]
  act_comm u v m := by
    simp only [← Int.mul_assoc]
    rw [Int.mul_comm u v]

/-- Commutative cell-field payload combinators generalizing `Branch.MergeKind` with signed deltas. -/
inductive SemidirectOpPayload where
  | addDelta (cellId fieldId : UInt64) (delta : Int)
  | maxNat   (cellId fieldId : UInt64) (val : Nat)
  | orMask   (cellId fieldId : UInt64) (mask : UInt64)
  deriving DecidableEq, Repr

/-- Effective data action after semidirect revocation filtering: either `.noop` or `.apply payload`. -/
inductive DataEffect where
  | noop
  | apply (payload : SemidirectOpPayload)
  deriving DecidableEq, Repr

/-- Immutable signed header of a replica data operation (`BitVec 256` opId and nullifiers). -/
structure SignedOpHeader where
  opId       : Digest256
  actor      : UInt64
  stamp      : CausalStamp
  nullifiers : SortedNullifierSet
  payload    : SemidirectOpPayload
  deriving DecidableEq, Repr

/-- Signed replica data operation (`annihilated = false` when authored; `true` iff turned into `.noop`). -/
structure SignedDataOp where
  hdr         : SignedOpHeader
  annihilated : Bool := false
  deriving DecidableEq, Repr

def SignedDataOp.mkLive (hdr : SignedOpHeader) : SignedDataOp :=
  { hdr := hdr, annihilated := false }

def SignedDataOp.effect (op : SignedDataOp) : DataEffect :=
  if op.annihilated then .noop else .apply op.hdr.payload

/-- Control-plane capability revocation carrying a 256-bit nullifier and causal stamp. -/
structure Revocation where
  nul     : CapNullifier
  stamp   : CausalStamp
  revoker : UInt64
  deriving DecidableEq, Repr

/-- **Causal-Ancestry Annihilation Predicate (`#tooth` mutation target)**:
    a revocation `rev` hits `hdr` iff `rev.nul ∈ hdr.nullifiers` AND `¬(hdr.stamp ≺c rev.stamp)`. -/
def revokeHitsHeader (rev : Revocation) (hdr : SignedOpHeader) : Bool :=
  hdr.nullifiers.contains rev.nul && !(causallyLt hdr.stamp rev.stamp)

/-- **Semidirect Action `actRevoke` ($C_{\text{acl}} \triangleright C_{\text{data}}$)**:
    annihilates `op` to `.noop` iff `rev.nul ∈ op.nullifiers ∧ ¬(op.stamp ≺c rev.stamp)`. -/
@[expose] def actRevoke (rev : Revocation) (op : SignedDataOp) : SignedDataOp :=
  if revokeHitsHeader rev op.hdr then { op with annihilated := true } else op

/-- **Exact `actRevoke` Characterization**: on any authored live operation (`op.annihilated = false`),
    `actRevoke rev op` becomes `.noop` iff `rev.nul` is in `op`'s 256-bit nullifier set and `op`
    did NOT causally precede `rev`. -/
theorem actRevoke_noop_iff (rev : Revocation) (hdr : SignedOpHeader) :
    (actRevoke rev (SignedDataOp.mkLive hdr)).effect = .noop ↔
      (rev.nul ∈ hdr.nullifiers.data.toList ∧ ¬(hdr.stamp ≺c rev.stamp)) := by
  unfold actRevoke revokeHitsHeader SignedDataOp.mkLive SignedDataOp.effect
  rw [← hdr.nullifiers.contains_eq_spec rev.nul]
  cases hc : hdr.nullifiers.contains rev.nul <;>
  cases hlt : causallyLt hdr.stamp rev.stamp <;>
  simp

/-- **(1a) Causally-Prior Write Preservation (Curing `Branch.lean:81`!)**:
    a replica's own write authored causally BEFORE a later revocation (`op.stamp ≺c rev.stamp`)
    survives `actRevoke` intact, even when `rev` revokes the exact capability `op` relied on. -/
theorem causally_prior_write_survives_revocation (rev : Revocation) (hdr : SignedOpHeader)
    (hPrior : hdr.stamp ≺c rev.stamp) :
    actRevoke rev (SignedDataOp.mkLive hdr) = SignedDataOp.mkLive hdr ∧
    (actRevoke rev (SignedDataOp.mkLive hdr)).effect = .apply hdr.payload := by
  unfold actRevoke revokeHitsHeader SignedDataOp.mkLive SignedDataOp.effect
  simp [hPrior]

/-- **(1b-i) Concurrent Write Annihilation**: any concurrent write (`op.stamp ∥c rev.stamp`) relying
    on `rev.nul` is deterministically annihilated to `.noop`. -/
theorem concurrent_write_annihilated (rev : Revocation) (hdr : SignedOpHeader)
    (hNul : rev.nul ∈ hdr.nullifiers.data.toList)
    (hConc : CausalConcurrent hdr.stamp rev.stamp) :
    (actRevoke rev (SignedDataOp.mkLive hdr)).effect = .noop :=
  (actRevoke_noop_iff rev hdr).mpr ⟨hNul, hConc.1⟩

/-- **(1b-ii) Post-Revocation Write Annihilation**: any write at or causally after `rev.stamp`
    (`rev.stamp ≤c op.stamp`) relying on `rev.nul` is deterministically annihilated to `.noop`. -/
theorem post_revocation_write_annihilated (rev : Revocation) (hdr : SignedOpHeader)
    (hNul : rev.nul ∈ hdr.nullifiers.data.toList)
    (hAfter : causallyLe rev.stamp hdr.stamp = true) :
    (actRevoke rev (SignedDataOp.mkLive hdr)).effect = .noop := by
  refine (actRevoke_noop_iff rev hdr).mpr ⟨hNul, fun hBefore => ?_⟩
  have hSelf : rev.stamp ≺c rev.stamp := causallyLe_causallyLt_trans hAfter hBefore
  exact causallyLt_irrefl rev.stamp hSelf

/-- **Semidirect Action Commutativity**: concurrent revocations commute on every `SignedDataOp`. -/
theorem actRevoke_comm (r₁ r₂ : Revocation) (op : SignedDataOp) :
    actRevoke r₁ (actRevoke r₂ op) = actRevoke r₂ (actRevoke r₁ op) := by
  unfold actRevoke
  cases h1 : revokeHitsHeader r₁ op.hdr <;> cases h2 : revokeHitsHeader r₂ op.hdr <;>
    simp [h1, h2]

/-- **Semidirect Action Idempotence**: re-applying the same revocation is a no-op. -/
theorem actRevoke_idem (r : Revocation) (op : SignedDataOp) :
    actRevoke r (actRevoke r op) = actRevoke r op := by
  unfold actRevoke
  cases h : revokeHitsHeader r op.hdr <;> simp [h]

/-! ### 3.1 Canonical `RevokeSet`, `SemidirectReplica`, & Order-Independent `semidirectMerge` -/

def cmpCausalStamp : CausalStamp → CausalStamp → Ordering :=
  cmpBy (fun (s : CausalStamp) => (s.dagAnchor, s.entries))
    (cmpProd cmpDigest256 (cmpList (cmpProd cmpNat cmpNat)))

theorem lawfulCmp_causalStamp : LawfulCmp cmpCausalStamp :=
  lawfulCmp_by (fun (s : CausalStamp) => (s.dagAnchor, s.entries))
    (fun (a : CausalStamp) (b : CausalStamp) h => by
      rcases a with ⟨e1, d1⟩; rcases b with ⟨e2, d2⟩
      injection h with hd he; subst hd he; rfl)
    (lawfulCmp_prod lawfulCmp_digest256 (lawfulCmp_list (lawfulCmp_prod lawfulCmp_nat lawfulCmp_nat)))

def cmpRevocation : Revocation → Revocation → Ordering :=
  cmpBy (fun (r : Revocation) => (r.nul, (r.revoker, r.stamp)))
    (cmpProd cmpDigest256 (cmpProd cmpUInt64 cmpCausalStamp))

theorem lawfulCmp_revocation : LawfulCmp cmpRevocation :=
  lawfulCmp_by (fun (r : Revocation) => (r.nul, (r.revoker, r.stamp)))
    (fun (a : Revocation) (b : Revocation) h => by
      rcases a with ⟨n1, s1, a1⟩; rcases b with ⟨n2, s2, a2⟩
      injection h with hn h2; injection h2 with ha hs; subst hn ha hs; rfl)
    (lawfulCmp_prod lawfulCmp_digest256 (lawfulCmp_prod lawfulCmp_uint64 lawfulCmp_causalStamp))

private def payloadKey : SemidirectOpPayload → Nat × UInt64 × UInt64 × Int
  | .addDelta c f d => (0, c, f, d)
  | .maxNat   c f v => (1, c, f, (v : Int))
  | .orMask   c f m => (2, c, f, (m.toNat : Int))

private theorem payloadKey_injective (p₁ p₂ : SemidirectOpPayload)
    (h : payloadKey p₁ = payloadKey p₂) : p₁ = p₂ := by
  cases p₁ <;> cases p₂ <;> simp [payloadKey] at h
  · rcases h with ⟨rfl, rfl, rfl⟩; rfl
  · rcases h with ⟨rfl, rfl, hv⟩
    rename_i v1 v2
    have hv' : v1 = v2 := by omega
    rw [hv']
  · rcases h with ⟨rfl, rfl, hm⟩
    exact congrArg _ (UInt64.toNat_inj.mp (by omega))

def cmpPayload : SemidirectOpPayload → SemidirectOpPayload → Ordering :=
  cmpBy payloadKey (cmpProd cmpNat (cmpProd cmpUInt64 (cmpProd cmpUInt64 cmpInt)))

theorem lawfulCmp_payload : LawfulCmp cmpPayload :=
  lawfulCmp_by payloadKey payloadKey_injective
    (lawfulCmp_prod lawfulCmp_nat (lawfulCmp_prod lawfulCmp_uint64 (lawfulCmp_prod lawfulCmp_uint64 lawfulCmp_int)))

def cmpSignedOpHeader : SignedOpHeader → SignedOpHeader → Ordering :=
  cmpBy (fun (h : SignedOpHeader) => (h.opId, (h.actor, (h.stamp, (h.nullifiers.data.toList, h.payload)))))
    (cmpProd cmpDigest256 (cmpProd cmpUInt64
      (cmpProd cmpCausalStamp (cmpProd (cmpList cmpDigest256) cmpPayload))))

theorem lawfulCmp_signedOpHeader : LawfulCmp cmpSignedOpHeader :=
  lawfulCmp_by (fun (h : SignedOpHeader) => (h.opId, (h.actor, (h.stamp, (h.nullifiers.data.toList, h.payload)))))
    (fun (a : SignedOpHeader) (b : SignedOpHeader) h => by
      rcases a with ⟨id1, ac1, st1, ⟨⟨l1⟩, sn1⟩, p1⟩
      rcases b with ⟨id2, ac2, st2, ⟨⟨l2⟩, sn2⟩, p2⟩
      injection h with hid h2
      injection h2 with hac h3
      injection h3 with hst h4
      injection h4 with hnl hp
      dsimp only at hnl
      subst hid hac hst hnl hp
      rfl)
    (lawfulCmp_prod lawfulCmp_digest256 (lawfulCmp_prod lawfulCmp_uint64
      (lawfulCmp_prod lawfulCmp_causalStamp (lawfulCmp_prod (lawfulCmp_list lawfulCmp_digest256) lawfulCmp_payload))))

/-- Canonical monotone set of `Revocation`s, strictly sorted by `cmpRevocation`. -/
structure RevokeSet where
  items  : List Revocation
  sorted : items.Pairwise (fun a b => (cmpRevocation a b == .lt) = true)
  deriving DecidableEq, Repr

def RevokeSet.empty : RevokeSet := ⟨[], List.Pairwise.nil⟩

def RevokeSet.insert (rs : RevokeSet) (r : Revocation) : RevokeSet :=
  ⟨insertByCmp cmpRevocation r rs.items,
   pairwise_insertByCmp lawfulCmp_revocation r rs.items rs.sorted⟩

def RevokeSet.union (r₁ r₂ : RevokeSet) : RevokeSet :=
  r₂.items.foldl RevokeSet.insert r₁

def RevokeSet.hitsHeader (rs : RevokeSet) (hdr : SignedOpHeader) : Bool :=
  rs.items.any (fun rev => revokeHitsHeader rev hdr)

private theorem mem_foldl_insertRev (xs : List Revocation) (acc : RevokeSet) (x : Revocation) :
    x ∈ (xs.foldl RevokeSet.insert acc).items ↔ x ∈ acc.items ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, ih, RevokeSet.insert,
      mem_insertByCmp lawfulCmp_revocation hd x acc.items, List.mem_cons] <;> grind

@[simp] theorem RevokeSet.mem_insert (rs : RevokeSet) (r x : Revocation) :
    x ∈ (rs.insert r).items ↔ x = r ∨ x ∈ rs.items :=
  mem_insertByCmp lawfulCmp_revocation r x rs.items

@[simp] theorem RevokeSet.mem_union (r₁ r₂ : RevokeSet) (x : Revocation) :
    x ∈ (r₁.union r₂).items ↔ x ∈ r₁.items ∨ x ∈ r₂.items :=
  mem_foldl_insertRev r₂.items r₁ x

theorem RevokeSet.ext {r₁ r₂ : RevokeSet} (h : ∀ x, x ∈ r₁.items ↔ x ∈ r₂.items) : r₁ = r₂ := by
  rcases r₁ with ⟨xs, hxs⟩
  rcases r₂ with ⟨ys, hys⟩
  have heq := pairwise_lt_ext (lt := fun a b => cmpRevocation a b == .lt)
    lawfulCmp_revocation.lt_irrefl (fun a b c => lawfulCmp_revocation.lt_trans) hxs hys h
  subst heq; rfl

theorem RevokeSet.union_comm (r₁ r₂ : RevokeSet) : r₁.union r₂ = r₂.union r₁ :=
  RevokeSet.ext fun x => by simp [or_comm]

theorem RevokeSet.union_assoc (r₁ r₂ r₃ : RevokeSet) :
    (r₁.union r₂).union r₃ = r₁.union (r₂.union r₃) :=
  RevokeSet.ext fun x => by simp [or_assoc]

theorem RevokeSet.union_idem (r : RevokeSet) : r.union r = r :=
  RevokeSet.ext fun x => by simp

theorem RevokeSet.hitsHeader_insert (rs : RevokeSet) (rev : Revocation) (hdr : SignedOpHeader) :
    (rs.insert rev).hitsHeader hdr = (revokeHitsHeader rev hdr || rs.hitsHeader hdr) := by
  apply Bool.eq_iff_iff.mpr
  simp only [RevokeSet.hitsHeader, List.any_eq_true, Bool.or_eq_true, RevokeSet.mem_insert]
  constructor
  · rintro ⟨x, rfl | hx, hh⟩
    · exact .inl hh
    · exact .inr ⟨x, hx, hh⟩
  · rintro (hh | ⟨x, hx, hh⟩)
    · exact ⟨rev, .inl rfl, hh⟩
    · exact ⟨x, .inr hx, hh⟩

theorem RevokeSet.hitsHeader_union (r₁ r₂ : RevokeSet) (hdr : SignedOpHeader) :
    (r₁.union r₂).hitsHeader hdr = (r₁.hitsHeader hdr || r₂.hitsHeader hdr) := by
  apply Bool.eq_iff_iff.mpr
  simp only [RevokeSet.hitsHeader, List.any_eq_true, Bool.or_eq_true, RevokeSet.mem_union]
  constructor
  · rintro ⟨x, h1 | h2, hh⟩
    · exact .inl ⟨x, h1, hh⟩
    · exact .inr ⟨x, h2, hh⟩
  · rintro (⟨x, h1, hh⟩ | ⟨x, h2, hh⟩)
    · exact ⟨x, .inl h1, hh⟩
    · exact ⟨x, .inr h2, hh⟩

/-- Sorted key-value insert merging duplicate `SignedOpHeader` entries via `Bool.or` on `annihilated`. -/
def insertOpEntry (hdr : SignedOpHeader) (ann : Bool) :
    List (SignedOpHeader × Bool) → List (SignedOpHeader × Bool)
  | [] => [(hdr, ann)]
  | (h, a) :: rest =>
    match cmpSignedOpHeader hdr h with
    | .lt => (hdr, ann) :: (h, a) :: rest
    | .eq => (h, a || ann) :: rest
    | .gt => (h, a) :: insertOpEntry hdr ann rest

def lookupOpEntry (hdr : SignedOpHeader) : List (SignedOpHeader × Bool) → Option Bool
  | [] => none
  | (h, a) :: rest =>
    if h == hdr then some a else lookupOpEntry hdr rest

private theorem fst_mem_insertOpEntry (hdr : SignedOpHeader) (ann : Bool)
    (xs : List (SignedOpHeader × Bool)) (q : SignedOpHeader) :
    q ∈ (insertOpEntry hdr ann xs).map Prod.fst ↔ q = hdr ∨ q ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simp [insertOpEntry]
  | cons hd tl ih =>
    rcases hd with ⟨h, a⟩
    unfold insertOpEntry
    cases hcmp : cmpSignedOpHeader hdr h with
    | lt => simp only [List.map_cons, List.mem_cons] <;> grind
    | eq =>
      have he := lawfulCmp_signedOpHeader.eq_of hdr h hcmp; subst he
      simp only [List.map_cons, List.mem_cons] <;> grind
    | gt =>
      simp only [List.map_cons, List.mem_cons, ih] <;> grind

private theorem pairwise_insertOpEntry (hdr : SignedOpHeader) (ann : Bool)
    (xs : List (SignedOpHeader × Bool))
    (hp : xs.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true)) :
    (insertOpEntry hdr ann xs).Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true) := by
  induction xs with
  | nil => simp [insertOpEntry]
  | cons hd tl ih =>
    rcases hd with ⟨h, a⟩
    obtain ⟨hh, htl⟩ := List.pairwise_cons.mp hp
    unfold insertOpEntry
    cases hcmp : cmpSignedOpHeader hdr h with
    | lt =>
      have hlt : (cmpSignedOpHeader hdr h == .lt) = true := beq_iff_eq.mpr hcmp
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨hh, htl⟩⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hztl
      · exact hlt
      · exact lawfulCmp_signedOpHeader.lt_trans hlt (hh z hztl)
    | eq =>
      exact List.pairwise_cons.mpr ⟨hh, htl⟩
    | gt =>
      have hgt : (cmpSignedOpHeader h hdr == .lt) = true :=
        beq_iff_eq.mpr ((lawfulCmp_signedOpHeader.swap hdr h).mp hcmp)
      refine List.pairwise_cons.mpr ⟨?_, ih htl⟩
      intro z hz
      have hzFst : z.1 ∈ (insertOpEntry hdr ann tl).map Prod.fst := List.mem_map_of_mem hz
      rcases (fst_mem_insertOpEntry hdr ann tl z.1).mp hzFst with heq | hin
      · rw [heq]; exact hgt
      · obtain ⟨w, hw, hwEq⟩ := List.mem_map.mp hin
        rw [← hwEq]; exact hh w hw

private theorem lookup_none_of_gt {q : SignedOpHeader} :
    ∀ {xs : List (SignedOpHeader × Bool)},
      (∀ p ∈ xs, (cmpSignedOpHeader q p.1 == .lt) = true) →
      lookupOpEntry q xs = none
  | [], _ => rfl
  | (h, a) :: tl, hall => by
    have hlt : cmpSignedOpHeader q h = .lt := beq_iff_eq.mp (hall (h, a) List.mem_cons_self)
    have hne : h ≠ q := fun he => by
      subst he; rw [lawfulCmp_signedOpHeader.refl] at hlt; cases hlt
    have hb : (h == q) = false := beq_eq_false_iff_ne.mpr hne
    simp only [lookupOpEntry, hb, Bool.false_eq_true, ↓reduceIte]
    exact lookup_none_of_gt (fun p hp => hall p (List.mem_cons_of_mem _ hp))

private theorem lookupOpEntry_insert (hdr q : SignedOpHeader) (ann : Bool)
    (xs : List (SignedOpHeader × Bool))
    (hp : xs.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true)) :
    lookupOpEntry q (insertOpEntry hdr ann xs) =
      if q == hdr then
        match lookupOpEntry hdr xs with
        | some old => some (old || ann)
        | none => some ann
      else lookupOpEntry q xs := by
  induction xs with
  | nil =>
    simp only [insertOpEntry, lookupOpEntry]
    by_cases hq : q = hdr
    · subst hq; simp
    · have hb1 : (hdr == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
      have hb2 : (q == hdr) = false := beq_eq_false_iff_ne.mpr hq
      simp [hb1, hb2]
  | cons hd tl ih =>
    rcases hd with ⟨h, a⟩
    obtain ⟨hh, htl⟩ := List.pairwise_cons.mp hp
    unfold insertOpEntry
    cases hcmp : cmpSignedOpHeader hdr h with
    | lt =>
      have hne_hdr_h : h ≠ hdr := fun he => by
        subst he; rw [lawfulCmp_signedOpHeader.refl] at hcmp; cases hcmp
      by_cases hq : q = hdr
      · subst hq
        have hb : (h == q) = false := beq_eq_false_iff_ne.mpr hne_hdr_h
        have hnone : lookupOpEntry q tl = none :=
          lookup_none_of_gt (fun p hp =>
            lawfulCmp_signedOpHeader.lt_trans (beq_iff_eq.mpr hcmp) (hh p hp))
        simp [lookupOpEntry, hb, hnone]
      · have hb1 : (hdr == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
        have hb2 : (q == hdr) = false := beq_eq_false_iff_ne.mpr hq
        simp [lookupOpEntry, hb1, hb2]
    | eq =>
      have he := lawfulCmp_signedOpHeader.eq_of hdr h hcmp; subst he
      by_cases hq : q = hdr
      · subst hq; simp [lookupOpEntry]
      · have hb1 : (hdr == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
        have hb2 : (q == hdr) = false := beq_eq_false_iff_ne.mpr hq
        simp [lookupOpEntry, hb1, hb2]
    | gt =>
      have hlt_h_hdr : cmpSignedOpHeader h hdr = .lt :=
        (lawfulCmp_signedOpHeader.swap hdr h).mp hcmp
      have hne_h_hdr : h ≠ hdr := fun he => by
        subst he; rw [lawfulCmp_signedOpHeader.refl] at hlt_h_hdr; cases hlt_h_hdr
      by_cases hq : q = hdr
      · subst hq
        have hb : (h == q) = false := beq_eq_false_iff_ne.mpr hne_h_hdr
        simp [lookupOpEntry, hb, ih htl]
      · have hb2 : (q == hdr) = false := beq_eq_false_iff_ne.mpr hq
        by_cases hqh : q = h
        · subst hqh
          simp [lookupOpEntry, hb2]
        · have hb3 : (h == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hqh)
          simp [lookupOpEntry, hb2, hb3, ih htl]

private theorem pairwise_opEntries_ext :
    ∀ {xs ys : List (SignedOpHeader × Bool)},
      xs.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true) →
      ys.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true) →
      (∀ q, lookupOpEntry q xs = lookupOpEntry q ys) →
      xs = ys
  | [], [], _, _, _ => rfl
  | (h, _) :: _, [], _, _, hlk => by
    have := hlk h; simp [lookupOpEntry] at this
  | [], (h, _) :: _, _, _, hlk => by
    have := hlk h; simp [lookupOpEntry] at this
  | (h₁, a₁) :: xs, (h₂, a₂) :: ys, hpx, hpy, hlk => by
    obtain ⟨hx_lt, hpx'⟩ := List.pairwise_cons.mp hpx
    obtain ⟨hy_lt, hpy'⟩ := List.pairwise_cons.mp hpy
    have hh : h₁ = h₂ := by
      rcases lawfulCmp_signedOpHeader.trichotomy h₁ h₂ with hlt | heq | hgt
      · have hnone := lookup_none_of_gt (q := h₁) (xs := (h₂, a₂) :: ys) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hpr
          · exact hlt
          · exact lawfulCmp_signedOpHeader.lt_trans hlt (hy_lt p hpr))
        have hsome := hlk h₁
        rw [hnone] at hsome
        simp [lookupOpEntry] at hsome
      · exact heq
      · have hnone := lookup_none_of_gt (q := h₂) (xs := (h₁, a₁) :: xs) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hpr
          · exact hgt
          · exact lawfulCmp_signedOpHeader.lt_trans hgt (hx_lt p hpr))
        have hsome := (hlk h₂).symm
        rw [hnone] at hsome
        simp [lookupOpEntry] at hsome
    subst hh
    have ha : a₁ = a₂ := by
      have := hlk h₁
      simpa [lookupOpEntry] using this
    subst ha
    congr 1
    refine pairwise_opEntries_ext hpx' hpy' (fun q => ?_)
    by_cases hq : q = h₁
    · subst hq
      rw [lookup_none_of_gt hx_lt, lookup_none_of_gt hy_lt]
    · have hb : (h₁ == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hq)
      have := hlk q
      simpa [lookupOpEntry, hb] using this

/-- Replica state of the Causal-Ancestry Semidirect Product $C_{\text{data}} \rtimes_\triangleright C_{\text{acl}}$. -/
structure SemidirectReplica where
  ops       : List (SignedOpHeader × Bool)
  opsSorted : ops.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true)
  revokes   : RevokeSet
  deriving DecidableEq, Repr

def SemidirectReplica.empty : SemidirectReplica :=
  ⟨[], List.Pairwise.nil, RevokeSet.empty⟩

def SemidirectReplica.lookupOp (s : SemidirectReplica) (hdr : SignedOpHeader) : Option Bool :=
  lookupOpEntry hdr s.ops

/-- Semidirect annihilation bit combiner (`#tooth` mutation target). -/
def mergeKillBit (ann hit : Bool) : Bool := ann || hit

private def applyRevokeSetToEntries (rs : RevokeSet) (xs : List (SignedOpHeader × Bool)) :
    List (SignedOpHeader × Bool) :=
  xs.map (fun (hdr, ann) => (hdr, mergeKillBit ann (rs.hitsHeader hdr)))

private theorem pairwise_applyRevokeSetToEntries (rs : RevokeSet)
    {xs : List (SignedOpHeader × Bool)}
    (hp : xs.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true)) :
    (applyRevokeSetToEntries rs xs).Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true) := by
  unfold applyRevokeSetToEntries
  rw [List.pairwise_map]
  exact hp

private theorem lookup_applyRevokeSetToEntries (rs : RevokeSet)
    (q : SignedOpHeader) (xs : List (SignedOpHeader × Bool)) :
    lookupOpEntry q (applyRevokeSetToEntries rs xs) =
      (lookupOpEntry q xs).map (fun ann => ann || rs.hitsHeader q) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨h, a⟩
    change lookupOpEntry q ((h, mergeKillBit a (rs.hitsHeader h)) :: applyRevokeSetToEntries rs tl) =
      (lookupOpEntry q ((h, a) :: tl)).map (fun ann => ann || rs.hitsHeader q)
    unfold lookupOpEntry mergeKillBit
    by_cases hq : h = q
    · subst hq; simp [Option.map]
    · have hb : (h == q) = false := beq_eq_false_iff_ne.mpr hq
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- Post a signed data operation onto a replica, immediately filtering by known revocations. -/
def SemidirectReplica.postData (s : SemidirectReplica) (op : SignedDataOp) : SemidirectReplica :=
  let ann := op.annihilated || s.revokes.hitsHeader op.hdr
  ⟨insertOpEntry op.hdr ann s.ops,
   pairwise_insertOpEntry op.hdr ann s.ops s.opsSorted,
   s.revokes⟩

/-- Post a control-plane revocation onto a replica, acting via `▷` on all stored data operations. -/
def SemidirectReplica.postRevoke (s : SemidirectReplica) (rev : Revocation) : SemidirectReplica :=
  let rs' := s.revokes.insert rev
  ⟨applyRevokeSetToEntries rs' s.ops,
   pairwise_applyRevokeSetToEntries rs' s.opsSorted,
   rs'⟩

private def unionOpEntries (xs ys : List (SignedOpHeader × Bool)) : List (SignedOpHeader × Bool) :=
  ys.foldl (fun acc (hdr, ann) => insertOpEntry hdr ann acc) xs

private theorem pairwise_unionOpEntries {xs : List (SignedOpHeader × Bool)}
    (ys : List (SignedOpHeader × Bool))
    (hxs : xs.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true)) :
    (unionOpEntries xs ys).Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true) := by
  unfold unionOpEntries
  induction ys generalizing xs with
  | nil => exact hxs
  | cons hd tl ih =>
    rcases hd with ⟨h, a⟩
    exact ih (pairwise_insertOpEntry h a xs hxs)

def combineOptBool : Option Bool → Option Bool → Option Bool
  | some a, some b => some (a || b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

private theorem combineOptBool_comm (x y : Option Bool) :
    combineOptBool x y = combineOptBool y x := by
  cases x <;> cases y <;> simp [combineOptBool, Bool.or_comm]

private theorem combineOptBool_assoc (x y z : Option Bool) :
    combineOptBool (combineOptBool x y) z = combineOptBool x (combineOptBool y z) := by
  cases x <;> cases y <;> cases z <;> simp [combineOptBool, Bool.or_assoc]

private theorem lookup_unionOpEntries (q : SignedOpHeader)
    {xs ys : List (SignedOpHeader × Bool)}
    (hxs : xs.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true))
    (hys : ys.Pairwise (fun a b => (cmpSignedOpHeader a.1 b.1 == .lt) = true)) :
    lookupOpEntry q (unionOpEntries xs ys) =
      combineOptBool (lookupOpEntry q xs) (lookupOpEntry q ys) := by
  unfold unionOpEntries
  induction ys generalizing xs with
  | nil =>
    dsimp only [List.foldl]
    cases lookupOpEntry q xs <;> rfl
  | cons hd tl ih =>
    rcases hd with ⟨h, a⟩
    obtain ⟨hh, htl⟩ := List.pairwise_cons.mp hys
    simp only [List.foldl_cons]
    rw [ih (pairwise_insertOpEntry h a xs hxs) htl, lookupOpEntry_insert h q a xs hxs]
    by_cases hqh : q = h
    · subst hqh
      have hnone : lookupOpEntry q tl = none := lookup_none_of_gt hh
      simp only [beq_self_eq_true, ↓reduceIte, lookupOpEntry, hnone]
      cases lookupOpEntry q xs <;> simp [combineOptBool]
    · have hb1 : (q == h) = false := beq_eq_false_iff_ne.mpr hqh
      have hb2 : (h == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hqh)
      simp [hb1, hb2, lookupOpEntry]

/-- **Order-Independent Semidirect Replica Merge (`semidirectMerge`)**:
    unions `RevokeSet`s and `SignedDataOp` logs and acts via `▷` (`mergeKillBit`),
    guaranteeing exact commutativity and associativity (`Branch.lean:84` cured!). -/
def semidirectMerge (s₁ s₂ : SemidirectReplica) : SemidirectReplica :=
  let rs := s₁.revokes.union s₂.revokes
  let raw := unionOpEntries s₁.ops s₂.ops
  have hRaw := pairwise_unionOpEntries s₂.ops s₁.opsSorted
  ⟨applyRevokeSetToEntries rs raw,
   pairwise_applyRevokeSetToEntries rs hRaw,
   rs⟩

theorem SemidirectReplica.ext {s₁ s₂ : SemidirectReplica}
    (hRev : s₁.revokes = s₂.revokes)
    (hOps : ∀ q, s₁.lookupOp q = s₂.lookupOp q) : s₁ = s₂ := by
  rcases s₁ with ⟨o1, hs1, r1⟩
  rcases s₂ with ⟨o2, hs2, r2⟩
  dsimp only at hRev
  subst hRev
  have ho := pairwise_opEntries_ext hs1 hs2 hOps
  subst ho
  rfl

theorem semidirectMerge_lookupOp (s₁ s₂ : SemidirectReplica) (q : SignedOpHeader) :
    (semidirectMerge s₁ s₂).lookupOp q =
      (combineOptBool (s₁.lookupOp q) (s₂.lookupOp q)).map
        (fun ann => ann || (s₁.revokes.hitsHeader q || s₂.revokes.hitsHeader q)) := by
  unfold semidirectMerge SemidirectReplica.lookupOp
  dsimp only
  rw [lookup_applyRevokeSetToEntries, lookup_unionOpEntries q s₁.opsSorted s₂.opsSorted,
      RevokeSet.hitsHeader_union]

private theorem semidirectMerge_revokes (s₁ s₂ : SemidirectReplica) :
    (semidirectMerge s₁ s₂).revokes = s₁.revokes.union s₂.revokes := rfl

/-- **(1c-i) Exact Commutativity of Semidirect Replica Merge (`semidirectMerge_comm`)**:
    merging `s₁` with `s₂` is strictly equal (`=`) to merging `s₂` with `s₁` in the Lean kernel. -/
theorem semidirectMerge_comm (s₁ s₂ : SemidirectReplica) :
    semidirectMerge s₁ s₂ = semidirectMerge s₂ s₁ := by
  refine SemidirectReplica.ext (RevokeSet.union_comm s₁.revokes s₂.revokes) (fun q => ?_)
  rw [semidirectMerge_lookupOp, semidirectMerge_lookupOp,
      combineOptBool_comm, Bool.or_comm (s₁.revokes.hitsHeader q)]

/-- **(1c-ii) Exact Associativity of Semidirect Replica Merge (`semidirectMerge_assoc`)**:
    three-way replica merge is strictly independent of parenthesization (`=`). -/
theorem semidirectMerge_assoc (s₁ s₂ s₃ : SemidirectReplica) :
    semidirectMerge (semidirectMerge s₁ s₂) s₃ =
      semidirectMerge s₁ (semidirectMerge s₂ s₃) := by
  refine SemidirectReplica.ext (RevokeSet.union_assoc s₁.revokes s₂.revokes s₃.revokes) (fun q => ?_)
  rw [semidirectMerge_lookupOp, semidirectMerge_lookupOp,
      semidirectMerge_lookupOp, semidirectMerge_lookupOp,
      semidirectMerge_revokes, semidirectMerge_revokes,
      RevokeSet.hitsHeader_union, RevokeSet.hitsHeader_union]
  cases s₁.lookupOp q <;>
  cases s₂.lookupOp q <;>
  cases s₃.lookupOp q <;>
  cases s₁.revokes.hitsHeader q <;>
  cases s₂.revokes.hitsHeader q <;>
  cases s₃.revokes.hitsHeader q <;>
  simp [combineOptBool, Bool.or_assoc]

/-- **End-to-End Causally-Prior Survival Across Replica Merge**:
    when a branch posts a live write `hdr` at `hdr.stamp` and subsequently revokes its own
    capability at `rev.stamp` (`hdr.stamp ≺c rev.stamp`), merging with any remote replica `remote`
    that did not concurrently revoke `hdr` preserves `hdr` as live (`some false`, not annihilated). -/
theorem semidirectMerge_causally_prior_survives
    (hdr : SignedOpHeader) (rev : Revocation) (remote : SemidirectReplica)
    (hPrior : hdr.stamp ≺c rev.stamp)
    (hRemoteNotAnn : remote.lookupOp hdr ≠ some true)
    (hRemoteClean : remote.revokes.hitsHeader hdr = false) :
    let localBranch := (SemidirectReplica.empty.postData (SignedDataOp.mkLive hdr)).postRevoke rev
    (semidirectMerge localBranch remote).lookupOp hdr = some false ∧
    (semidirectMerge remote localBranch).lookupOp hdr = some false := by
  intro localBranch
  have hRevFalse : revokeHitsHeader rev hdr = false := by
    unfold revokeHitsHeader; simp [hPrior]
  have hLocalRevClean : localBranch.revokes.hitsHeader hdr = false := by
    simp [localBranch, SemidirectReplica.postRevoke, SemidirectReplica.postData,
          SemidirectReplica.empty, RevokeSet.hitsHeader, RevokeSet.empty, hRevFalse]
  have hLocalLookup : localBranch.lookupOp hdr = some false := by
    change lookupOpEntry hdr
      (applyRevokeSetToEntries localBranch.revokes
        (insertOpEntry hdr (false || RevokeSet.empty.hitsHeader hdr) [])) = some false
    rw [lookup_applyRevokeSetToEntries, lookupOpEntry_insert hdr hdr _ [] List.Pairwise.nil,
        hLocalRevClean]
    simp [RevokeSet.hitsHeader, RevokeSet.empty, lookupOpEntry]
  have hLeft : (semidirectMerge localBranch remote).lookupOp hdr = some false := by
    rw [semidirectMerge_lookupOp, hLocalLookup, hLocalRevClean, hRemoteClean]
    cases hr : remote.lookupOp hdr with
    | none => rfl
    | some b =>
      cases b
      · rfl
      · exact absurd hr hRemoteNotAnn
  exact ⟨hLeft, by rw [semidirectMerge_comm]; exact hLeft⟩

/-- **Zero-Coordination Concurrent Revocation Annihilation Across Merge**:
    if Replica A posts live `hdr` relying on `rev.nul` while Replica B concurrently revokes
    `rev.nul` (`¬(hdr.stamp ≺c rev.stamp)`), both `semidirectMerge A B` and `semidirectMerge B A`
    annihilate `hdr` (`some true`) with zero coordination. -/
theorem semidirectMerge_concurrent_revoke_annihilates
    (sA sB : SemidirectReplica) (hdr : SignedOpHeader) (rev : Revocation)
    (hNul : rev.nul ∈ hdr.nullifiers.data.toList)
    (hNotPrior : ¬(hdr.stamp ≺c rev.stamp)) :
    let repA := sA.postData (SignedDataOp.mkLive hdr)
    let repB := sB.postRevoke rev
    (semidirectMerge repA repB).lookupOp hdr = some true ∧
    (semidirectMerge repB repA).lookupOp hdr = some true := by
  intro repA repB
  have hHit : revokeHitsHeader rev hdr = true := by
    unfold revokeHitsHeader
    rw [(hdr.nullifiers.contains_eq_spec rev.nul).mpr hNul]
    cases hlt : causallyLt hdr.stamp rev.stamp
    · rfl
    · exact absurd hlt hNotPrior
  have hRepBHit : repB.revokes.hitsHeader hdr = true := by
    unfold RevokeSet.hitsHeader
    rw [List.any_eq_true]
    exact ⟨rev, (RevokeSet.mem_insert sB.revokes rev rev).mpr (.inl rfl), hHit⟩
  have hRepALookup : ∃ b, repA.lookupOp hdr = some b := by
    unfold SemidirectReplica.lookupOp
    dsimp only [repA, SemidirectReplica.postData, SignedDataOp.mkLive]
    rw [lookupOpEntry_insert hdr hdr _ sA.ops sA.opsSorted]
    simp only [beq_self_eq_true, ↓reduceIte]
    cases lookupOpEntry hdr sA.ops <;> exact ⟨_, rfl⟩
  obtain ⟨bA, hbA⟩ := hRepALookup
  have hLeft : (semidirectMerge repA repB).lookupOp hdr = some true := by
    rw [semidirectMerge_lookupOp, hbA, hRepBHit]
    cases repB.lookupOp hdr <;> simp [combineOptBool]
  exact ⟨hLeft, by rw [semidirectMerge_comm]; exact hLeft⟩

/-- Materialize surviving additive deltas for `(cellId, fieldId)` from a `SemidirectReplica`. -/
def evalSemidirectFieldDelta (s : SemidirectReplica) (cellId fieldId : UInt64) : Int :=
  s.ops.foldl (fun acc (hdr, ann) =>
    if ann then acc
    else match hdr.payload with
      | .addDelta c f d => if c == cellId && f == fieldId then acc + d else acc
      | _ => acc) 0

theorem evalSemidirectFieldDelta_merge_comm (s₁ s₂ : SemidirectReplica) (cellId fieldId : UInt64) :
    evalSemidirectFieldDelta (semidirectMerge s₁ s₂) cellId fieldId =
      evalSemidirectFieldDelta (semidirectMerge s₂ s₁) cellId fieldId := by
  rw [semidirectMerge_comm]

/-! ## 4. CISE / `Mandate` Bounded Sub-Object Escrow Leases (`Amber` Local Debits & Credits) -/

def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

@[simp] theorem sumNat_nil : sumNat [] = 0 := by simp [sumNat]
@[simp] theorem sumNat_cons (x : Nat) (xs : List Nat) : sumNat (x :: xs) = x + sumNat xs := by
  simp [sumNat]

theorem sumNat_append (xs ys : List Nat) : sumNat (xs ++ ys) = sumNat xs + sumNat ys := by
  induction xs with
  | nil => simp
  | cons x tl ih => simp [ih, Nat.add_assoc]

def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

@[simp] theorem sumInt_nil : sumInt [] = 0 := by simp [sumInt]
@[simp] theorem sumInt_cons (x : Int) (xs : List Int) : sumInt (x :: xs) = x + sumInt xs := by
  simp [sumInt]

/-- Per-replica conserved escrow lease slice (`Amber` tier: local offline debits AND credits!). -/
structure EscrowSlice where
  replicaId       : UInt64
  mandateId       : Nat
  granted         : Nat
  creditedLocally : Nat
  spentLocally    : Nat
  returned        : Nat
  deriving DecidableEq, Repr

/-- Exact non-negative local escrow balance remaining at replica `r`. -/
def EscrowSlice.remaining (s : EscrowSlice) : Nat :=
  (s.granted + s.creditedLocally) - (s.spentLocally + s.returned)

/-- Signed integer escrow balance (non-vacuous `0 ≤ netRemainingInt` target: goes `< 0` on overdraw!). -/
@[expose] def EscrowSlice.netRemainingInt (s : EscrowSlice) : Int :=
  (s.granted : Int) + (s.creditedLocally : Int) - (s.spentLocally : Int) - (s.returned : Int)

/-- Slice validity: cumulative debits plus voluntary returns never exceed granted plus local credits. -/
@[expose] def EscrowSlice.Valid (s : EscrowSlice) : Prop :=
  s.spentLocally + s.returned ≤ s.granted + s.creditedLocally

theorem EscrowSlice.valid_remaining_int {s : EscrowSlice} (hv : s.Valid) :
    0 ≤ s.netRemainingInt ∧ (s.remaining : Int) = s.netRemainingInt := by
  unfold EscrowSlice.Valid EscrowSlice.remaining EscrowSlice.netRemainingInt at *
  omega

/-- Shared coordinator resource pool from which `EscrowSlice`s are carved. -/
structure ResourcePool where
  initialSupply : Nat
  unallocated   : Nat
  deriving DecidableEq, Repr

/-- Conserved net system balance across `pool` and all replicas (`initialSupply + ∑ credits - ∑ debits`). -/
def ResourcePool.total_conserved (pool : ResourcePool) (slices : List EscrowSlice) : Nat :=
  (pool.initialSupply + sumNat (slices.map EscrowSlice.creditedLocally)) -
    sumNat (slices.map EscrowSlice.spentLocally)

/-- Signed integer global balance across unallocated pool and all replica slices. -/
def globalBalanceInt (pool : ResourcePool) (slices : List EscrowSlice) : Int :=
  (pool.unallocated : Int) + sumInt (slices.map EscrowSlice.netRemainingInt)

/-- Multi-locus escrow world state. -/
structure MultiLocusEscrowWorld where
  pool   : ResourcePool
  slices : List EscrowSlice
  deriving DecidableEq, Repr

def initEscrowWorld (supply : Nat) : MultiLocusEscrowWorld where
  pool   := { initialSupply := supply, unallocated := supply }
  slices := []

/-- Inductive conservation & non-overdraw invariant across `pool` and all `EscrowSlice`s. -/
structure EscrowWorldInv (w : MultiLocusEscrowWorld) : Prop where
  nodup_replicas : (w.slices.map EscrowSlice.replicaId).Nodup
  slices_valid   : ∀ s ∈ w.slices, s.Valid
  gross_conserved :
    w.pool.unallocated + sumNat (w.slices.map EscrowSlice.remaining) +
      sumNat (w.slices.map EscrowSlice.spentLocally) =
    w.pool.initialSupply + sumNat (w.slices.map EscrowSlice.creditedLocally)

theorem initEscrowWorld_inv (supply : Nat) : EscrowWorldInv (initEscrowWorld supply) where
  nodup_replicas := List.Pairwise.nil
  slices_valid := fun _ h => by cases h
  gross_conserved := by simp [initEscrowWorld]

/-- Carve an initial `EscrowSlice` directly from an `Obend.Vault.Mandate` delegation step,
    inheriting `Mandate.delegate_conserves` and `Mandate.delegate_child_attenuates`. -/
def carveEscrowViaMandate (parent : Mandate) (replicaId : UInt64) (childId : Nat)
    (child : Principal) (reqRights : List Auth) (quota : Nat) (mask : List Nat)
    (term : Nat) (cv : Caveat) : Mandate × Mandate × EscrowSlice :=
  let (parentAfter, childMandate) :=
    parent.delegate childId child reqRights quota mask term cv
  let slice : EscrowSlice :=
    { replicaId       := replicaId
      mandateId       := childMandate.id
      granted         := childMandate.budget
      creditedLocally := 0
      spentLocally    := 0
      returned        := 0 }
  (parentAfter, childMandate, slice)

theorem carveEscrowViaMandate_conserves (parent : Mandate) (replicaId : UInt64) (childId : Nat)
    (child : Principal) (reqRights : List Auth) (quota : Nat) (mask : List Nat)
    (term : Nat) (cv : Caveat) :
    let (pAfter, cMand, slice) :=
      carveEscrowViaMandate parent replicaId childId child reqRights quota mask term cv
    pAfter.budget + slice.remaining = parent.budget ∧
    attenuates cMand parent ∧
    slice.Valid := by
  dsimp only [carveEscrowViaMandate, EscrowSlice.remaining, EscrowSlice.Valid]
  refine ⟨?_, delegate_child_attenuates parent childId child reqRights quota mask term cv, by omega⟩
  simpa using delegate_conserves parent childId child reqRights quota mask term cv

/-- Guard for bounded local offline debit (`#tooth` mutation target: `spend ≤ slice.remaining`). -/
def canLocalDebit (s : EscrowSlice) (spend : Nat) : Bool :=
  decide (spend ≤ s.remaining)

def findSlice (r : UInt64) : List EscrowSlice → Option EscrowSlice
  | [] => none
  | s :: rest => if s.replicaId == r then some s else findSlice r rest

private def updateSlice (r : UInt64) (f : EscrowSlice → EscrowSlice) :
    List EscrowSlice → List EscrowSlice
  | [] => []
  | s :: rest =>
    if s.replicaId == r then f s :: rest else s :: updateSlice r f rest

/-- Componentwise `max` join of two gossiped views of the same replica's `EscrowSlice`. -/
def EscrowSlice.join (s₁ s₂ : EscrowSlice) : EscrowSlice where
  replicaId       := s₁.replicaId
  mandateId       := s₁.mandateId
  granted         := Max.max s₁.granted s₂.granted
  creditedLocally := Max.max s₁.creditedLocally s₂.creditedLocally
  spentLocally    := Max.max s₁.spentLocally s₂.spentLocally
  returned        := Max.max s₁.returned s₂.returned

/-- Monotone single-writer progression along replica `r`'s local history chain (CISE $\tau_r$). -/
def EscrowSlice.ChainOrdered (s₁ s₂ : EscrowSlice) : Prop :=
  s₁.replicaId = s₂.replicaId ∧ s₁.mandateId = s₂.mandateId ∧
  ((s₁.granted ≤ s₂.granted ∧ s₁.creditedLocally ≤ s₂.creditedLocally ∧
    s₁.spentLocally ≤ s₂.spentLocally ∧ s₁.returned ≤ s₂.returned) ∨
   (s₂.granted ≤ s₁.granted ∧ s₂.creditedLocally ≤ s₁.creditedLocally ∧
    s₂.spentLocally ≤ s₁.spentLocally ∧ s₂.returned ≤ s₁.returned))

/-- **Offline Subset / Peer-Gossip Merge Soundness**: joining any two chain-ordered gossiped states
    of a replica's `EscrowSlice` is commutative and preserves `Valid` + `0 ≤ netRemainingInt`. -/
theorem mergeEscrowSlices_preserves_valid_and_nonneg {s₁ s₂ : EscrowSlice}
    (hv₁ : s₁.Valid) (hv₂ : s₂.Valid) (hChain : s₁.ChainOrdered s₂) :
    s₁.join s₂ = s₂.join s₁ ∧
    (s₁.join s₂).Valid ∧
    0 ≤ (s₁.join s₂).netRemainingInt := by
  rcases hChain with ⟨hr, hm, h12 | h21⟩
  · have hEq2 : s₁.join s₂ = s₂ := by
      rcases s₁ with ⟨r1, m1, g1, c1, sp1, rt1⟩
      rcases s₂ with ⟨r2, m2, g2, c2, sp2, rt2⟩
      dsimp only at hr hm h12
      subst hr hm
      unfold EscrowSlice.join; dsimp only; congr 1 <;> omega
    have hComm : s₁.join s₂ = s₂.join s₁ := by
      rcases s₁ with ⟨r1, m1, g1, c1, sp1, rt1⟩
      rcases s₂ with ⟨r2, m2, g2, c2, sp2, rt2⟩
      dsimp only at hr hm
      subst hr hm
      unfold EscrowSlice.join; dsimp only; congr 1 <;> omega
    refine ⟨hComm, ?_, ?_⟩
    · rw [hEq2]; exact hv₂
    · rw [hEq2]; exact (EscrowSlice.valid_remaining_int hv₂).1
  · have hEq1 : s₁.join s₂ = s₁ := by
      rcases s₁ with ⟨r1, m1, g1, c1, sp1, rt1⟩
      rcases s₂ with ⟨r2, m2, g2, c2, sp2, rt2⟩
      dsimp only at hr hm h21
      subst hr hm
      unfold EscrowSlice.join; dsimp only; congr 1 <;> omega
    have hComm : s₁.join s₂ = s₂.join s₁ := by
      rcases s₁ with ⟨r1, m1, g1, c1, sp1, rt1⟩
      rcases s₂ with ⟨r2, m2, g2, c2, sp2, rt2⟩
      dsimp only at hr hm
      subst hr hm
      unfold EscrowSlice.join; dsimp only; congr 1 <;> omega
    refine ⟨hComm, ?_, ?_⟩
    · rw [hEq1]; exact hv₁
    · rw [hEq1]; exact (EscrowSlice.valid_remaining_int hv₁).1

/-- Open-world syntactic turns over `MultiLocusEscrowWorld`. -/
inductive EscrowTurn where
  | grantSlice  (replica : UInt64) (mandateId amount : Nat)
  | returnSlice (replica : UInt64) (amount : Nat)
  | localDebit  (replica : UInt64) (amount : Nat)
  | localCredit (replica : UInt64) (amount : Nat)
  deriving DecidableEq, Repr

/-- Structured refusal reasons witnessing exact escrow contract violations. -/
inductive EscrowRefusal where
  | unknownReplica   (replica : UInt64)
  | insufficientPool (requested unallocated : Nat)
  | overdrawDebit    (replica : UInt64) (requested remaining : Nat)
  | excessiveReturn  (replica : UInt64) (requested remaining : Nat)
  deriving DecidableEq, Repr

/-- Declarative contract for admissible `EscrowTurn`s. -/
def EscrowTurnContract (w : MultiLocusEscrowWorld) : EscrowTurn → Prop
  | .grantSlice _ _ amount => amount ≤ w.pool.unallocated
  | .returnSlice r amount => ∃ s, findSlice r w.slices = some s ∧ amount ≤ s.remaining
  | .localDebit r amount  => ∃ s, findSlice r w.slices = some s ∧ amount ≤ s.remaining
  | .localCredit r _      => ∃ s, findSlice r w.slices = some s

def EscrowRefusalSound (w : MultiLocusEscrowWorld) (t : EscrowTurn) : EscrowRefusal → Prop
  | .unknownReplica r => findSlice r w.slices = none
  | .insufficientPool req unalloc => unalloc = w.pool.unallocated ∧ ¬(req ≤ w.pool.unallocated)
  | .overdrawDebit r req rem =>
    match t, findSlice r w.slices with
    | .localDebit _ _, some s => rem = s.remaining ∧ ¬(req ≤ s.remaining)
    | _, _ => False
  | .excessiveReturn r req rem =>
    match t, findSlice r w.slices with
    | .returnSlice _ _, some s => rem = s.remaining ∧ ¬(req ≤ s.remaining)
    | _, _ => False

/-- Executable transition function for `MultiLocusEscrowWorld`.
    Notice that `.localDebit` and `.localCredit` leave `w.pool` completely untouched (`0` round-trips!). -/
def stepEscrowWorld (w : MultiLocusEscrowWorld) (t : EscrowTurn) :
    Except EscrowRefusal MultiLocusEscrowWorld :=
  match t with
  | .grantSlice r mandateId amount =>
    if decide (amount ≤ w.pool.unallocated) then
      let pool' := { w.pool with unallocated := w.pool.unallocated - amount }
      match findSlice r w.slices with
      | some _ =>
        .ok { pool := pool'
              slices := updateSlice r (fun s => { s with granted := s.granted + amount }) w.slices }
      | none =>
        let fresh : EscrowSlice := ⟨r, mandateId, amount, 0, 0, 0⟩
        .ok { pool := pool', slices := w.slices ++ [fresh] }
    else .error (.insufficientPool amount w.pool.unallocated)
  | .returnSlice r amount =>
    match findSlice r w.slices with
    | none => .error (.unknownReplica r)
    | some s =>
      if decide (amount ≤ s.remaining) then
        .ok { pool := { w.pool with unallocated := w.pool.unallocated + amount }
              slices := updateSlice r (fun x => { x with returned := x.returned + amount }) w.slices }
      else .error (.excessiveReturn r amount s.remaining)
  | .localDebit r amount =>
    match findSlice r w.slices with
    | none => .error (.unknownReplica r)
    | some s =>
      if canLocalDebit s amount then
        .ok { w with
              slices := updateSlice r (fun x => { x with spentLocally := x.spentLocally + amount }) w.slices }
      else .error (.overdrawDebit r amount s.remaining)
  | .localCredit r amount =>
    match findSlice r w.slices with
    | none => .error (.unknownReplica r)
    | some _ =>
      .ok { w with
            slices := updateSlice r (fun x => { x with creditedLocally := x.creditedLocally + amount }) w.slices }

private theorem findSlice_mem {r : UInt64} {s : EscrowSlice} :
    ∀ {xs : List EscrowSlice}, findSlice r xs = some s → s ∈ xs
  | [], h => by cases h
  | hd :: tl, h => by
    unfold findSlice at h
    by_cases hsr : hd.replicaId = r
    · simp [beq_iff_eq.mpr hsr] at h; subst s; exact List.mem_cons_self
    · simp [beq_eq_false_iff_ne.mpr hsr] at h; exact List.mem_cons_of_mem _ (findSlice_mem h)

private theorem findSlice_none_not_mem (r : UInt64) :
    ∀ {xs : List EscrowSlice}, findSlice r xs = none → r ∉ xs.map EscrowSlice.replicaId
  | [], _ => List.not_mem_nil
  | s :: rest, h => by
    unfold findSlice at h
    by_cases hsr : s.replicaId = r
    · subst hsr; simp at h
    · have hb : (s.replicaId == r) = false := beq_eq_false_iff_ne.mpr hsr
      rw [hb] at h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm hsr, findSlice_none_not_mem r h⟩

private theorem updateSlice_replicaIds (r : UInt64) (f : EscrowSlice → EscrowSlice)
    (hf : ∀ s, (f s).replicaId = s.replicaId) :
    ∀ (xs : List EscrowSlice), (updateSlice r f xs).map EscrowSlice.replicaId = xs.map EscrowSlice.replicaId
  | [] => rfl
  | s :: rest => by
    unfold updateSlice
    split
    · simp [hf s]
    · simp [updateSlice_replicaIds r f hf rest]

private theorem updateSlice_preserves_valid (r : UInt64) (f : EscrowSlice → EscrowSlice) :
    ∀ {xs : List EscrowSlice} {target : EscrowSlice},
      findSlice r xs = some target →
      (f target).Valid →
      (∀ s ∈ xs, s.Valid) →
      ∀ s ∈ updateSlice r f xs, s.Valid
  | [], _, hF, _, _ => by cases hF
  | s :: rest, target, hF, hfV, hall => by
    unfold findSlice at hF
    unfold updateSlice
    by_cases hsr : s.replicaId = r
    · have hb : (s.replicaId == r) = true := beq_iff_eq.mpr hsr
      simp only [hb, ↓reduceIte, Option.some.injEq] at hF ⊢
      rw [← hF] at hfV
      intro q hq
      rcases List.mem_cons.mp hq with hqs | hqr
      · rw [hqs]; exact hfV
      · exact hall q (List.mem_cons_of_mem _ hqr)
    · have hb : (s.replicaId == r) = false := beq_eq_false_iff_ne.mpr hsr
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hF ⊢
      intro q hq
      rcases List.mem_cons.mp hq with hqs | hqr
      · rw [hqs]; exact hall s List.mem_cons_self
      · exact updateSlice_preserves_valid r f hF hfV
          (fun x hx => hall x (List.mem_cons_of_mem _ hx)) q hqr

private theorem sumNat_map_updateSlice (r : UInt64) (f : EscrowSlice → EscrowSlice) (g : EscrowSlice → Nat) :
    ∀ {xs : List EscrowSlice} {target : EscrowSlice},
      (xs.map EscrowSlice.replicaId).Nodup →
      findSlice r xs = some target →
      sumNat ((updateSlice r f xs).map g) + g target = sumNat (xs.map g) + g (f target)
  | [], _, _, hF => by cases hF
  | s :: rest, target, hnd, hF => by
    obtain ⟨_, hnd'⟩ := List.nodup_cons.mp hnd
    unfold findSlice at hF
    unfold updateSlice
    by_cases hsr : s.replicaId = r
    · have hb : (s.replicaId == r) = true := beq_iff_eq.mpr hsr
      simp only [hb, ↓reduceIte, Option.some.injEq] at hF ⊢
      subst target
      simp only [List.map_cons, sumNat_cons]
      omega
    · have hb : (s.replicaId == r) = false := beq_eq_false_iff_ne.mpr hsr
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hF ⊢
      have ih := sumNat_map_updateSlice r f g hnd' hF
      simp only [List.map_cons, sumNat_cons]
      omega

theorem stepEscrowWorld_preserves_inv {w w' : MultiLocusEscrowWorld} {t : EscrowTurn}
    (hInv : EscrowWorldInv w) (hStep : stepEscrowWorld w t = .ok w') :
    EscrowTurnContract w t ∧ EscrowWorldInv w' := by
  cases t with
  | grantSlice r mandateId amount =>
    simp only [stepEscrowWorld] at hStep
    cases hAmtDec : decide (amount ≤ w.pool.unallocated) <;> rw [hAmtDec] at hStep
    · simp at hStep
    · simp only [↓reduceIte] at hStep
      have hAmt : amount ≤ w.pool.unallocated := of_decide_eq_true hAmtDec
      cases hFind : findSlice r w.slices with
      | some s =>
        rw [hFind] at hStep
        simp only [Except.ok.injEq] at hStep; subst w'
        have hsVal : s.Valid := hInv.slices_valid s (findSlice_mem hFind)
        let f := fun x : EscrowSlice => { x with granted := x.granted + amount }
        have hfVal : (f s).Valid := by
          unfold EscrowSlice.Valid at hsVal ⊢; dsimp [f]; omega
        refine ⟨hAmt, ?_, updateSlice_preserves_valid r f hFind hfVal hInv.slices_valid, ?_⟩
        · dsimp only
          rw [updateSlice_replicaIds r f (fun _ => rfl)]
          exact hInv.nodup_replicas
        · dsimp only
          have hRem := sumNat_map_updateSlice r f EscrowSlice.remaining hInv.nodup_replicas hFind
          have hSp  := sumNat_map_updateSlice r f EscrowSlice.spentLocally hInv.nodup_replicas hFind
          have hCr  := sumNat_map_updateSlice r f EscrowSlice.creditedLocally hInv.nodup_replicas hFind
          have hfRem : (f s).remaining = s.remaining + amount := by
            unfold EscrowSlice.remaining; unfold EscrowSlice.Valid at hsVal; dsimp [f]; omega
          have hfSp : (f s).spentLocally = s.spentLocally := rfl
          have hfCr : (f s).creditedLocally = s.creditedLocally := rfl
          dsimp only [f] at hRem hSp hCr hfRem hfSp hfCr
          have hGross := hInv.gross_conserved
          omega
      | none =>
        rw [hFind] at hStep
        simp only [Except.ok.injEq] at hStep; subst w'
        have hNotMem := findSlice_none_not_mem r hFind
        refine ⟨hAmt, ?_, ?_, ?_⟩
        · dsimp only
          rw [List.map_append, List.nodup_append]
          refine ⟨hInv.nodup_replicas, by simp, ?_⟩
          intro x hx y hy heq
          simp at hy; subst hy; subst heq
          exact hNotMem hx
        · intro s hs
          rcases List.mem_append.mp hs with hs | hs
          · exact hInv.slices_valid s hs
          · simp at hs; subst hs; unfold EscrowSlice.Valid; dsimp; omega
        · dsimp only
          simp only [List.map_append, sumNat_append, List.map_cons, List.map_nil, sumNat_cons, sumNat_nil]
          dsimp only [EscrowSlice.remaining]
          have hGross := hInv.gross_conserved
          omega
  | returnSlice r amount =>
    simp only [stepEscrowWorld] at hStep
    cases hFind : findSlice r w.slices with
    | none => rw [hFind] at hStep; cases hStep
    | some s =>
      rw [hFind] at hStep; dsimp only at hStep
      cases hAmtDec : decide (amount ≤ s.remaining) <;> rw [hAmtDec] at hStep
      · simp at hStep
      · simp only [↓reduceIte, Except.ok.injEq] at hStep
        have hAmt : amount ≤ s.remaining := of_decide_eq_true hAmtDec
        subst w'
        have hsVal : s.Valid := hInv.slices_valid s (findSlice_mem hFind)
        let f := fun x : EscrowSlice => { x with returned := x.returned + amount }
        have hfVal : (f s).Valid := by
          unfold EscrowSlice.Valid at hsVal ⊢; unfold EscrowSlice.remaining at hAmt; dsimp [f]; omega
        refine ⟨⟨s, hFind, hAmt⟩, ?_, updateSlice_preserves_valid r f hFind hfVal hInv.slices_valid, ?_⟩
        · dsimp only; rw [updateSlice_replicaIds r f (fun _ => rfl)]; exact hInv.nodup_replicas
        · dsimp only
          have hRem := sumNat_map_updateSlice r f EscrowSlice.remaining hInv.nodup_replicas hFind
          have hSp  := sumNat_map_updateSlice r f EscrowSlice.spentLocally hInv.nodup_replicas hFind
          have hCr  := sumNat_map_updateSlice r f EscrowSlice.creditedLocally hInv.nodup_replicas hFind
          have hfRem : (f s).remaining + amount = s.remaining := by
            unfold EscrowSlice.Valid at hsVal; unfold EscrowSlice.remaining at hAmt ⊢; dsimp [f]; omega
          have hfSp : (f s).spentLocally = s.spentLocally := rfl
          have hfCr : (f s).creditedLocally = s.creditedLocally := rfl
          dsimp only [f] at hRem hSp hCr hfRem hfSp hfCr
          have hGross := hInv.gross_conserved
          omega
  | localDebit r amount =>
    simp only [stepEscrowWorld] at hStep
    cases hFind : findSlice r w.slices with
    | none => rw [hFind] at hStep; cases hStep
    | some s =>
      rw [hFind] at hStep; dsimp only at hStep
      cases hCan : canLocalDebit s amount <;> rw [hCan] at hStep
      · simp at hStep
      · simp only [↓reduceIte, Except.ok.injEq] at hStep
        unfold canLocalDebit at hCan
        have hAmt : amount ≤ s.remaining := of_decide_eq_true hCan
        subst w'
        have hsVal : s.Valid := hInv.slices_valid s (findSlice_mem hFind)
        let f := fun x : EscrowSlice => { x with spentLocally := x.spentLocally + amount }
        have hfVal : (f s).Valid := by
          unfold EscrowSlice.Valid at hsVal ⊢; unfold EscrowSlice.remaining at hAmt; dsimp [f]; omega
        refine ⟨⟨s, hFind, hAmt⟩, ?_, updateSlice_preserves_valid r f hFind hfVal hInv.slices_valid, ?_⟩
        · dsimp only; rw [updateSlice_replicaIds r f (fun _ => rfl)]; exact hInv.nodup_replicas
        · dsimp only
          have hRem := sumNat_map_updateSlice r f EscrowSlice.remaining hInv.nodup_replicas hFind
          have hSp  := sumNat_map_updateSlice r f EscrowSlice.spentLocally hInv.nodup_replicas hFind
          have hCr  := sumNat_map_updateSlice r f EscrowSlice.creditedLocally hInv.nodup_replicas hFind
          have hfRem : (f s).remaining + amount = s.remaining := by
            unfold EscrowSlice.Valid at hsVal; unfold EscrowSlice.remaining at hAmt ⊢; dsimp [f]; omega
          have hfSp : (f s).spentLocally = s.spentLocally + amount := rfl
          have hfCr : (f s).creditedLocally = s.creditedLocally := rfl
          dsimp only [f] at hRem hSp hCr hfRem hfSp hfCr
          have hGross := hInv.gross_conserved
          omega
  | localCredit r amount =>
    simp only [stepEscrowWorld] at hStep
    cases hFind : findSlice r w.slices with
    | none => rw [hFind] at hStep; cases hStep
    | some s =>
      rw [hFind] at hStep; simp only [Except.ok.injEq] at hStep; subst w'
      have hsVal : s.Valid := hInv.slices_valid s (findSlice_mem hFind)
      let f := fun x : EscrowSlice => { x with creditedLocally := x.creditedLocally + amount }
      have hfVal : (f s).Valid := by
        unfold EscrowSlice.Valid at hsVal ⊢; dsimp [f]; omega
      refine ⟨⟨s, hFind⟩, ?_, updateSlice_preserves_valid r f hFind hfVal hInv.slices_valid, ?_⟩
      · dsimp only; rw [updateSlice_replicaIds r f (fun _ => rfl)]; exact hInv.nodup_replicas
      · dsimp only
        have hRem := sumNat_map_updateSlice r f EscrowSlice.remaining hInv.nodup_replicas hFind
        have hSp  := sumNat_map_updateSlice r f EscrowSlice.spentLocally hInv.nodup_replicas hFind
        have hCr  := sumNat_map_updateSlice r f EscrowSlice.creditedLocally hInv.nodup_replicas hFind
        have hfRem : (f s).remaining = s.remaining + amount := by
          unfold EscrowSlice.Valid at hsVal; unfold EscrowSlice.remaining; dsimp [f]; omega
        have hfSp : (f s).spentLocally = s.spentLocally := rfl
        have hfCr : (f s).creditedLocally = s.creditedLocally + amount := rfl
        dsimp only [f] at hRem hSp hCr hfRem hfSp hfCr
        have hGross := hInv.gross_conserved
        omega

/-- Multi-step execution of `EscrowTurn` sequences from `w₀`. -/
def runEscrowTurns : MultiLocusEscrowWorld → List EscrowTurn → Except EscrowRefusal MultiLocusEscrowWorld
  | w, [] => .ok w
  | w, t :: rest => do
    let w' ← stepEscrowWorld w t
    runEscrowTurns w' rest

/-- Multi-turn reachability relation over `MultiLocusEscrowWorld` propagating `stepEscrowWorld` from `w₀`. -/
def ValidEscrowTrace (w₀ : MultiLocusEscrowWorld) (tr : List EscrowTurn)
    (w : MultiLocusEscrowWorld) : Prop :=
  runEscrowTurns w₀ tr = .ok w

private theorem runEscrowTurns_preserves_inv {w₀ w : MultiLocusEscrowWorld} {tr : List EscrowTurn}
    (hInv₀ : EscrowWorldInv w₀) (hTrace : ValidEscrowTrace w₀ tr w) :
    EscrowWorldInv w := by
  unfold ValidEscrowTrace at hTrace
  induction tr generalizing w₀ with
  | nil =>
    simp only [runEscrowTurns, Except.ok.injEq] at hTrace
    subst w
    exact hInv₀
  | cons t rest ih =>
    simp only [runEscrowTurns, bind, Except.bind] at hTrace
    cases hSt : stepEscrowWorld w₀ t <;> rw [hSt] at hTrace
    · cases hTrace
    · exact ih (stepEscrowWorld_preserves_inv hInv₀ hSt).2 hTrace

private theorem sumNat_eq_sumInt {xs : List EscrowSlice} (hv : ∀ s ∈ xs, s.Valid) :
    ((sumNat (xs.map EscrowSlice.remaining) : Nat) : Int) =
      sumInt (xs.map EscrowSlice.netRemainingInt) := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    have hs := (EscrowSlice.valid_remaining_int (hv s List.mem_cons_self)).2
    have hrest := ih (fun q hq => hv q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, sumNat_cons, sumInt_cons]
    omega

/-- **Multi-Locus Escrow Non-Negativity & Exact Conservation (`multi_locus_escrow_nonneg_and_conserved`)**:
    Across ANY multi-turn `ValidEscrowTrace` starting from an invariant-satisfying `w₀` across
    arbitrary grants, returns, offline local debits, and offline local credits:
    1. Every replica's signed balance `s.netRemainingInt` is $\ge 0$ (no slice ever overdraws),
    2. Global signed balance `globalBalanceInt w.pool w.slices` is $\ge 0$,
    3. Exact live pool conservation holds:
       `w.pool.unallocated + sumNat (w.slices.map remaining) = w.pool.total_conserved w.slices`,
    4. Offline local debits and credits execute with **zero coordinator pool contact** (`w'.pool = w.pool`). -/
theorem multi_locus_escrow_nonneg_and_conserved
    {w₀ w : MultiLocusEscrowWorld} {tr : List EscrowTurn}
    (hInv₀ : EscrowWorldInv w₀)
    (hTrace : ValidEscrowTrace w₀ tr w) :
    EscrowWorldInv w ∧
    (∀ s ∈ w.slices, 0 ≤ s.netRemainingInt) ∧
    0 ≤ globalBalanceInt w.pool w.slices ∧
    w.pool.unallocated + sumNat (w.slices.map EscrowSlice.remaining) =
      w.pool.total_conserved w.slices ∧
    (∀ wPre wPost r amt,
      stepEscrowWorld wPre (.localDebit r amt) = .ok wPost → wPost.pool = wPre.pool) ∧
    (∀ wPre wPost r amt,
      stepEscrowWorld wPre (.localCredit r amt) = .ok wPost → wPost.pool = wPre.pool) := by
  have hInv : EscrowWorldInv w := runEscrowTurns_preserves_inv hInv₀ hTrace
  have hSlicesNonneg : ∀ s ∈ w.slices, 0 ≤ s.netRemainingInt :=
    fun s hs => (EscrowSlice.valid_remaining_int (hInv.slices_valid s hs)).1
  have hSumEq : ((sumNat (w.slices.map EscrowSlice.remaining) : Nat) : Int) =
      sumInt (w.slices.map EscrowSlice.netRemainingInt) :=
    sumNat_eq_sumInt hInv.slices_valid
  have hGlobalNonneg : 0 ≤ globalBalanceInt w.pool w.slices := by
    unfold globalBalanceInt
    rw [← hSumEq]
    omega
  have hLiveConserved :
      w.pool.unallocated + sumNat (w.slices.map EscrowSlice.remaining) =
        w.pool.total_conserved w.slices := by
    unfold ResourcePool.total_conserved
    have hg := hInv.gross_conserved
    omega
  refine ⟨hInv, hSlicesNonneg, hGlobalNonneg, hLiveConserved, ?_, ?_⟩
  · intro wPre wPost r amt hSt
    simp only [stepEscrowWorld] at hSt
    cases hF : findSlice r wPre.slices <;> rw [hF] at hSt
    · cases hSt
    · rename_i s
      dsimp only at hSt
      cases hC : canLocalDebit s amt <;> rw [hC] at hSt
      · simp at hSt
      · simp only [↓reduceIte, Except.ok.injEq] at hSt; subst wPost; rfl
  · intro wPre wPost r amt hSt
    simp only [stepEscrowWorld] at hSt
    cases hF : findSlice r wPre.slices <;> rw [hF] at hSt
    · cases hSt
    · simp only [Except.ok.injEq] at hSt; subst wPost; rfl

/-- **Anti-Narrowing Completeness for Escrow Turns (`escrow_skip_implies_contract_violation`)**:
    a turn is refused iff `EscrowTurnContract w t` fails, accompanied by a sound `EscrowRefusal`. -/
theorem escrow_skip_implies_contract_violation (w : MultiLocusEscrowWorld) (t : EscrowTurn) :
    (∀ ref, stepEscrowWorld w t = .error ref → EscrowRefusalSound w t ref ∧ ¬ EscrowTurnContract w t) ∧
    (EscrowTurnContract w t → ∃ w', stepEscrowWorld w t = .ok w') := by
  refine ⟨?_, ?_⟩
  · intro ref hErr
    cases t with
    | grantSlice r mid amt =>
      simp only [stepEscrowWorld] at hErr
      cases hDec : decide (amt ≤ w.pool.unallocated) <;> rw [hDec] at hErr
      · simp only [Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at hErr
        subst ref
        have hn : ¬(amt ≤ w.pool.unallocated) := fun hp => by
          rw [decide_eq_true hp] at hDec; cases hDec
        exact ⟨⟨rfl, hn⟩, hn⟩
      · simp only [↓reduceIte] at hErr
        cases hF : findSlice r w.slices <;> simp [hF] at hErr
    | returnSlice r amt =>
      simp only [stepEscrowWorld] at hErr
      cases hF : findSlice r w.slices <;> rw [hF] at hErr
      · simp only [Except.error.injEq] at hErr; subst ref
        exact ⟨hF, fun ⟨_, hs, _⟩ => by rw [hF] at hs; cases hs⟩
      · rename_i s
        dsimp only at hErr
        cases hDec : decide (amt ≤ s.remaining) <;> rw [hDec] at hErr
        · simp only [Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at hErr
          subst ref
          have hn : ¬(amt ≤ s.remaining) := fun hp => by
            rw [decide_eq_true hp] at hDec; cases hDec
          exact ⟨by simp [EscrowRefusalSound, hF, hn],
                 fun ⟨s', hs', hle⟩ => by rw [hF] at hs'; cases hs'; exact hn hle⟩
        · simp at hErr
    | localDebit r amt =>
      simp only [stepEscrowWorld] at hErr
      cases hF : findSlice r w.slices <;> rw [hF] at hErr
      · simp only [Except.error.injEq] at hErr; subst ref
        exact ⟨hF, fun ⟨_, hs, _⟩ => by rw [hF] at hs; cases hs⟩
      · rename_i s
        dsimp only at hErr
        cases hDec : canLocalDebit s amt <;> rw [hDec] at hErr
        · simp only [Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at hErr
          subst ref
          unfold canLocalDebit at hDec
          have hn : ¬(amt ≤ s.remaining) := fun hp => by
            rw [decide_eq_true hp] at hDec; cases hDec
          exact ⟨by simp [EscrowRefusalSound, hF, hn],
                 fun ⟨s', hs', hle⟩ => by rw [hF] at hs'; cases hs'; exact hn hle⟩
        · simp at hErr
    | localCredit r amt =>
      simp only [stepEscrowWorld] at hErr
      cases hF : findSlice r w.slices <;> rw [hF] at hErr
      · simp only [Except.error.injEq] at hErr; subst ref
        exact ⟨hF, fun ⟨_, hs⟩ => by rw [hF] at hs; cases hs⟩
      · cases hErr
  · intro hC
    cases t with
    | grantSlice r mid amt =>
      dsimp only [EscrowTurnContract] at hC
      simp only [stepEscrowWorld, decide_eq_true hC, ↓reduceIte]
      cases findSlice r w.slices <;> exact ⟨_, rfl⟩
    | returnSlice r amt =>
      rcases hC with ⟨s, hF, hle⟩
      simp [stepEscrowWorld, hF, decide_eq_true hle]
    | localDebit r amt =>
      rcases hC with ⟨s, hF, hle⟩
      simp [stepEscrowWorld, canLocalDebit, hF, decide_eq_true hle]
    | localCredit r amt =>
      rcases hC with ⟨s, hF⟩
      simp [stepEscrowWorld, hF]

/-- Canonical `UniversalEnvHarness` instance for `MultiLocusEscrowWorld`. -/
def escrowEnvHarness : UniversalEnvHarness MultiLocusEscrowWorld EscrowTurn Unit EscrowRefusal where
  worldInv := EscrowWorldInv
  contractHolds := EscrowTurnContract
  refusalSound := EscrowRefusalSound
  step w t := match stepEscrowWorld w t with
    | .ok w' => .inl (w', ())
    | .error ref => .inr ref
  step_preserves_inv w t w' _ hInv hSt := by
    cases h : stepEscrowWorld w t with
    | ok w'' =>
      rw [h] at hSt; injection hSt with hp; injection hp with hw _; subst w''
      exact stepEscrowWorld_preserves_inv hInv h
    | error _ => rw [h] at hSt; cases hSt
  step_complete_on_contract w t _ hC := by
    obtain ⟨w', hw'⟩ := (escrow_skip_implies_contract_violation w t).2 hC
    exact ⟨w', (), by simp [hw']⟩
  step_refusal_witnesses_violation w t ref _ hR := by
    cases h : stepEscrowWorld w t with
    | ok _ => rw [h] at hR; cases hR
    | error r' =>
      rw [h] at hR; injection hR with hr; subst r'
      exact (escrow_skip_implies_contract_violation w t).1 ref h

/-! ## 5. MixT / Gallifrey 4-Level Consistency-as-Integrity Lattice & IFC Typing -/

/-- 4-level consistency-as-integrity lattice (`bluePure < blueSemidirect < amberEscrow < redQuorum`). -/
inductive ConsistencyGrade where
  | bluePure
  | blueSemidirect
  | amberEscrow
  | redQuorum
  deriving DecidableEq, Repr

def ConsistencyGrade.rank : ConsistencyGrade → Nat
  | .bluePure       => 0
  | .blueSemidirect => 1
  | .amberEscrow    => 2
  | .redQuorum      => 3

theorem ConsistencyGrade.rank_injective {a b : ConsistencyGrade} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

def ConsistencyGrade.le (a b : ConsistencyGrade) : Bool := decide (a.rank ≤ b.rank)
def ConsistencyGrade.lt (a b : ConsistencyGrade) : Bool := decide (a.rank < b.rank)

/-- Lattice meet (`min` integrity: combining a weak `blue*` read with a strong read taints the result). -/
def ConsistencyGrade.meet (a b : ConsistencyGrade) : ConsistencyGrade :=
  if a.le b then a else b

/-- Lattice join (`max` required consistency tier). -/
def ConsistencyGrade.join (a b : ConsistencyGrade) : ConsistencyGrade :=
  if a.le b then b else a

theorem ConsistencyGrade.strict_chain :
    ConsistencyGrade.bluePure.lt .blueSemidirect = true ∧
    ConsistencyGrade.blueSemidirect.lt .amberEscrow = true ∧
    ConsistencyGrade.amberEscrow.lt .redQuorum = true := by
  decide

theorem ConsistencyGrade.meet_comm (a b : ConsistencyGrade) : a.meet b = b.meet a := by
  cases a <;> cases b <;> decide

theorem ConsistencyGrade.meet_assoc (a b c : ConsistencyGrade) :
    (a.meet b).meet c = a.meet (b.meet c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem ConsistencyGrade.join_comm (a b : ConsistencyGrade) : a.join b = b.join a := by
  cases a <;> cases b <;> decide

theorem ConsistencyGrade.join_assoc (a b c : ConsistencyGrade) :
    (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Expressions inside a composite multi-consistency object method. -/
inductive IfcExpr where
  | const           (val : Int)
  | readField       (fieldId : Nat) (tier : ConsistencyGrade)
  | add             (lhs rhs : IfcExpr)
  | le              (lhs rhs : IfcExpr)
  | endorseViaFlush (inner : IfcExpr) (target : ConsistencyGrade)
  deriving DecidableEq, Repr

/-- Statements of a composite object method emitting consistency-graded shadow effects. -/
inductive IfcMethod where
  | skip
  | emitShadow (targetTier : ConsistencyGrade) (guard payload : IfcExpr)
  | seq        (fst snd : IfcMethod)
  | branch     (cond : IfcExpr) (thenBranch elseBranch : IfcMethod)
  deriving DecidableEq, Repr

inductive IfcRefusal where
  | unendorsedUpgrade (target : ConsistencyGrade)
  | weakGuardFlow     (guardGrade requiredTier : ConsistencyGrade)
  | weakPayloadFlow   (payloadGrade requiredTier : ConsistencyGrade)
  | implicitPcFlow    (pcGrade requiredTier : ConsistencyGrade)
  deriving DecidableEq, Repr

/-- Infer consistency-integrity grade of `e`, rejecting `.endorseViaFlush` unless `endorseAllowed`. -/
def inferExprGrade (endorseAllowed : Bool) : IfcExpr → Except IfcRefusal ConsistencyGrade
  | .const _ => .ok .redQuorum
  | .readField _ tier => .ok tier
  | .add l r => do
    let gl ← inferExprGrade endorseAllowed l
    let gr ← inferExprGrade endorseAllowed r
    .ok (gl.meet gr)
  | .le l r => do
    let gl ← inferExprGrade endorseAllowed l
    let gr ← inferExprGrade endorseAllowed r
    .ok (gl.meet gr)
  | .endorseViaFlush inner target =>
    if endorseAllowed then do
      let _ ← inferExprGrade endorseAllowed inner
      .ok target
    else .error (.unendorsedUpgrade target)

/-- **MixT / Gallifrey IFC Method Checker (`#tooth` mutation target)**:
    enforces both explicit guard/payload integrity (`targetTier ≤ exprGrade`) and implicit
    program-counter integrity (`targetTier ≤ pcGrade`) across conditional branches. -/
def checkMethodIfc (pcGrade : ConsistencyGrade) (endorseAllowed : Bool) :
    IfcMethod → Except IfcRefusal Unit
  | .skip => .ok ()
  | .emitShadow targetTier guard payload => do
    if !(targetTier.le pcGrade) then
      .error (.implicitPcFlow pcGrade targetTier)
    else
      let gGuard ← inferExprGrade endorseAllowed guard
      if !(targetTier.le gGuard) then
        .error (.weakGuardFlow gGuard targetTier)
      else
        let gPay ← inferExprGrade endorseAllowed payload
        if !(targetTier.le gPay) then
          .error (.weakPayloadFlow gPay targetTier)
        else .ok ()
  | .seq m₁ m₂ => do
    checkMethodIfc pcGrade endorseAllowed m₁
    checkMethodIfc pcGrade endorseAllowed m₂
  | .branch cond tBranch eBranch => do
    let gCond ← inferExprGrade endorseAllowed cond
    let pc' := pcGrade.meet gCond
    checkMethodIfc pc' endorseAllowed tBranch
    checkMethodIfc pc' endorseAllowed eBranch

/-- Multi-tier read environment mapping `(tier, fieldId)` to integer values. -/
abbrev MultiTierEnv := ConsistencyGrade → Nat → Int

def evalIfcExpr (env : MultiTierEnv) : IfcExpr → Int
  | .const v => v
  | .readField fid tier => env tier fid
  | .add l r => evalIfcExpr env l + evalIfcExpr env r
  | .le l r => if evalIfcExpr env l ≤ evalIfcExpr env r then 1 else 0
  | .endorseViaFlush inner _ => evalIfcExpr env inner

/-- Operational evaluation of `IfcMethod`, emitting `(tier, payload)` shadow effects when `guard ≠ 0`. -/
def evalIfcMethod (env : MultiTierEnv) : IfcMethod → List (ConsistencyGrade × Int)
  | .skip => []
  | .emitShadow tier guard payload =>
    if evalIfcExpr env guard != 0 then [(tier, evalIfcExpr env payload)] else []
  | .seq m₁ m₂ => evalIfcMethod env m₁ ++ evalIfcMethod env m₂
  | .branch cond tB eB =>
    if evalIfcExpr env cond != 0 then evalIfcMethod env tB else evalIfcMethod env eB

/-- Strong (`amberEscrow` or `redQuorum`) shadow effects emitted by a method. -/
def isStrongGrade (g : ConsistencyGrade) : Bool :=
  ConsistencyGrade.amberEscrow.le g

def filterStrongEffects (effs : List (ConsistencyGrade × Int)) : List (ConsistencyGrade × Int) :=
  effs.filter (fun p => isStrongGrade p.1)

private theorem filterStrongEffects_append (xs ys : List (ConsistencyGrade × Int)) :
    filterStrongEffects (xs ++ ys) = filterStrongEffects xs ++ filterStrongEffects ys := by
  simp [filterStrongEffects]

/-- Two environments agree on all strong (`amberEscrow` and `redQuorum`) state while differing
    arbitrarily on weak `bluePure` and `blueSemidirect` eventual/causal state. -/
def StrongEnvAgree (env₁ env₂ : MultiTierEnv) : Prop :=
  ∀ (tier : ConsistencyGrade) (fid : Nat),
    isStrongGrade tier = true → env₁ tier fid = env₂ tier fid

private theorem evalIfcExpr_strong_eq {env₁ env₂ : MultiTierEnv} (hAgree : StrongEnvAgree env₁ env₂) :
    ∀ {e : IfcExpr} {g : ConsistencyGrade},
      inferExprGrade false e = .ok g →
      isStrongGrade g = true →
      evalIfcExpr env₁ e = evalIfcExpr env₂ e
  | .const _, _, _, _ => rfl
  | .readField fid tier, g, hInf, hStr => by
    simp only [inferExprGrade, Except.ok.injEq] at hInf; subst g
    exact hAgree tier fid hStr
  | .add l r, g, hInf, hStr => by
    simp only [inferExprGrade, bind, Except.bind] at hInf
    cases hl : inferExprGrade false l <;> rw [hl] at hInf
    · cases hInf
    · rename_i gl
      dsimp only at hInf
      cases hr : inferExprGrade false r <;> rw [hr] at hInf
      · cases hInf
      · rename_i gr
        simp only [Except.ok.injEq] at hInf; subst g
        have hStrL : isStrongGrade gl = true := by
          cases gl <;> cases gr <;> first | decide | cases hStr
        have hStrR : isStrongGrade gr = true := by
          cases gl <;> cases gr <;> first | decide | cases hStr
        simp only [evalIfcExpr, evalIfcExpr_strong_eq hAgree hl hStrL,
          evalIfcExpr_strong_eq hAgree hr hStrR]
  | .le l r, g, hInf, hStr => by
    simp only [inferExprGrade, bind, Except.bind] at hInf
    cases hl : inferExprGrade false l <;> rw [hl] at hInf
    · cases hInf
    · rename_i gl
      dsimp only at hInf
      cases hr : inferExprGrade false r <;> rw [hr] at hInf
      · cases hInf
      · rename_i gr
        simp only [Except.ok.injEq] at hInf; subst g
        have hStrL : isStrongGrade gl = true := by
          cases gl <;> cases gr <;> first | decide | cases hStr
        have hStrR : isStrongGrade gr = true := by
          cases gl <;> cases gr <;> first | decide | cases hStr
        simp only [evalIfcExpr, evalIfcExpr_strong_eq hAgree hl hStrL,
          evalIfcExpr_strong_eq hAgree hr hStrR]
  | .endorseViaFlush _ _, _, hInf, _ => by
    simp [inferExprGrade] at hInf

private theorem checkMethodIfc_weak_pc_no_strong {env : MultiTierEnv}
    {m : IfcMethod} {pc : ConsistencyGrade}
    (hWeak : isStrongGrade pc = false)
    (hChk : checkMethodIfc pc false m = .ok ()) :
    filterStrongEffects (evalIfcMethod env m) = [] := by
  induction m generalizing pc with
  | skip => rfl
  | emitShadow tier guard payload =>
    simp only [checkMethodIfc] at hChk
    cases hle : tier.le pc <;> rw [hle] at hChk
    · simp at hChk
    · have hTierWeak : isStrongGrade tier = false := by
        cases tier <;> cases pc <;> simp [isStrongGrade, ConsistencyGrade.le, ConsistencyGrade.rank] at hWeak hle ⊢
      unfold evalIfcMethod filterStrongEffects
      split <;> simp [hTierWeak]
  | seq m₁ m₂ ih₁ ih₂ =>
    simp only [checkMethodIfc, bind, Except.bind] at hChk
    cases h1 : checkMethodIfc pc false m₁ <;> rw [h1] at hChk
    · cases hChk
    · dsimp only at hChk
      simp only [evalIfcMethod, filterStrongEffects_append]
      rw [ih₁ hWeak h1, ih₂ hWeak hChk]
      rfl
  | branch cond tB eB ihT ihE =>
    simp only [checkMethodIfc, bind, Except.bind] at hChk
    cases hc : inferExprGrade false cond <;> rw [hc] at hChk
    · cases hChk
    · rename_i gCond
      dsimp only at hChk
      have hWeak' : isStrongGrade (pc.meet gCond) = false := by
        cases pc <;> cases gCond <;> simp [isStrongGrade, ConsistencyGrade.meet, ConsistencyGrade.le, ConsistencyGrade.rank] at hWeak ⊢
      cases h1 : checkMethodIfc (pc.meet gCond) false tB <;> rw [h1] at hChk
      · cases hChk
      · dsimp only at hChk
        unfold evalIfcMethod
        split
        · exact ihT hWeak' h1
        · exact ihE hWeak' hChk

/-- **MixT / Gallifrey Semantic Strong Non-Interference (`ifc_unendorsed_strong_noninterference`)**:
    For ANY composite object method `m` accepted without endorsement (`checkMethodIfc pc false m = .ok ()`),
    weak `bluePure` and `blueSemidirect` reads CANNOT influence ANY `amberEscrow` or `redQuorum`
    shadow effect — neither through explicit guard/payload expressions nor through implicit
    conditional branches! -/
theorem ifc_unendorsed_strong_noninterference
    {m : IfcMethod} {pc : ConsistencyGrade} {env₁ env₂ : MultiTierEnv}
    (hAgree : StrongEnvAgree env₁ env₂)
    (hTyped : checkMethodIfc pc false m = .ok ()) :
    filterStrongEffects (evalIfcMethod env₁ m) =
      filterStrongEffects (evalIfcMethod env₂ m) := by
  induction m generalizing pc with
  | skip => rfl
  | emitShadow tier guard payload =>
    by_cases hStr : isStrongGrade tier = true
    · simp only [checkMethodIfc] at hTyped
      cases hpc : tier.le pc <;> rw [hpc] at hTyped
      · simp at hTyped
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTyped
        cases hg : inferExprGrade false guard <;> rw [hg] at hTyped
        · cases hTyped
        · rename_i gGuard
          dsimp only [bind, Except.bind] at hTyped
          cases hgle : tier.le gGuard <;> rw [hgle] at hTyped
          · simp at hTyped
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTyped
            cases hp : inferExprGrade false payload <;> rw [hp] at hTyped
            · cases hTyped
            · rename_i gPay
              dsimp only [bind, Except.bind] at hTyped
              cases hple : tier.le gPay <;> rw [hple] at hTyped
              · simp at hTyped
              · have hGuardStr : isStrongGrade gGuard = true := by
                  cases tier <;> cases gGuard <;> simp [isStrongGrade, ConsistencyGrade.le, ConsistencyGrade.rank] at hStr hgle ⊢
                have hPayStr : isStrongGrade gPay = true := by
                  cases tier <;> cases gPay <;> simp [isStrongGrade, ConsistencyGrade.le, ConsistencyGrade.rank] at hStr hple ⊢
                unfold evalIfcMethod
                rw [evalIfcExpr_strong_eq hAgree hg hGuardStr,
                    evalIfcExpr_strong_eq hAgree hp hPayStr]
    · have hWeak : isStrongGrade tier = false := Bool.eq_false_iff.mpr hStr
      unfold evalIfcMethod filterStrongEffects
      split <;> split <;> simp [hWeak]
  | seq m₁ m₂ ih₁ ih₂ =>
    simp only [checkMethodIfc, bind, Except.bind] at hTyped
    cases h1 : checkMethodIfc pc false m₁ <;> rw [h1] at hTyped
    · cases hTyped
    · dsimp only at hTyped
      simp only [evalIfcMethod, filterStrongEffects_append]
      rw [ih₁ h1, ih₂ hTyped]
  | branch cond tB eB ihT ihE =>
    simp only [checkMethodIfc, bind, Except.bind] at hTyped
    cases hc : inferExprGrade false cond <;> rw [hc] at hTyped
    · cases hTyped
    · rename_i gCond
      dsimp only at hTyped
      cases h1 : checkMethodIfc (pc.meet gCond) false tB <;> rw [h1] at hTyped
      · cases hTyped
      · dsimp only at hTyped
        by_cases hMeetStr : isStrongGrade (pc.meet gCond) = true
        · have hCondStr : isStrongGrade gCond = true := by
            cases pc <;> cases gCond <;> simp [isStrongGrade, ConsistencyGrade.meet, ConsistencyGrade.le, ConsistencyGrade.rank] at hMeetStr ⊢
          unfold evalIfcMethod
          rw [evalIfcExpr_strong_eq hAgree hc hCondStr]
          split
          · exact ihT h1
          · exact ihE hTyped
        · have hMeetWeak : isStrongGrade (pc.meet gCond) = false := Bool.eq_false_iff.mpr hMeetStr
          unfold evalIfcMethod
          have hL : filterStrongEffects
              (if evalIfcExpr env₁ cond != 0 then evalIfcMethod env₁ tB else evalIfcMethod env₁ eB) = [] := by
            split
            · exact checkMethodIfc_weak_pc_no_strong hMeetWeak h1
            · exact checkMethodIfc_weak_pc_no_strong hMeetWeak hTyped
          have hR : filterStrongEffects
              (if evalIfcExpr env₂ cond != 0 then evalIfcMethod env₂ tB else evalIfcMethod env₂ eB) = [] := by
            split
            · exact checkMethodIfc_weak_pc_no_strong hMeetWeak h1
            · exact checkMethodIfc_weak_pc_no_strong hMeetWeak hTyped
          rw [hL, hR]

/-- Weak (`bluePure` / `blueSemidirect`) reads into `amberEscrow` or `redQuorum` guards are refused
    unless explicitly endorsed via `endorseViaFlush` (`endorseAllowed = true`). -/
theorem weak_read_refused_in_strong_guard_unless_endorsed (fid : Nat) :
    checkMethodIfc .redQuorum false
      (.emitShadow .amberEscrow (.readField fid .blueSemidirect) (.const 1)) =
      .error (.weakGuardFlow .blueSemidirect .amberEscrow) ∧
    checkMethodIfc .redQuorum true
      (.emitShadow .amberEscrow
        (.endorseViaFlush (.readField fid .blueSemidirect) .amberEscrow) (.const 1)) =
      .ok () := by
  simp [checkMethodIfc, inferExprGrade, ConsistencyGrade.le, ConsistencyGrade.rank,
        bind, Except.bind]

/-! ## 6. Burckhardt GSP (`confirmed · pending`) Prefix Rebase, Permutation Convergence & Tombstone GC -/

/-- Local pending item in a replica's speculative GSP queue. -/
inductive GspItem where
  | data   (op : SignedDataOp)
  | revoke (rev : Revocation)
  deriving DecidableEq, Repr

/-- Apply a single `GspItem` (`data` or `revoke`) directly to a `SemidirectReplica`. -/
def applyGspStep (s : SemidirectReplica) : GspItem → SemidirectReplica
  | .data op => s.postData op
  | .revoke rev => s.postRevoke rev

/-- Domain-separated 256-bit hash chain advancing `confirmedRoot` across finalized GSP batches. -/
def hashGspItem (prevRoot : Digest256) : GspItem → Digest256
  | .data op => digest256 prevRoot (digest256 op.hdr.opId op.hdr.stamp.dagAnchor)
  | .revoke rev => digest256 prevRoot (digest256 rev.nul rev.stamp.dagAnchor)

def foldBatchRoot (prevRoot : Digest256) (batch : List GspItem) : Digest256 :=
  batch.foldl hashGspItem prevRoot

/-- **Exact Step Commutativity Across Data & Revocations (`applyGspStep_comm`)**:
    any two `GspItem`s (`.data`/`.data`, `.revoke`/`.revoke`, or mixed `.data`/`.revoke`) commute
    identically on `SemidirectReplica` (`=`). -/
private theorem postData_postRevoke_comm (op : SignedDataOp) (rev : Revocation)
    (s : SemidirectReplica) :
    (s.postData op).postRevoke rev = (s.postRevoke rev).postData op := by
  refine SemidirectReplica.ext rfl (fun q => ?_)
  unfold SemidirectReplica.postData SemidirectReplica.postRevoke SemidirectReplica.lookupOp
  dsimp only
  rw [lookup_applyRevokeSetToEntries,
      lookupOpEntry_insert op.hdr q _ _ s.opsSorted,
      lookupOpEntry_insert op.hdr q _ _ (pairwise_applyRevokeSetToEntries _ s.opsSorted),
      lookup_applyRevokeSetToEntries, lookup_applyRevokeSetToEntries]
  by_cases hq : q = op.hdr
  · rw [hq]
    simp only [beq_self_eq_true, ↓reduceIte, RevokeSet.hitsHeader_insert]
    cases lookupOpEntry op.hdr s.ops <;>
    cases op.annihilated <;>
    cases revokeHitsHeader rev op.hdr <;>
    cases s.revokes.hitsHeader op.hdr <;>
    simp [Option.map]
  · have hb : (q == op.hdr) = false := beq_eq_false_iff_ne.mpr hq
    simp [hb]

theorem applyGspStep_comm (x y : GspItem) (s : SemidirectReplica) :
    applyGspStep (applyGspStep s x) y = applyGspStep (applyGspStep s y) x := by
  cases x with
  | data op₁ =>
    cases y with
    | data op₂ =>
      refine SemidirectReplica.ext rfl (fun q => ?_)
      unfold applyGspStep SemidirectReplica.postData SemidirectReplica.lookupOp
      dsimp only
      rw [lookupOpEntry_insert op₂.hdr q _ _ (pairwise_insertOpEntry _ _ _ s.opsSorted),
          lookupOpEntry_insert op₁.hdr q _ _ (pairwise_insertOpEntry _ _ _ s.opsSorted),
          lookupOpEntry_insert op₁.hdr q _ _ s.opsSorted,
          lookupOpEntry_insert op₂.hdr q _ _ s.opsSorted]
      by_cases hq1 : q = op₁.hdr <;> by_cases hq2 : q = op₂.hdr
      · have hh : op₂.hdr = op₁.hdr := hq2.symm.trans hq1
        rw [hq1, hh]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [lookupOpEntry_insert op₁.hdr op₁.hdr _ _ s.opsSorted,
            lookupOpEntry_insert op₁.hdr op₁.hdr _ _ s.opsSorted]
        simp only [beq_self_eq_true, ↓reduceIte]
        cases lookupOpEntry op₁.hdr s.ops <;> simp [Bool.or_comm, Bool.or_left_comm]
      · have hb2 : (q == op₂.hdr) = false := beq_eq_false_iff_ne.mpr hq2
        have hb1 : (q == op₁.hdr) = true := beq_iff_eq.mpr hq1
        have hb12 : (op₁.hdr == op₂.hdr) = false := beq_eq_false_iff_ne.mpr (hq1 ▸ hq2)
        simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
        rw [lookupOpEntry_insert op₂.hdr op₁.hdr _ _ s.opsSorted]
        simp [hb12]
      · have hb1 : (q == op₁.hdr) = false := beq_eq_false_iff_ne.mpr hq1
        have hb2 : (q == op₂.hdr) = true := beq_iff_eq.mpr hq2
        have hb21 : (op₂.hdr == op₁.hdr) = false := beq_eq_false_iff_ne.mpr (hq2 ▸ hq1)
        simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
        rw [lookupOpEntry_insert op₁.hdr op₂.hdr _ _ s.opsSorted]
        simp [hb21]
      · have hb1 : (q == op₁.hdr) = false := beq_eq_false_iff_ne.mpr hq1
        have hb2 : (q == op₂.hdr) = false := beq_eq_false_iff_ne.mpr hq2
        simp [hb1, hb2]
    | revoke rev => exact postData_postRevoke_comm op₁ rev s
  | revoke rev₁ =>
    cases y with
    | data op₂ => exact (postData_postRevoke_comm op₂ rev₁ s).symm
    | revoke rev₂ =>
      have hRevComm : (s.revokes.insert rev₁).insert rev₂ = (s.revokes.insert rev₂).insert rev₁ :=
        RevokeSet.ext fun z => by simp [or_left_comm]
      refine SemidirectReplica.ext hRevComm (fun q => ?_)
      unfold applyGspStep SemidirectReplica.postRevoke SemidirectReplica.lookupOp
      dsimp only
      rw [lookup_applyRevokeSetToEntries, lookup_applyRevokeSetToEntries,
          lookup_applyRevokeSetToEntries, lookup_applyRevokeSetToEntries, hRevComm]
      simp only [RevokeSet.hitsHeader_insert]
      cases lookupOpEntry q s.ops <;>
      cases revokeHitsHeader rev₁ q <;>
      cases revokeHitsHeader rev₂ q <;>
      cases s.revokes.hitsHeader q <;>
      simp [Option.map]

/-- **Permutation-Invariant Batch Folding**: two replicas applying ANY permutation `batch₁ ~ batch₂`
    of concurrent `GspItem`s reach the exact same `SemidirectReplica` (`=`). -/
theorem foldl_applyGspStep_perm {batch₁ batch₂ : List GspItem}
    (hPerm : batch₁.Perm batch₂) :
    ∀ (s : SemidirectReplica), batch₁.foldl applyGspStep s = batch₂.foldl applyGspStep s := by
  induction hPerm with
  | nil => intro _; rfl
  | cons x _ ih => intro s; exact ih (applyGspStep s x)
  | swap x y _ =>
    intro s
    simp only [List.foldl_cons]
    rw [applyGspStep_comm y x s]
  | trans _ _ ih₁ ih₂ =>
    intro s
    exact (ih₁ s).trans (ih₂ s)

/-- Burckhardt GSP Replica State (`confirmed · pending`) with causal-stability tombstone compaction. -/
structure GspReplicaState where
  confirmedRoot       : Digest256
  stabilityWatermark  : CausalStamp
  confirmed           : SemidirectReplica
  activeTombstones    : RevokeSet
  compactedNullifiers : SortedNullifierSet
  pending             : List GspItem
  deriving DecidableEq, Repr

def GspReplicaState.init (root : Digest256) : GspReplicaState where
  confirmedRoot       := root
  stabilityWatermark  := CausalStamp.genesis
  confirmed           := SemidirectReplica.empty
  activeTombstones    := RevokeSet.empty
  compactedNullifiers := SortedNullifierSet.empty
  pending             := []

/-- Check whether a header is annihilated by either compacted finalized nullifiers or active tombstones. -/
def gspAnnihilatesHeader (compacted : SortedNullifierSet) (active : RevokeSet)
    (hdr : SignedOpHeader) : Bool :=
  hdr.nullifiers.data.toList.any (fun n => compacted.contains n) || active.hitsHeader hdr

/-- Fold speculative `pending` operations over `confirmed` to obtain the Read-My-Writes local view. -/
def evalGspComposite (g : GspReplicaState) : SemidirectReplica :=
  g.pending.foldl (fun acc item =>
    match item with
    | .data op =>
      let killed := op.annihilated || gspAnnihilatesHeader g.compactedNullifiers g.activeTombstones op.hdr
      acc.postData { op with annihilated := killed }
    | .revoke rev => acc.postRevoke rev) g.confirmed

/-- Post an offline local `SignedDataOp` onto `pending`. -/
def gspPostLocalData (g : GspReplicaState) (op : SignedDataOp) : GspReplicaState :=
  { g with pending := g.pending ++ [.data op] }

/-- **Read-My-Writes (`gsp_local_post_read_my_writes`)**: posting a live local operation unrevoked by
    known tombstones is immediately visible as live (`some false`) in `evalGspComposite` with zero round-trips. -/
theorem gsp_local_post_read_my_writes (g : GspReplicaState) (hdr : SignedOpHeader)
    (hNotCompacted : (hdr.nullifiers.data.toList.any (fun n => g.compactedNullifiers.contains n)) = false)
    (hNotActive : g.activeTombstones.hitsHeader hdr = false)
    (hNotRevInComposite : (evalGspComposite g).revokes.hitsHeader hdr = false)
    (hFresh : (evalGspComposite g).lookupOp hdr = none) :
    (evalGspComposite (gspPostLocalData g (SignedDataOp.mkLive hdr))).lookupOp hdr = some false := by
  have hStepEq :
      evalGspComposite (gspPostLocalData g (SignedDataOp.mkLive hdr)) =
        (evalGspComposite g).postData
          { hdr := hdr
            annihilated := false || gspAnnihilatesHeader g.compactedNullifiers g.activeTombstones hdr } := by
    unfold evalGspComposite gspPostLocalData
    rw [List.foldl_append]
    rfl
  rw [hStepEq]
  have hNoKill : gspAnnihilatesHeader g.compactedNullifiers g.activeTombstones hdr = false := by
    simp [gspAnnihilatesHeader, hNotCompacted, hNotActive]
  rw [hNoKill]
  unfold SemidirectReplica.lookupOp SemidirectReplica.postData
  dsimp only
  rw [lookupOpEntry_insert hdr hdr _ (evalGspComposite g).ops (evalGspComposite g).opsSorted]
  have hFresh' : lookupOpEntry hdr (evalGspComposite g).ops = none := hFresh
  simp [hFresh', hNotRevInComposite]

private def stepTombstoneGc (watermark : CausalStamp)
    (acc : SortedNullifierSet × RevokeSet) (rev : Revocation) : SortedNullifierSet × RevokeSet :=
  if causallyLe rev.stamp watermark then
    (acc.1.insert rev.nul, acc.2)
  else
    (acc.1, acc.2.insert rev)

/-- **Causal-Stability Tombstone GC (`#tooth` mutation target)**:
    moves finalized tombstones with `rev.stamp ≤c watermark` out of `activeTombstones` (dropping
    their causal vector clocks!) into the compact 32-byte `SortedNullifierSet`. -/
def compactFinalizedTombstones (watermark : CausalStamp) (compacted : SortedNullifierSet)
    (active : RevokeSet) : SortedNullifierSet × RevokeSet :=
  active.items.foldl (stepTombstoneGc watermark) (compacted, RevokeSet.empty)

private theorem compactFinalizedTombstones_fold_invariant (watermark : CausalStamp)
    (hdr : SignedOpHeader) (hPastWatermark : watermark ≺c hdr.stamp)
    (revs : List Revocation) (acc : SortedNullifierSet × RevokeSet) :
    gspAnnihilatesHeader (revs.foldl (stepTombstoneGc watermark) acc).1
        (revs.foldl (stepTombstoneGc watermark) acc).2 hdr =
      (gspAnnihilatesHeader acc.1 acc.2 hdr || revs.any (fun rev => revokeHitsHeader rev hdr)) := by
  induction revs generalizing acc with
  | nil => simp
  | cons rev tl ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih (stepTombstoneGc watermark acc rev)]
    unfold stepTombstoneGc
    cases hle : causallyLe rev.stamp watermark
    · simp only [Bool.false_eq_true, ↓reduceIte, ← Bool.or_assoc]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [gspAnnihilatesHeader, RevokeSet.hitsHeader_insert, Bool.or_eq_true]
      constructor
      · rintro (h1 | (h2 | h3))
        · exact .inl (.inl h1)
        · exact .inr h2
        · exact .inl (.inr h3)
      · rintro ((h1 | h3) | h2)
        · exact .inl h1
        · exact .inr (.inr h3)
        · exact .inr (.inl h2)
    · simp only [↓reduceIte, ← Bool.or_assoc]
      congr 1
      have hNotPrior : causallyLt hdr.stamp rev.stamp = false := by
        cases hlt : causallyLt hdr.stamp rev.stamp
        · rfl
        · exfalso
          have h1 : rev.stamp ≺c hdr.stamp := causallyLe_causallyLt_trans hle hPastWatermark
          exact causallyLt_asymm h1 hlt
      apply Bool.eq_iff_iff.mpr
      simp only [gspAnnihilatesHeader, revokeHitsHeader, hNotPrior, Bool.not_false, Bool.and_true,
        Bool.or_eq_true, List.any_eq_true, SortedNullifierSet.contains_eq_spec,
        SortedNullifierSet.mem_insert]
      constructor
      · rintro (⟨n, hn, rfl | hnc⟩ | ha)
        · exact .inr hn
        · exact .inl (.inl ⟨n, hn, hnc⟩)
        · exact .inl (.inr ha)
      · rintro ((⟨n, hn, hnc⟩ | ha) | hnRev)
        · exact .inl ⟨n, hn, .inr hnc⟩
        · exact .inr ha
        · exact .inl ⟨rev.nul, hnRev, .inl rfl⟩

/-- **Exact Soundness of Causal-Stability Tombstone GC (`compactFinalizedTombstones_exact`)**:
    for every unconfirmed or future operation `hdr` causally after `watermark` (`watermark ≺c hdr.stamp`),
    garbage-collecting finalized tombstones (`rev.stamp ≤c watermark`) into `SortedNullifierSet`
    produces the **exact same** annihilation verdict as retaining the full unbounded `RevokeSet`! -/
theorem compactFinalizedTombstones_exact (watermark : CausalStamp)
    (compacted : SortedNullifierSet) (active : RevokeSet) (hdr : SignedOpHeader)
    (hPastWatermark : watermark ≺c hdr.stamp) :
    let res := compactFinalizedTombstones watermark compacted active
    gspAnnihilatesHeader res.1 res.2 hdr = gspAnnihilatesHeader compacted active hdr := by
  dsimp only [compactFinalizedTombstones]
  rw [compactFinalizedTombstones_fold_invariant watermark hdr hPastWatermark active.items
        (compacted, RevokeSet.empty)]
  simp [gspAnnihilatesHeader, RevokeSet.hitsHeader, RevokeSet.empty]

private def mapBatchWithTombstones (compacted : SortedNullifierSet) (active : RevokeSet)
    (item : GspItem) : GspItem :=
  match item with
  | .data op =>
    let killed := op.annihilated || gspAnnihilatesHeader compacted active op.hdr
    GspItem.data { op with annihilated := killed }
  | .revoke rev => GspItem.revoke rev

private def extractDataOpId (item : GspItem) : Option Digest256 :=
  match item with
  | .data op => some op.hdr.opId
  | .revoke _ => none

private def rebasePendingItem (confirmedIds : List Digest256) (compacted : SortedNullifierSet)
    (active activeWithBatch : RevokeSet) (item : GspItem) : Option GspItem :=
  match item with
  | .data op =>
    if confirmedIds.contains op.hdr.opId then none
    else
      let killed := op.annihilated || gspAnnihilatesHeader compacted active op.hdr
      some (.data { op with annihilated := killed })
  | .revoke rev =>
    if activeWithBatch.items.contains rev then none else some (.revoke rev)

/-- Rebase a `GspReplicaState` upon receiving a newly finalized batch at `(newRoot, newWatermark)`. -/
def rebasePending (g : GspReplicaState) (newRoot : Digest256) (newWatermark : CausalStamp)
    (finalizedBatch : List GspItem) : GspReplicaState :=
  let preFiltered := finalizedBatch.map (mapBatchWithTombstones g.compactedNullifiers g.activeTombstones)
  let confirmed' := preFiltered.foldl applyGspStep g.confirmed
  let activeWithBatch := finalizedBatch.foldl (fun rAcc (item : GspItem) =>
    match item with
    | .data _ => rAcc
    | .revoke rev => rAcc.insert rev) g.activeTombstones
  let gcRes := compactFinalizedTombstones newWatermark g.compactedNullifiers activeWithBatch
  let confirmedIds := finalizedBatch.filterMap extractDataOpId
  let pending' := g.pending.filterMap (rebasePendingItem confirmedIds gcRes.1 gcRes.2 activeWithBatch)
  { confirmedRoot       := newRoot
    stabilityWatermark  := newWatermark
    confirmed           := confirmed'
    activeTombstones    := gcRes.2
    compactedNullifiers := gcRes.1
    pending             := pending' }

/-- Every local item in `pending` appears in `batch` (either by `opId` for data or `Revocation` membership). -/
def AllPendingConfirmedIn (pending batch : List GspItem) : Prop :=
  ∀ item ∈ pending,
    match item with
    | .data op => ∃ op' ∈ batch, op' = GspItem.data op ∨
        (∃ d, op' = GspItem.data d ∧ d.hdr.opId = op.hdr.opId)
    | .revoke rev => GspItem.revoke rev ∈ batch

private theorem filterMap_pending_drained (compacted : SortedNullifierSet) (active activeWithBatch : RevokeSet)
    (batch : List GspItem)
    (hRevCovered : ∀ rev, GspItem.revoke rev ∈ batch → rev ∈ activeWithBatch.items) :
    ∀ (pending : List GspItem),
      AllPendingConfirmedIn pending batch →
      pending.filterMap (rebasePendingItem (batch.filterMap extractDataOpId) compacted active activeWithBatch) = []
  | [], _ => rfl
  | .data op :: tl, hAll => by
    have hHead := hAll (.data op) List.mem_cons_self
    have hIdMem : op.hdr.opId ∈ batch.filterMap extractDataOpId := by
      rcases hHead with ⟨item, hMem, rfl | ⟨d, rfl, hid⟩⟩
      · exact List.mem_filterMap.mpr ⟨.data op, hMem, rfl⟩
      · exact List.mem_filterMap.mpr ⟨.data d, hMem, congrArg some hid⟩
    have hContains : (batch.filterMap extractDataOpId).contains op.hdr.opId = true :=
      List.contains_iff_mem.mpr hIdMem
    simp only [List.filterMap_cons, rebasePendingItem, hContains, ↓reduceIte]
    exact filterMap_pending_drained compacted active activeWithBatch batch hRevCovered tl
      (fun x hx => hAll x (List.mem_cons_of_mem _ hx))
  | .revoke rev :: tl, hAll => by
    have hHead := hAll (.revoke rev) List.mem_cons_self
    have hContains : activeWithBatch.items.contains rev = true :=
      List.contains_iff_mem.mpr (hRevCovered rev hHead)
    simp only [List.filterMap_cons, rebasePendingItem, hContains, ↓reduceIte]
    exact filterMap_pending_drained compacted active activeWithBatch batch hRevCovered tl
      (fun x hx => hAll x (List.mem_cons_of_mem _ hx))

private theorem mem_foldl_batch_revokes (batch : List GspItem) (rAcc : RevokeSet) (rev : Revocation)
    (hMem : GspItem.revoke rev ∈ batch) :
    rev ∈ (batch.foldl (fun acc (item : GspItem) =>
      match item with | .data _ => acc | .revoke r => acc.insert r) rAcc).items := by
  induction batch generalizing rAcc with
  | nil => cases hMem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hMem with rfl | htl
    · simp only [List.foldl_cons]
      clear ih
      have hMono : ∀ (xs : List GspItem) (acc : RevokeSet),
          rev ∈ acc.items →
          rev ∈ (xs.foldl (fun a (item : GspItem) =>
            match item with | .data _ => a | .revoke r => a.insert r) acc).items := by
        intro xs
        induction xs with
        | nil => intro _ h; exact h
        | cons x xtl ihx =>
          intro acc h
          cases x with
          | data _ => exact ihx acc h
          | revoke r' => exact ihx (acc.insert r') ((RevokeSet.mem_insert acc r' rev).mpr (.inr h))
      exact hMono tl (rAcc.insert rev) ((RevokeSet.mem_insert rAcc rev rev).mpr (.inl rfl))
    · cases hd <;> exact ih _ htl

/-- **GSP Quiescent Convergence Across Distinct Pending Queues & Permuted Arrival Orders (`gsp_rebase_quiescent_agreement`)**:
    Suppose Replica 1 and Replica 2 hold **distinct** unconfirmed local pending queues (`g₁.pending ≠ g₂.pending`)
    over a shared `confirmed` base, and receive concurrent operations in **permuted arrival orders**
    `batch₁ ~ batch₂` (`List.Perm batch₁ batch₂`) covering their respective pending sets.
    Then `rebasePending` drains both pending queues and converges both replicas to the **exact same**
    composite `SemidirectReplica` (`=`) with zero coordination! -/
theorem gsp_rebase_quiescent_agreement (g₁ g₂ : GspReplicaState)
    (newRoot : Digest256) (newWatermark : CausalStamp) (batch₁ batch₂ : List GspItem)
    (hBase : g₁.confirmed = g₂.confirmed)
    (hComp : g₁.compactedNullifiers = g₂.compactedNullifiers)
    (hAct  : g₁.activeTombstones = g₂.activeTombstones)
    (hPerm : batch₁.Perm batch₂)
    (hCov₁ : AllPendingConfirmedIn g₁.pending batch₁)
    (hCov₂ : AllPendingConfirmedIn g₂.pending batch₂) :
    (rebasePending g₁ newRoot newWatermark batch₁).pending = [] ∧
    (rebasePending g₂ newRoot newWatermark batch₂).pending = [] ∧
    evalGspComposite (rebasePending g₁ newRoot newWatermark batch₁) =
      evalGspComposite (rebasePending g₂ newRoot newWatermark batch₂) := by
  have hDrain₁ : (rebasePending g₁ newRoot newWatermark batch₁).pending = [] :=
    filterMap_pending_drained _ _ _ batch₁
      (fun rev hm => mem_foldl_batch_revokes batch₁ g₁.activeTombstones rev hm) g₁.pending hCov₁
  have hDrain₂ : (rebasePending g₂ newRoot newWatermark batch₂).pending = [] :=
    filterMap_pending_drained _ _ _ batch₂
      (fun rev hm => mem_foldl_batch_revokes batch₂ g₂.activeTombstones rev hm) g₂.pending hCov₂
  refine ⟨hDrain₁, hDrain₂, ?_⟩
  unfold evalGspComposite
  rw [hDrain₁, hDrain₂]
  dsimp only [List.foldl]
  unfold rebasePending
  dsimp only
  rw [hBase, hComp, hAct]
  exact foldl_applyGspStep_perm (hPerm.map _) g₂.confirmed

/-! ## 7. Coupled Multi-Turn `SS-GSP` World & End-to-End Cathedral Apex Theorem -/

/-- Escalated `Red` operation tagged by causal cone `coneId : UInt64`: guarded CAS `(coneId, expected, next)`. -/
structure EscalatedConeOp where
  coneId   : UInt64
  expected : Nat
  nextVal  : Nat
  deriving DecidableEq, Repr

def lookupConeVal (coneId : UInt64) (st : List (UInt64 × Nat)) : Nat :=
  (st.lookup coneId).getD 0

private def setConeVal (coneId : UInt64) (val : Nat) : List (UInt64 × Nat) → List (UInt64 × Nat)
  | [] => [(coneId, val)]
  | (c, v) :: rest => if c == coneId then (coneId, val) :: rest else (c, v) :: setConeVal coneId val rest

def stepConeStore (st : List (UInt64 × Nat)) (op : EscalatedConeOp) :
    Except (UInt64 × Nat × Nat) (List (UInt64 × Nat)) :=
  let cur := lookupConeVal op.coneId st
  if cur == op.expected then .ok (setConeVal op.coneId op.nextVal st)
  else .error (op.coneId, op.expected, cur)

/-- Unified `SS-GSP` world coupling `GspReplicaState` (`digest256`-chained roots), multi-locus
    `Amber` escrow slices, MixT IFC-admitted method audit log, and per-cone settled `Red` store. -/
structure SsGspWorld where
  gsp             : GspReplicaState
  escrow          : MultiLocusEscrowWorld
  coneStore       : List (UInt64 × Nat)
  admittedMethods : List IfcMethod
  rootChain       : List (Digest256 × Digest256)
  deriving DecidableEq, Repr

def initSsGspWorld (root : Digest256) (supply : Nat) : SsGspWorld where
  gsp             := GspReplicaState.init root
  escrow          := initEscrowWorld supply
  coneStore       := []
  admittedMethods := []
  rootChain       := []

/-- Coupled protocol refusals across MixT IFC checks and `Amber` escrow conservation bounds. -/
inductive SsGspRefusal where
  | ifcRejected    (reason : IfcRefusal)
  | escrowRejected (reason : EscrowRefusal)
  deriving DecidableEq, Repr

/-- Coupled multi-turn `SS-GSP` protocol transitions across `Blue`, IFC-gated `Amber`, `GSP` hash-chained
    rebase, and IFC-gated per-cone `Red` settlement. -/
inductive SsGspTurn where
  | bluePostData     (op : SignedDataOp)
  | blueMergeRemote  (remote : SemidirectReplica)
  | amberIfcEscrow   (guardMethod : IfcMethod) (t : EscrowTurn)
  | gspRebase        (watermark : CausalStamp) (batch : List GspItem)
  | redIfcSettleCone (guardMethod : IfcMethod) (ops : List EscalatedConeOp)
  deriving DecidableEq, Repr

/-- Coupled `SS-GSP` step: gates `Amber` and `Red` turns on `checkMethodIfc .redQuorum false` and
    binds every `gspRebase` root transition via `foldBatchRoot` (`digest256`). -/
def stepSsGspWorld (w : SsGspWorld) : SsGspTurn → Except SsGspRefusal SsGspWorld
  | .bluePostData op =>
    .ok { w with gsp := gspPostLocalData w.gsp op }
  | .blueMergeRemote remote =>
    .ok { w with gsp := { w.gsp with confirmed := semidirectMerge w.gsp.confirmed remote } }
  | .amberIfcEscrow guardMethod t =>
    match checkMethodIfc .redQuorum false guardMethod with
    | .error ifcErr => .error (.ifcRejected ifcErr)
    | .ok () =>
      match stepEscrowWorld w.escrow t with
      | .error escErr => .error (.escrowRejected escErr)
      | .ok esc' =>
        .ok { w with escrow := esc', admittedMethods := w.admittedMethods ++ [guardMethod] }
  | .gspRebase watermark batch =>
    let oldRoot := w.gsp.confirmedRoot
    let newRoot := foldBatchRoot oldRoot batch
    .ok { w with
          gsp := rebasePending w.gsp newRoot watermark batch
          rootChain := w.rootChain ++ [(oldRoot, newRoot)] }
  | .redIfcSettleCone guardMethod ops =>
    match checkMethodIfc .redQuorum false guardMethod with
    | .error ifcErr => .error (.ifcRejected ifcErr)
    | .ok () =>
      let settled := settleByCone EscalatedConeOp.coneId stepConeStore w.coneStore ops
      .ok { w with
            coneStore := settled.1
            admittedMethods := w.admittedMethods ++ [guardMethod] }

/-- Coupled world invariant across `Amber` escrow slices, MixT IFC typing, and 256-bit GSP root chains. -/
structure SsGspWorldInv (w : SsGspWorld) : Prop where
  escrow_inv    : EscrowWorldInv w.escrow
  methods_typed : ∀ m ∈ w.admittedMethods, checkMethodIfc .redQuorum false m = .ok ()
  roots_chained : ∀ link ∈ w.rootChain, ∃ batch, link.2 = foldBatchRoot link.1 batch

theorem initSsGspWorld_inv (root : Digest256) (supply : Nat) :
    SsGspWorldInv (initSsGspWorld root supply) where
  escrow_inv := initEscrowWorld_inv supply
  methods_typed := fun _ h => by cases h
  roots_chained := fun _ h => by cases h

/-- Multi-turn reachability trace over `SsGspWorld` propagating `stepSsGspWorld` from `w₀`. -/
inductive ValidSsGspTrace : SsGspWorld → List SsGspTurn → SsGspWorld → Prop where
  | nil {w : SsGspWorld} : ValidSsGspTrace w [] w
  | cons {w₁ w₂ w₃ : SsGspWorld} {t : SsGspTurn} {rest : List SsGspTurn} :
      stepSsGspWorld w₁ t = .ok w₂ →
      ValidSsGspTrace w₂ rest w₃ →
      ValidSsGspTrace w₁ (t :: rest) w₃

private theorem stepSsGspWorld_preserves_inv {w w' : SsGspWorld} {t : SsGspTurn}
    (hInv : SsGspWorldInv w) (hSt : stepSsGspWorld w t = .ok w') :
    SsGspWorldInv w' := by
  cases t with
  | bluePostData _ =>
    simp only [stepSsGspWorld, Except.ok.injEq] at hSt; subst w'
    exact ⟨hInv.escrow_inv, hInv.methods_typed, hInv.roots_chained⟩
  | blueMergeRemote _ =>
    simp only [stepSsGspWorld, Except.ok.injEq] at hSt; subst w'
    exact ⟨hInv.escrow_inv, hInv.methods_typed, hInv.roots_chained⟩
  | amberIfcEscrow gm et =>
    simp only [stepSsGspWorld] at hSt
    cases hIfc : checkMethodIfc .redQuorum false gm <;> rw [hIfc] at hSt
    · cases hSt
    · dsimp only at hSt
      cases hEsc : stepEscrowWorld w.escrow et <;> rw [hEsc] at hSt
      · cases hSt
      · simp only [Except.ok.injEq] at hSt; subst w'
        refine ⟨(stepEscrowWorld_preserves_inv hInv.escrow_inv hEsc).2, ?_, hInv.roots_chained⟩
        intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hInv.methods_typed m hm
        · simp at hm; subst m; exact hIfc
  | gspRebase wm batch =>
    simp only [stepSsGspWorld, Except.ok.injEq] at hSt; subst w'
    refine ⟨hInv.escrow_inv, hInv.methods_typed, ?_⟩
    intro link hlink
    rcases List.mem_append.mp hlink with hlink | hlink
    · exact hInv.roots_chained link hlink
    · simp at hlink; subst link
      exact ⟨batch, rfl⟩
  | redIfcSettleCone gm ops =>
    simp only [stepSsGspWorld] at hSt
    cases hIfc : checkMethodIfc .redQuorum false gm <;> rw [hIfc] at hSt
    · cases hSt
    · simp only [Except.ok.injEq] at hSt; subst w'
      refine ⟨hInv.escrow_inv, ?_, hInv.roots_chained⟩
      intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hInv.methods_typed m hm
      · simp at hm; subst m; exact hIfc

private theorem lookupConeVal_set_self (c : UInt64) (v : Nat) :
    ∀ (st : List (UInt64 × Nat)), lookupConeVal c (setConeVal c v st) = v
  | [] => by simp [setConeVal, lookupConeVal]
  | (k, _) :: tl => by
    unfold setConeVal
    by_cases hk : k = c
    · subst hk; simp [lookupConeVal]
    · have hb1 : (k == c) = false := beq_eq_false_iff_ne.mpr hk
      have hb2 : (c == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
      simp only [hb1, Bool.false_eq_true, ↓reduceIte, lookupConeVal, List.lookup, hb2]
      exact lookupConeVal_set_self c v tl

private theorem lookupConeVal_set_ne {c₁ c₂ : UInt64} (hne : c₂ ≠ c₁) (v : Nat) :
    ∀ (st : List (UInt64 × Nat)), lookupConeVal c₂ (setConeVal c₁ v st) = lookupConeVal c₂ st
  | [] => by simp [setConeVal, lookupConeVal, List.lookup, beq_eq_false_iff_ne.mpr hne]
  | (k, _) :: tl => by
    unfold setConeVal
    by_cases hk : k = c₁
    · subst hk; simp [lookupConeVal, List.lookup, beq_eq_false_iff_ne.mpr hne]
    · have hb : (k == c₁) = false := beq_eq_false_iff_ne.mpr hk
      simp only [hb, Bool.false_eq_true, ↓reduceIte, lookupConeVal, List.lookup]
      cases c₂ == k
      · exact lookupConeVal_set_ne hne v tl
      · rfl

/-- **End-to-End Multi-Turn Stratified Semidirect GSP Soundness (`apex_semidirect_gsp_multi_turn_sound`)**:
    Across ANY multi-turn `ValidSsGspTrace` from an invariant-satisfying `w₀` interleaving `Blue`
    semidirect merges, IFC-gated `Amber` offline escrow debits/credits, `digest256`-chained GSP
    rebases, and IFC-gated per-cone `Red` settlements:
    1. **Escrow Non-Negativity & Exact Conservation:** every slice and `globalBalanceInt` remain $\ge 0$
       and `unallocated + sumNat remaining = total_conserved`,
    2. **Semidirect Merge Commutativity & Associativity:** `semidirectMerge` commutes and associates
       identically on `w.gsp.confirmed`,
    3. **MixT Strong Non-Interference:** every admitted composite method in `w.admittedMethods`
       provably isolates `amberEscrow`/`redQuorum` effects from weak `blue*` state,
    4. **256-Bit Hash-Chained GSP Anchors:** every `(r₁, r₂) ∈ w.rootChain` is bound via `foldBatchRoot`,
    5. **Per-Cone Independent Non-Aborting Settlement:** clean cone `c₁` commits (`lookupConeVal` advances)
       even when a disjoint cone `c₂ ≠ c₁` conflicts! -/
theorem apex_semidirect_gsp_multi_turn_sound
    {w₀ w : SsGspWorld} {tr : List SsGspTurn}
    (hInv₀ : SsGspWorldInv w₀)
    (hTrace : ValidSsGspTrace w₀ tr w) :
    SsGspWorldInv w ∧
    (∀ s ∈ w.escrow.slices, 0 ≤ s.netRemainingInt) ∧
    0 ≤ globalBalanceInt w.escrow.pool w.escrow.slices ∧
    w.escrow.pool.unallocated + sumNat (w.escrow.slices.map EscrowSlice.remaining) =
      w.escrow.pool.total_conserved w.escrow.slices ∧
    (∀ r₁ r₂ : SemidirectReplica,
      semidirectMerge w.gsp.confirmed r₁ = semidirectMerge r₁ w.gsp.confirmed ∧
      semidirectMerge (semidirectMerge w.gsp.confirmed r₁) r₂ =
        semidirectMerge w.gsp.confirmed (semidirectMerge r₁ r₂)) ∧
    (∀ m ∈ w.admittedMethods, ∀ env₁ env₂ : MultiTierEnv,
      StrongEnvAgree env₁ env₂ →
      filterStrongEffects (evalIfcMethod env₁ m) = filterStrongEffects (evalIfcMethod env₂ m)) ∧
    (∀ link ∈ w.rootChain, ∃ batch, link.2 = foldBatchRoot link.1 batch) ∧
    (∀ c₁ c₂ : UInt64, c₁ ≠ c₂ →
      let ops : List EscalatedConeOp :=
        [⟨c₁, lookupConeVal c₁ w.coneStore, lookupConeVal c₁ w.coneStore + 1⟩,
         ⟨c₂, lookupConeVal c₂ w.coneStore + 99, 0⟩]
      let settled := settleByCone EscalatedConeOp.coneId stepConeStore w.coneStore ops
      lookupConeVal c₁ settled.1 = lookupConeVal c₁ w.coneStore + 1 ∧
      c₁ ∈ settled.2.1 ∧ settled.2.2 ≠ []) := by
  have hInv : SsGspWorldInv w := by
    induction hTrace with
    | nil => exact hInv₀
    | cons hSt _ ih => exact ih (stepSsGspWorld_preserves_inv hInv₀ hSt)
  have hEsc := multi_locus_escrow_nonneg_and_conserved (tr := []) hInv.escrow_inv rfl
  refine ⟨hInv, hEsc.2.1, hEsc.2.2.1, hEsc.2.2.2.1,
    fun r₁ r₂ => ⟨semidirectMerge_comm w.gsp.confirmed r₁,
                  semidirectMerge_assoc w.gsp.confirmed r₁ r₂⟩,
    fun m hm env₁ env₂ hAg =>
      ifc_unendorsed_strong_noninterference hAg (hInv.methods_typed m hm),
    hInv.roots_chained, ?_⟩
  intro c₁ c₂ hne
  let s₁ := setConeVal c₁ (lookupConeVal c₁ w.coneStore + 1) w.coneStore
  have hOk₁ : stepConeStore w.coneStore ⟨c₁, lookupConeVal c₁ w.coneStore, lookupConeVal c₁ w.coneStore + 1⟩ = .ok s₁ := by
    simp [stepConeStore, s₁]
  have hErr₂ : stepConeStore s₁ ⟨c₂, lookupConeVal c₂ w.coneStore + 99, 0⟩ =
      .error (c₂, lookupConeVal c₂ w.coneStore + 99, lookupConeVal c₂ w.coneStore) := by
    unfold stepConeStore
    dsimp only
    rw [lookupConeVal_set_ne (Ne.symm hne)]
    have hBad : (lookupConeVal c₂ w.coneStore == lookupConeVal c₂ w.coneStore + 99) = false := by
      apply beq_eq_false_iff_ne.mpr; omega
    simp [hBad]
  obtain ⟨hStEq, hMem1, hMem2⟩ := settleByCone_two_disjoint_first_commits
    EscalatedConeOp.coneId stepConeStore w.coneStore s₁
    ⟨c₁, lookupConeVal c₁ w.coneStore, lookupConeVal c₁ w.coneStore + 1⟩
    ⟨c₂, lookupConeVal c₂ w.coneStore + 99, 0⟩
    (c₂, lookupConeVal c₂ w.coneStore + 99, lookupConeVal c₂ w.coneStore)
    hne hOk₁ hErr₂
  refine ⟨?_, hMem1, fun hNil => ?_⟩
  · rw [hStEq]; exact lookupConeVal_set_self c₁ _ w.coneStore
  · rw [hNil] at hMem2; cases hMem2

/-- Constructive multi-step `ValidSsGspTrace` runner. -/
def runSsGspTurns : SsGspWorld → List SsGspTurn → Except SsGspRefusal SsGspWorld
  | w, [] => .ok w
  | w, t :: rest => do
    let w' ← stepSsGspWorld w t
    runSsGspTurns w' rest

theorem runSsGspTurns_validTrace {w₀ wF : SsGspWorld} {ts : List SsGspTurn}
    (hRun : runSsGspTurns w₀ ts = .ok wF) :
    ValidSsGspTrace w₀ ts wF := by
  induction ts generalizing w₀ with
  | nil =>
    simp only [runSsGspTurns, Except.ok.injEq] at hRun; subst wF
    exact .nil
  | cons t rest ih =>
    simp only [runSsGspTurns, bind, Except.bind] at hRun
    cases h1 : stepSsGspWorld w₀ t <;> rw [h1] at hRun
    · cases hRun
    · exact .cons h1 (ih hRun)

/-- **Multi-Replica Joint Inhabitedness Witness (`ssGsp_multi_turn_inhabited`)**:
    symbolically witnesses an 8-turn `ValidSsGspTrace` from `initSsGspWorld root 100` for EVERY
    `root : Digest256`, exercising two concurrent replicas (`1 ≠ 2`), IFC-checked offline debits
    AND credits, `Blue` data posting, `digest256`-chained GSP rebase, and per-cone `Red` settlement! -/
theorem ssGsp_multi_turn_inhabited (root : Digest256) :
    let w₀ := initSsGspWorld root 100
    let hdr : SignedOpHeader :=
      { opId := 0x01#256
        actor := 1
        stamp := ⟨[(1, 1)], root⟩
        nullifiers := SortedNullifierSet.empty.insert 0xCAFE#256
        payload := .addDelta 10 0 7 }
    let amberGuard : IfcMethod :=
      .emitShadow .amberEscrow (.readField 0 .amberEscrow) (.const 1)
    let redGuard : IfcMethod :=
      .emitShadow .redQuorum (.readField 0 .redQuorum) (.const 1)
    let script : List SsGspTurn :=
      [ .amberIfcEscrow amberGuard (.grantSlice 1 101 40)
      , .amberIfcEscrow amberGuard (.grantSlice 2 102 30)
      , .amberIfcEscrow amberGuard (.localDebit 1 25)
      , .amberIfcEscrow amberGuard (.localCredit 1 10)
      , .amberIfcEscrow amberGuard (.localDebit 2 15)
      , .bluePostData (SignedDataOp.mkLive hdr)
      , .gspRebase ⟨[(1, 1)], root⟩ [.data (SignedDataOp.mkLive hdr)]
      , .redIfcSettleCone redGuard [⟨10, 0, 42⟩, ⟨20, 99, 1⟩] ]
    ∃ wF,
      runSsGspTurns w₀ script = .ok wF ∧
      ValidSsGspTrace w₀ script wF ∧
      wF.escrow.pool.unallocated = 30 ∧
      wF.gsp.pending = [] ∧
      wF.rootChain.length = 1 ∧
      lookupConeVal 10 wF.coneStore = 42 ∧
      lookupConeVal 20 wF.coneStore = 0 := by
  intro w₀ hdr amberGuard redGuard script
  have hCone :
      (settleByCone EscalatedConeOp.coneId stepConeStore ([] : List (UInt64 × Nat))
        [⟨10, 0, 42⟩, ⟨20, 99, 1⟩]).1 = [(10, 42)] :=
    (settleByCone_two_disjoint_first_commits EscalatedConeOp.coneId stepConeStore
      [] [(10, 42)] ⟨10, 0, 42⟩ ⟨20, 99, 1⟩ (20, 99, 0)
      (by decide) rfl rfl).1
  let gspAfterPost := gspPostLocalData (GspReplicaState.init root) (SignedDataOp.mkLive hdr)
  let newRoot := foldBatchRoot root [.data (SignedDataOp.mkLive hdr)]
  let gspFinal := rebasePending gspAfterPost newRoot ⟨[(1, 1)], root⟩ [.data (SignedDataOp.mkLive hdr)]
  have hPendNil : gspFinal.pending = [] := by
    simp [gspFinal, gspAfterPost, rebasePending, gspPostLocalData, GspReplicaState.init,
          extractDataOpId, rebasePendingItem]
  let escF : MultiLocusEscrowWorld :=
    { pool := { initialSupply := 100, unallocated := 30 }
      slices := [ ⟨1, 101, 40, 10, 25, 0⟩, ⟨2, 102, 30, 0, 15, 0⟩ ] }
  let wF : SsGspWorld :=
    { gsp := gspFinal
      escrow := escF
      coneStore := [(10, 42)]
      admittedMethods := [amberGuard, amberGuard, amberGuard, amberGuard, amberGuard, redGuard]
      rootChain := [(root, newRoot)] }
  have hRun : runSsGspTurns w₀ script = .ok wF := by
    have hA : checkMethodIfc .redQuorum false amberGuard = .ok () := rfl
    have hR : checkMethodIfc .redQuorum false redGuard = .ok () := rfl
    have h1 : stepEscrowWorld (initEscrowWorld 100) (.grantSlice 1 101 40) =
        .ok ⟨⟨100, 60⟩, [⟨1, 101, 40, 0, 0, 0⟩]⟩ := rfl
    have h2 : stepEscrowWorld ⟨⟨100, 60⟩, [⟨1, 101, 40, 0, 0, 0⟩]⟩ (.grantSlice 2 102 30) =
        .ok ⟨⟨100, 30⟩, [⟨1, 101, 40, 0, 0, 0⟩, ⟨2, 102, 30, 0, 0, 0⟩]⟩ := rfl
    have h3 : stepEscrowWorld ⟨⟨100, 30⟩, [⟨1, 101, 40, 0, 0, 0⟩, ⟨2, 102, 30, 0, 0, 0⟩]⟩ (.localDebit 1 25) =
        .ok ⟨⟨100, 30⟩, [⟨1, 101, 40, 0, 25, 0⟩, ⟨2, 102, 30, 0, 0, 0⟩]⟩ := rfl
    have h4 : stepEscrowWorld ⟨⟨100, 30⟩, [⟨1, 101, 40, 0, 25, 0⟩, ⟨2, 102, 30, 0, 0, 0⟩]⟩ (.localCredit 1 10) =
        .ok ⟨⟨100, 30⟩, [⟨1, 101, 40, 10, 25, 0⟩, ⟨2, 102, 30, 0, 0, 0⟩]⟩ := rfl
    have h5 : stepEscrowWorld ⟨⟨100, 30⟩, [⟨1, 101, 40, 10, 25, 0⟩, ⟨2, 102, 30, 0, 0, 0⟩]⟩ (.localDebit 2 15) =
        .ok escF := rfl
    simp only [w₀, script, wF, gspFinal, gspAfterPost, newRoot, initSsGspWorld,
      runSsGspTurns, stepSsGspWorld, bind, Except.bind,
      hA, hR, h1, h2, h3, h4, h5, hCone]
    rfl
  exact ⟨wF, hRun, runSsGspTurns_validTrace hRun, rfl, hPendNil, rfl, rfl, rfl⟩

end Obend.Vault.SemidirectGsp

end
