module
/-
# Obend.Crypto.ThresholdMpcUcGames — Finite `KeyedLazyRO`, Pad-Space Bijections & Canetti UC Signatures

Establishes the 0-axiom game-hopping, secret-sharing simulation, and Universal Composability (UC)
foundations for threshold post-quantum hash-based signatures:

1. **Finite Query-Bounded `KeyedLazyRO` Birthday & Hiding Floors (`§1`)**:
   - Adaptive `Q`-query `OracleComp` decision trees evaluated before oracle sampling.
   - Slice reprogramming invariance (`condProb_pin_untouched`): reprogramming an unqueried point
     leaves every branch and acceptance count identically unchanged.
   - Unified leaf + internal-node domain (`Sum LeafBlock (Digest32 × Digest32)`) closing leaf
     binding and Merkle path walking under a single query-bounded birthday bound `(Q^2 + 1) / |Cod|`.
   - Two-world keyed-ROM blinding/PRF hiding floor (`hidingAdv_le`) proved at **exact deployed
     cardinalities** (`BitVec 256` = `2^256` and `Goldilocks^4` = `goldilocksPrime^4`, explicitly
     proving `deployedCardGoldilocks4 ≠ deployedCardBitVec256`), paired with all three non-vacuity
     poles: full-table reader breaks small-`Q` bound, 1-query guesser achieves `> 0` within bound,
     and 0-query hardcoder achieves exact advantage `0`.
   - Transparent per-adversary `RomFaithfulInstantiation` definition (zero axioms) paired with
     `not_universal_romFaithful` refuting the false `∀ A` quantifier via a 0-query baked adversary.
2. **Polymorphic Shamir Pad-Space Bijection & Collusion Threshold Teeth (`§2`)**:
   - Constructive Lagrange-vanishing polynomial `vanishCorruptUnit0` over any `[LawfulCommRing R]`
     satisfying `L_C(0) = 1`, `deg(L_C) ≤ |C| ≤ t - 1`, and `L_C(x_c) = 0` at every `x_c ∈ C`,
     instantiated for both `Goldilocks` and `TowerElem k` (`BinaryTower256`).
   - Bijection `shamir_rebalanceEquiv` & `pad_bijection_masked_openings_uniform` mapping real
     masked Beaver/Power-7 openings onto secret-independent openings while holding all `|C| ≤ t - 1`
     corrupt shares identically fixed, plus strict characteristic-2 involution `shamir_tower_rebalance_involutive`.
   - Negative teeth: `full_collusion_breaks_hiding` (`|C| = t` reconstructs the secret) and
     `unpadded_open_refutes_hiding` (omitting the pad leaks the wire value).
3. **Canetti UC Signature Functionality `idealSig` (`§3`)**:
   - Exact equivalence `ucRealizes_iff_eufCma` between UC realization of `idealSig` and EUF-CMA,
     explicit `S`-session hybrid telescope `multi_session_uc_realizes`, and `uc_composition_theorem`.
-/
public import Obend.Crypto.BinaryTower256
public import Obend.Crypto.Poseidon2Goldilocks
public import Obend.Judge.Computational
import all Obend.Crypto.Sumcheck

public section
namespace Obend.Crypto.ThresholdMpcUcGames

open Obend.Apps.ZkNtt
open Obend.Crypto
open Obend.Crypto.BinaryTower256
open Obend.Digest.HashBytes
open Obend.Judge.Computational

set_option autoImplicit false

/-! ## 1. Finite Counting, `OracleComp` Decision Trees & `KeyedLazyRO` Bounds -/

/-- Exact deployed cardinality of 256-bit byte/bitvec digests (`2 ^ 256`). -/
@[expose] def deployedCardBitVec256 : Nat := 2 ^ 256

/-- Exact deployed cardinality of 4-limb Goldilocks capacity digests (`goldilocksPrime ^ 4`). -/
@[expose] def deployedCardGoldilocks4 : Nat := goldilocksPrime ^ 4

/-- Deployed `Goldilocks^4` cardinality is strictly between `2^255` and `2^256` (never equal to `2^256`). -/
theorem deployedCardGoldilocks4_ne_bitVec256 :
    deployedCardGoldilocks4 ≠ deployedCardBitVec256 ∧
    2 ^ 255 < deployedCardGoldilocks4 ∧
    deployedCardGoldilocks4 < deployedCardBitVec256 := by
  unfold deployedCardGoldilocks4 deployedCardBitVec256
  decide

/-- Pure mathematical finite sum `∑_{i < n} f(i)` for counting arguments without runtime enumeration. -/
def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + finSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem finSum_const : ∀ (n c : Nat), finSum n (fun _ => c) = n * c
  | 0, c => by simp [finSum]
  | n + 1, c => by
    simp only [finSum, finSum_const n c, Nat.succ_mul]
    omega

theorem finSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [finSum]
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hRest := ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

theorem finSum_add {n : Nat} (f g : Fin n → Nat) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum, ih]
    omega

theorem finSum_eq_indicator : ∀ (n : Nat) (a : Fin n),
    finSum n (fun i => if i = a then 1 else 0) = 1
  | 0, a => Fin.elim0 a
  | n + 1, ⟨0, _⟩ => by
    simp only [finSum, ↓reduceIte]
    have hZero : finSum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) =
        finSum n (fun _ => 0) := by
      apply finSum_congr
      intro i
      simp
    rw [hZero, finSum_const]
    omega
  | n + 1, ⟨k + 1, hk⟩ => by
    simp only [finSum]
    have h0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp at hv
    simp only [h0, ↓reduceIte, Nat.zero_add]
    have hShift :
        finSum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ then 1 else 0) =
        finSum n (fun i => if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then 1 else 0) := by
      apply finSum_congr
      intro i
      by_cases hik : i.1 = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        simp [h2]
      · have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := by
          intro heq
          exact hik (congrArg Fin.val heq)
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ := by
          intro heq
          have hv : i.1 + 1 = k + 1 := congrArg Fin.val heq
          exact hik (Nat.succ.inj hv)
        rw [ite_eq_right_iff.mpr (fun h => False.elim (h1 h)),
            ite_eq_right_iff.mpr (fun h => False.elim (h2 h))]
    rw [hShift]
    exact finSum_eq_indicator n ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Fundamental finite union bound: at most `S.length` elements of `Fin n` belong to `S`. -/
theorem finSum_mem_list_le (n : Nat) : ∀ (S : List (Fin n)),
    finSum n (fun i => if i ∈ S then 1 else 0) ≤ S.length
  | [] => by
    have h0 : finSum n (fun i => if i ∈ ([] : List (Fin n)) then 1 else 0) = finSum n (fun _ => 0) :=
      finSum_congr (fun _ => rfl)
    rw [h0, finSum_const]
    omega
  | a :: S => by
    have hPoint : ∀ i : Fin n,
        (if i ∈ a :: S then 1 else 0) ≤ (if i = a then 1 else 0) + (if i ∈ S then 1 else 0) := by
      intro i
      by_cases hia : i = a
      · subst hia; simp
      · by_cases his : i ∈ S <;> simp [hia, his]
    have hLe := finSum_le_finSum hPoint
    rw [finSum_add, finSum_eq_indicator] at hLe
    have ih := finSum_mem_list_le n S
    simp only [List.length_cons]
    omega

/-- Absolute difference `|a - b|` on natural numbers. -/
def natAbsDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

theorem natAbsDiff_triangle (a b c : Nat) :
    natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff
  split <;> split <;> split <;> omega

private theorem natAbsDiff_step (p0 q0 sp sq sb : Nat)
    (hp0 : p0 ≤ 1) (hq0 : q0 ≤ 1) (hih : natAbsDiff sp sq ≤ sb) :
    natAbsDiff (p0 + sp) (q0 + sq) ≤ 1 + sb := by
  unfold natAbsDiff at hih ⊢
  split at hih <;> split <;> omega

private theorem natAbsDiff_same_add (v sp sq : Nat) :
    natAbsDiff (v + sp) (v + sq) = natAbsDiff sp sq := by
  unfold natAbsDiff
  split <;> split <;> omega

theorem finSum_indicator_diff_le {n : Nat} (p q : Fin n → Bool) (bad : Fin n → Bool)
    (hAgree : ∀ i : Fin n, bad i = false → p i = q i) :
    natAbsDiff (finSum n (fun i => if p i then 1 else 0))
               (finSum n (fun i => if q i then 1 else 0)) ≤
      finSum n (fun i => if bad i then 1 else 0) := by
  induction n with
  | zero => simp [finSum, natAbsDiff]
  | succ n ih =>
    simp only [finSum]
    let p' : Fin n → Bool := fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let q' : Fin n → Bool := fun i => q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let b' : Fin n → Bool := fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih' := ih p' q' b' (fun i hi => hAgree ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hi)
    cases hb0 : bad ⟨0, Nat.zero_lt_succ n⟩
    · have hpq0 := hAgree ⟨0, Nat.zero_lt_succ n⟩ hb0
      rw [hpq0]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, natAbsDiff_same_add]
      exact ih'
    · simp only [↓reduceIte]
      exact natAbsDiff_step _ _ _ _ _
        (by split <;> omega) (by split <;> omega) ih'

/-- Adaptive `Q`-query decision tree interacting with an oracle `Dom → Cod`. -/
inductive OracleComp (Dom Cod α : Type) where
  | pure (ret : α)
  | query (q : Dom) (next : Cod → OracleComp Dom Cod α)

/-- Deterministic evaluation of an `OracleComp` decision tree against a fixed oracle `O`. -/
@[expose] def evalOracleComp {Dom Cod α : Type} (O : Dom → Cod) : OracleComp Dom Cod α → α
  | .pure ret => ret
  | .query q next => evalOracleComp O (next (O q))

/-- Exact sequence of oracle queries issued along the execution path against `O`. -/
def queryLog {Dom Cod α : Type} (O : Dom → Cod) : OracleComp Dom Cod α → List Dom
  | .pure _ => []
  | .query q next => q :: queryLog O (next (O q))

/-- Syntactic worst-case query budget bound across all oracle response branches. -/
def QueryBounded {Dom Cod α : Type} : Nat → OracleComp Dom Cod α → Prop
  | _, .pure _ => True
  | 0, .query _ _ => False
  | Q + 1, .query _ next => ∀ y : Cod, QueryBounded Q (next y)

theorem queryLog_length_le {Dom Cod α : Type} (O : Dom → Cod) :
    ∀ {Q : Nat} {prog : OracleComp Dom Cod α}, QueryBounded Q prog → (queryLog O prog).length ≤ Q
  | _, .pure _, _ => Nat.zero_le _
  | 0, .query _ _, h => False.elim h
  | Q + 1, .query q next, h => by
    simp only [queryLog, List.length_cons]
    have ih := queryLog_length_le O (h (O q))
    omega

/-- Reprogram oracle `O` at a single domain point `x₀` to return `v`. -/
def pinOracle {Dom Cod : Type} [DecidableEq Dom] (O : Dom → Cod) (x₀ : Dom) (v : Cod) : Dom → Cod :=
  fun x => if x = x₀ then v else O x

/-- Pointwise untouched invariance: reprogramming `O` at `x₀ ∉ queryLog O prog` preserves both
    the final output and the entire query log. -/
theorem evalOracleComp_pin_untouched {Dom Cod α : Type} [DecidableEq Dom]
    (O : Dom → Cod) (x₀ : Dom) (v : Cod) :
    ∀ (prog : OracleComp Dom Cod α), x₀ ∉ queryLog O prog →
      evalOracleComp (pinOracle O x₀ v) prog = evalOracleComp O prog ∧
      queryLog (pinOracle O x₀ v) prog = queryLog O prog
  | .pure _, _ => ⟨rfl, rfl⟩
  | .query q next, hNotMem => by
    simp only [queryLog, List.mem_cons, not_or] at hNotMem
    have hqNe : q ≠ x₀ := fun hEq => hNotMem.1 hEq.symm
    have hPinQ : pinOracle O x₀ v q = O q := by simp [pinOracle, hqNe]
    simp only [evalOracleComp, queryLog, hPinQ]
    obtain ⟨hEval, hLog⟩ := evalOracleComp_pin_untouched O x₀ v (next (O q)) hNotMem.2
    exact ⟨hEval, congrArg (q :: ·) hLog⟩

/-- **Slice Reprogramming Lemma (`condProb_pin_untouched`)**:
    Across all `C` uniformly sampled values at an unqueried coordinate `x₀ ∉ queryLog O prog`,
    every reprogrammed slice accepts with the exact indicator of `O` (`C * indicator`), and
    guessing `O(x₀)` without querying `x₀` succeeds on at most `1` of the `C` slices! -/
theorem condProb_pin_untouched {Dom Cod α : Type} [DecidableEq Dom]
    (C : Nat) (decodeCod : Fin C → Cod)
    (O : Dom → Cod) (x₀ : Dom) (prog : OracleComp Dom Cod α) (accept : α → Bool)
    (guessProg : OracleComp Dom Cod (Fin C))
    (hUntouched : x₀ ∉ queryLog O prog)
    (hUntouchedGuess : x₀ ∉ queryLog O guessProg) :
    finSum C (fun c => if accept (evalOracleComp (pinOracle O x₀ (decodeCod c)) prog) then 1 else 0) =
      C * (if accept (evalOracleComp O prog) then 1 else 0) ∧
    finSum C (fun c => if evalOracleComp (pinOracle O x₀ (decodeCod c)) guessProg = c then 1 else 0) ≤
      (if 0 < C then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · have hCongr :
        finSum C (fun c => if accept (evalOracleComp (pinOracle O x₀ (decodeCod c)) prog) then 1 else 0) =
        finSum C (fun _ => if accept (evalOracleComp O prog) then 1 else 0) := by
      apply finSum_congr
      intro c
      rw [(evalOracleComp_pin_untouched O x₀ (decodeCod c) prog hUntouched).1]
    rw [hCongr, finSum_const]
  · cases C with
    | zero => simp [finSum]
    | succ n =>
      have hCongr :
          finSum (n + 1) (fun c => if evalOracleComp (pinOracle O x₀ (decodeCod c)) guessProg = c then 1 else 0) =
          finSum (n + 1) (fun c => if c = evalOracleComp O guessProg then 1 else 0) := by
        apply finSum_congr
        intro c
        rw [(evalOracleComp_pin_untouched O x₀ (decodeCod c) guessProg hUntouchedGuess).1]
        by_cases hcg : evalOracleComp O guessProg = c
        · rw [hcg]
        · have hgc : c ≠ evalOracleComp O guessProg := fun h => hcg h.symm
          rw [ite_eq_right_iff.mpr (fun h => False.elim (hcg h)),
              ite_eq_right_iff.mpr (fun h => False.elim (hgc h))]
      rw [hCongr, finSum_eq_indicator]
      simp

/-- Unified domain separating leaf absorbs (`Sum.inl`) from binary Merkle parent absorbs (`Sum.inr`). -/
abbrev UnifiedTreeDom (LeafBlock Digest32 : Type) := Sum LeafBlock (Digest32 × Digest32)

/-- Leaf-to-root path verification query count: 2 leaf absorbs + `2 * depth` sibling node absorbs. -/
def merkleWalkQueries (depth : Nat) : Nat := 2 + 2 * depth

def stepCollisionHits (C : Nat) (prevDigests : List (Fin C)) : Nat :=
  finSum C (fun y => if y ∈ prevDigests then 1 else 0)

def cumulativeBirthdayBound : Nat → Nat
  | 0 => 1
  | q + 1 => cumulativeBirthdayBound q + q

theorem cumulativeBirthdayBound_le_sq_succ : ∀ (Q : Nat),
    cumulativeBirthdayBound Q ≤ Q * Q + 1
  | 0 => by simp [cumulativeBirthdayBound]
  | q + 1 => by
    simp only [cumulativeBirthdayBound]
    have ih := cumulativeBirthdayBound_le_sq_succ q
    have hExpand : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega

private theorem finSum_stepHits_le_sq_succ (C : Nat) :
    ∀ (Q : Nat) (stepHistory : (i : Nat) → i < Q → List (Fin C)),
      (∀ i (hi : i < Q), (stepHistory i hi).length ≤ i) →
      1 + finSum Q (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)) ≤ Q * Q + 1
  | 0, _, _ => by simp [finSum]
  | q + 1, stepHistory, hHistLen => by
    have hPt : ∀ idx : Fin (q + 1),
        stepCollisionHits C (stepHistory idx.val idx.isLt) ≤ q := fun idx =>
      Nat.le_trans (Nat.le_trans (finSum_mem_list_le C _) (hHistLen idx.val idx.isLt))
        (Nat.le_of_lt_succ idx.isLt)
    have hSumLe : finSum (q + 1) (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)) ≤
        (q + 1) * q := by
      rw [← finSum_const (q + 1) q]
      exact finSum_le_finSum hPt
    have hMulLe : (q + 1) * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul_left (q + 1) (Nat.le_succ q)
    omega

/-- **Unified `LeafBlock ⊕ (Digest32 × Digest32)` Tree Birthday Floor (`unifiedTreeGame_birthday_le`)**:
    In the unified domain-separated lazy RO game (`Sum.inl` leaf absorbs, `Sum.inr` Merkle parent
    nodes), summing collision hit counts `stepCollisionHits` across all `Q` fresh steps (covering
    `2 + 2 * depth ≤ Q` leaf+Merkle path walks) plus 1 forgery guess is bounded by `Q^2 + 1` over `C`! -/
theorem unifiedTreeGame_birthday_le {LeafBlock Digest32 : Type}
    (C Q depth : Nat) (hWalk : merkleWalkQueries depth ≤ Q)
    (stepHistory : (i : Nat) → i < Q → List (Fin C))
    (hHistLen : ∀ i (hi : i < Q), (stepHistory i hi).length ≤ i)
    (leafA : LeafBlock) (nodeB : Digest32 × Digest32) :
    (Sum.inl leafA : UnifiedTreeDom LeafBlock Digest32) ≠ Sum.inr nodeB ∧
    ratLe (1 + finSum Q (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)), C)
          (Q * Q + 1, C) ∧
    cumulativeBirthdayBound (merkleWalkQueries depth) ≤ Q * Q + 1 := by
  have hCumMono : ∀ a b, a ≤ b → cumulativeBirthdayBound a ≤ cumulativeBirthdayBound b := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih => simp only [cumulativeBirthdayBound]; omega
  refine ⟨?_, ?_, Nat.le_trans (hCumMono _ _ hWalk) (cumulativeBirthdayBound_le_sq_succ Q)⟩
  · intro h; cases h
  · unfold ratLe
    exact Nat.mul_le_mul_right C (finSum_stepHits_le_sq_succ C Q stepHistory hHistLen)

/-- Two-world keyed-ROM blinding / PRF hiding game over key space `Fin cardB`. -/
def keyedPrfRealAccept {TagDom Cod : Type} (cardB : Nat)
    (baseO : Fin cardB × TagDom → Cod) (secretVal : Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) : Nat :=
  finSum cardB (fun kStar =>
    let world0 : Fin cardB × TagDom → Cod :=
      fun q => if q.1 = kStar then secretVal else baseO q
    if evalOracleComp world0 A then 1 else 0)

def keyedPrfIdealAccept {TagDom Cod : Type} (cardB : Nat)
    (baseO : Fin cardB × TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) : Nat :=
  finSum cardB (fun _ => if evalOracleComp baseO A then 1 else 0)

theorem evalOracleComp_agree_if_key_unqueried {TagDom Cod α : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (secretVal : Cod) (kStar : Fin cardB) :
    ∀ (prog : OracleComp (Fin cardB × TagDom) Cod α),
      kStar ∉ (queryLog baseO prog).map Prod.fst →
      evalOracleComp (fun q => if q.1 = kStar then secretVal else baseO q) prog =
        evalOracleComp baseO prog
  | .pure _, _ => rfl
  | .query q next, hNotMem => by
    simp only [queryLog, List.map_cons, List.mem_cons, not_or] at hNotMem
    have hNe : q.1 ≠ kStar := fun h => hNotMem.1 h.symm
    simp only [evalOracleComp, hNe, ↓reduceIte]
    exact evalOracleComp_agree_if_key_unqueried baseO secretVal kStar (next (baseO q)) hNotMem.2

/-- **Keyed-ROM Blinding / PRF Hiding Floor (`hidingAdv_le`)**:
    For any `Q`-query adaptive distinguisher `A`, the distinguishing numerator across key space
    `Fin cardB` satisfies `|RealAccept - IdealAccept| ≤ Q ≤ 2 * Q`, hence rational distinguishing
    advantage `≤ 2Q / cardB` at **exact deployed cardinalities** (`BitVec 256` and `Goldilocks^4`). -/
theorem hidingAdv_le {TagDom Cod : Type}
    (cardB Q : Nat)
    (baseO : Fin cardB × TagDom → Cod) (secretVal : Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool)
    (hBounded : QueryBounded Q A) :
    let advNum := natAbsDiff (keyedPrfRealAccept cardB baseO secretVal A)
                             (keyedPrfIdealAccept cardB baseO A)
    advNum ≤ Q ∧
    ratLe (advNum, cardB) (2 * Q, cardB) := by
  intro advNum
  let touchedKeys : List (Fin cardB) := (queryLog baseO A).map Prod.fst
  have hLen : touchedKeys.length ≤ Q := by
    simp only [touchedKeys, List.length_map]
    exact queryLog_length_le baseO hBounded
  have hDiff : advNum ≤ finSum cardB (fun k => if k ∈ touchedKeys then 1 else 0) := by
    have hBadEq :
        finSum cardB (fun k => if decide (k ∈ touchedKeys) = true then 1 else 0) =
        finSum cardB (fun k => if k ∈ touchedKeys then 1 else 0) := by
      apply finSum_congr
      intro k
      by_cases hk : k ∈ touchedKeys <;> simp [hk]
    rw [← hBadEq]
    exact finSum_indicator_diff_le
      (fun kStar => evalOracleComp (fun q => if q.1 = kStar then secretVal else baseO q) A)
      (fun _ => evalOracleComp baseO A)
      (fun k => decide (k ∈ touchedKeys))
      (fun k hkFalse => by
        have hkNotMem : k ∉ touchedKeys := by
          intro hm; simp [hm] at hkFalse
        exact evalOracleComp_agree_if_key_unqueried baseO secretVal k A hkNotMem)
  have hAdvLeQ : advNum ≤ Q :=
    Nat.le_trans hDiff (Nat.le_trans (finSum_mem_list_le cardB touchedKeys) hLen)
  refine ⟨hAdvLeQ, ?_⟩
  unfold ratLe
  have h2Q : advNum ≤ 2 * Q := by omega
  exact Nat.mul_le_mul_right cardB h2Q

/-- Specialization of `hidingAdv_le` to both exact deployed `Obend` cardinalities (`2^256` & `p^4`). -/
theorem hidingAdv_le_deployed {TagDom Cod : Type} (Q : Nat)
    (baseBv : Fin deployedCardBitVec256 × TagDom → Cod)
    (baseGl : Fin deployedCardGoldilocks4 × TagDom → Cod)
    (secCod : Cod)
    (Abv : OracleComp (Fin deployedCardBitVec256 × TagDom) Cod Bool)
    (Agl : OracleComp (Fin deployedCardGoldilocks4 × TagDom) Cod Bool)
    (hBv : QueryBounded Q Abv) (hGl : QueryBounded Q Agl) :
    ratLe (natAbsDiff (keyedPrfRealAccept deployedCardBitVec256 baseBv secCod Abv)
                      (keyedPrfIdealAccept deployedCardBitVec256 baseBv Abv),
           deployedCardBitVec256)
          (2 * Q, deployedCardBitVec256) ∧
    ratLe (natAbsDiff (keyedPrfRealAccept deployedCardGoldilocks4 baseGl secCod Agl)
                      (keyedPrfIdealAccept deployedCardGoldilocks4 baseGl Agl),
           deployedCardGoldilocks4)
          (2 * Q, deployedCardGoldilocks4) := by
  exact ⟨(hidingAdv_le deployedCardBitVec256 Q baseBv secCod Abv hBv).2,
         (hidingAdv_le deployedCardGoldilocks4 Q baseGl secCod Agl hGl).2⟩

/-- Unrestricted full-table reader querying every key `0 .. cardB - 1` (`Q = cardB`). -/
def buildFullTableReader (cardB : Nat) : (rem : Nat) → rem ≤ cardB →
    OracleComp (Fin cardB × Unit) Bool Bool
  | 0, _ => .pure false
  | m + 1, hm =>
    .query (⟨cardB - (m + 1), by omega⟩, ()) (fun b =>
      if b then .pure true else buildFullTableReader cardB m (by omega))

/-- 1-query guesser probing key `0` once (`QueryBounded 1`). -/
def oneQueryGuesser (cardB : Nat) (hPos : 0 < cardB) : OracleComp (Fin cardB × Unit) Bool Bool :=
  .query (⟨0, hPos⟩, ()) (fun b => .pure b)

/-- 0-query hardcoder outputting a fixed bit (`QueryBounded 0`). -/
def zeroQueryHardcoder (cardB : Nat) (c : Bool) : OracleComp (Fin cardB × Unit) Bool Bool :=
  .pure c

/-- **Three-Regime `KeyedLazyRO` Query Characterization (`lazyRo_query_regime_characterization`)**:
    1. **0-query hardcoder** (`Q = 0`): achieves **exact** distinguishing numerator `0`.
    2. **1-query guesser** (`Q = 1`): achieves **strictly positive** advantage (`1 > 0`) while staying
       inside `hidingAdv_le` (`1 ≤ 2 * 1`).
    3. **Full-table reader** (`Q = cardB`, illustrated at `cardB = 8`): achieves advantage `8`,
       strictly breaking the `2 * qSmall` bound for `qSmall = 1` (`8 > 2`). -/
theorem lazyRo_query_regime_characterization (cardB : Nat) (hPos : 0 < cardB) (c : Bool) :
    natAbsDiff (keyedPrfRealAccept cardB (fun _ => false) true (zeroQueryHardcoder cardB c))
               (keyedPrfIdealAccept cardB (fun _ => false) (zeroQueryHardcoder cardB c)) = 0 ∧
    (0 < natAbsDiff (keyedPrfRealAccept cardB (fun _ => false) true (oneQueryGuesser cardB hPos))
                    (keyedPrfIdealAccept cardB (fun _ => false) (oneQueryGuesser cardB hPos)) ∧
     QueryBounded 1 (oneQueryGuesser cardB hPos)) ∧
    2 * 1 < natAbsDiff (keyedPrfRealAccept 8 (fun _ => false) true (buildFullTableReader 8 8 (Nat.le_refl 8)))
                       (keyedPrfIdealAccept 8 (fun _ => false) (buildFullTableReader 8 8 (Nat.le_refl 8))) := by
  refine ⟨?_, ⟨?_, fun _ => trivial⟩, by decide⟩
  · unfold keyedPrfRealAccept keyedPrfIdealAccept zeroQueryHardcoder evalOracleComp
    simp [natAbsDiff]
  · unfold keyedPrfRealAccept keyedPrfIdealAccept oneQueryGuesser evalOracleComp
    have hIdeal0 : finSum cardB (fun _ => (0 : Nat)) = 0 := by rw [finSum_const]; omega
    have hReal1 :
        finSum cardB (fun kStar : Fin cardB =>
          if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0) = 1 := by
      have hCongr :
          finSum cardB (fun kStar : Fin cardB =>
            if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0) =
          finSum cardB (fun kStar : Fin cardB => if kStar = ⟨0, hPos⟩ then 1 else 0) := by
        apply finSum_congr
        intro kStar
        by_cases hk : kStar = ⟨0, hPos⟩
        · subst hk; simp
        · have hne : (⟨0, hPos⟩ : Fin cardB) ≠ kStar := fun h => hk h.symm
          simp [hk, hne]
      rw [hCongr, finSum_eq_indicator]
    change 0 < natAbsDiff
      (finSum cardB (fun kStar : Fin cardB =>
        if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0))
      (finSum cardB (fun _ => 0))
    rw [hReal1, hIdeal0]
    decide

/-- **Transparent Per-Adversary Fixed-Sponge Bridge (`RomFaithfulInstantiation`)**:
    Explicit `def` (never a global `axiom`!) stating that a concrete `Q`-query algorithm `A`
    predicting an output of fixed concrete hash `H₀ : Dom → Fin cardCod` (`cardCod ≥ 2`) obeys
    the query-bounded `KeyedLazyRO` rational floor `(Q + 1, cardCod)`. -/
@[expose] def RomFaithfulInstantiation {Dom : Type} {cardCod : Nat}
    (H₀ : Dom → Fin cardCod) (Q : Nat) (xTarget : Dom)
    (A : OracleComp Dom (Fin cardCod) (Fin cardCod)) : Prop :=
  QueryBounded Q A ∧
  ratLe (if evalOracleComp H₀ A = H₀ xTarget then 1 else 0, 1) (Q + 1, cardCod)

/-- **Refutation of Universal Fixed-Function ROM (`not_universal_romFaithful`)**:
    For ANY fixed deterministic hash function `H₀` (`cardCod ≥ 2`), there exists a `0`-query
    adversary `bakedAdv := .pure (H₀ xTarget)` baking `H₀(xTarget)` into its code that breaks
    `RomFaithfulInstantiation H₀ 0` (`1 ≤ 1 / cardCod` is false for `cardCod ≥ 2`). -/
theorem not_universal_romFaithful {Dom : Type} {cardCod : Nat}
    (hGe2 : 2 ≤ cardCod) (H₀ : Dom → Fin cardCod) (xTarget : Dom) :
    ∃ A : OracleComp Dom (Fin cardCod) (Fin cardCod),
      QueryBounded 0 A ∧ ¬ RomFaithfulInstantiation H₀ 0 xTarget A := by
  refine ⟨.pure (H₀ xTarget), trivial, ?_⟩
  intro hFaith
  rcases hFaith with ⟨_, hRat⟩
  unfold ratLe evalOracleComp at hRat
  simp only [↓reduceIte] at hRat
  omega

/-! ## 2. Polymorphic Shamir Pad-Space Bijection (`Goldilocks`, `GoldilocksExt2`, `TowerElem k`) -/

section PolymorphicPadBijection
open CommRingOps

/-- Fixed-width (`len = t`) coefficient addition/subtraction over `[CommRingOps R]`. -/
def polyAddFixed {R : Type} [CommRingOps R] : List R → List R → List R
  | a :: as, b :: bs => add a b :: polyAddFixed as bs
  | [], _ => []
  | _, [] => []

def polySubFixed {R : Type} [CommRingOps R] : List R → List R → List R
  | a :: as, b :: bs => sub a b :: polySubFixed as bs
  | [], _ => []
  | _, [] => []

def polyScale {R : Type} [CommRingOps R] (s : R) : List R → List R
  | [] => []
  | c :: cs => mul s c :: polyScale s cs

theorem polyAddFixed_length {R : Type} [CommRingOps R] :
    ∀ (p q : List R), p.length = q.length → (polyAddFixed p q).length = p.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polyAddFixed_length as bs h]

theorem polySubFixed_length {R : Type} [CommRingOps R] :
    ∀ (p q : List R), p.length = q.length → (polySubFixed p q).length = p.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polySubFixed, polySubFixed_length as bs h]

theorem polyScale_length {R : Type} [CommRingOps R] (s : R) (p : List R) :
    (polyScale s p).length = p.length := by
  induction p <;> simp [polyScale, *]

private theorem add_sub_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    sub (add a b) b = a := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

private theorem sub_add_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    add (sub a b) b = a := by
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

theorem polySub_polyAdd_cancel {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R), p.length = q.length → polySubFixed (polyAddFixed p q) q = p
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polySubFixed, add_sub_cancel_right, polySub_polyAdd_cancel as bs h]

theorem polyAdd_polySub_cancel {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R), p.length = q.length → polyAddFixed (polySubFixed p q) q = p
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polySubFixed, sub_add_cancel_right, polyAdd_polySub_cancel as bs h]

theorem evalCoeffs_addFixed {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R), p.length = q.length →
      RoundPoly.evalCoeffs (polyAddFixed p q) x =
        add (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], [], _, _ => by simp [polyAddFixed, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | a :: as, b :: bs, x, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [polyAddFixed, RoundPoly.evalCoeffs, evalCoeffs_addFixed as bs x h]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem evalCoeffs_subFixed {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R), p.length = q.length →
      RoundPoly.evalCoeffs (polySubFixed p q) x =
        sub (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], [], _, _ => by simp [polySubFixed, RoundPoly.evalCoeffs, LawfulCommRing.sub_self]
  | a :: as, b :: bs, x, h => by
    have hLen : (polySubFixed (a :: as) (b :: bs)).length = (b :: bs).length := by
      rw [polySubFixed_length (a :: as) (b :: bs) h, h]
    have hEq := evalCoeffs_addFixed (polySubFixed (a :: as) (b :: bs)) (b :: bs) x hLen
    rw [polyAdd_polySub_cancel (a :: as) (b :: bs) h] at hEq
    have hSub := congrArg (fun u => sub u (RoundPoly.evalCoeffs (b :: bs) x)) hEq
    rw [add_sub_cancel_right] at hSub
    exact hSub.symm

theorem evalCoeffs_scale {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (polyScale s p) x = mul s (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [polyScale, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [polyScale, RoundPoly.evalCoeffs, evalCoeffs_scale s cs x]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc x s _,
        LawfulCommRing.mul_comm x s, LawfulCommRing.mul_assoc s x _]

private def mulLinearAux {R : Type} [CommRingOps R] (k prev : R) : List R → List R
  | [] => [prev]
  | c :: cs => add c prev :: mulLinearAux k (mul k c) cs

/-- Multiply `p(X)` by linear factor `(1 + k * X)` incrementing list length by `1`. -/
def mulOnePlusKX {R : Type} [CommRingOps R] (k : R) : List R → List R
  | [] => []
  | c :: cs => c :: mulLinearAux k (mul k c) cs

private theorem mulLinearAux_length {R : Type} [CommRingOps R] (k prev : R) :
    ∀ (cs : List R), (mulLinearAux k prev cs).length = cs.length + 1
  | [] => rfl
  | _ :: cs => by simp [mulLinearAux, mulLinearAux_length k _ cs]

theorem mulOnePlusKX_length {R : Type} [CommRingOps R] (k : R) :
    ∀ (p : List R), p ≠ [] → (mulOnePlusKX k p).length = p.length + 1
  | [], h => False.elim (h rfl)
  | _ :: _, _ => by simp [mulOnePlusKX, mulLinearAux_length]

private theorem evalCoeffs_mulLinearAux {R : Type} [LawfulCommRing R] (k prev : R) :
    ∀ (cs : List R) (x : R),
      RoundPoly.evalCoeffs (mulLinearAux k prev cs) x =
        add prev (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x))
  | [], x => by
    simp [mulLinearAux, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [mulLinearAux, RoundPoly.evalCoeffs, evalCoeffs_mulLinearAux k (mul k c) cs x]
    rw [LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (add one (mul k x)),
        LawfulCommRing.right_distrib one (mul k x) c, LawfulCommRing.one_mul]
    have hxc : mul x (mul k c) = mul (mul k x) c := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x k]
    have hxs : mul x (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x)) =
        mul (add one (mul k x)) (mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (add one (mul k x)),
          LawfulCommRing.mul_assoc]
    rw [hxc, hxs, LawfulCommRing.add_comm c prev, LawfulCommRing.add_assoc prev c,
        LawfulCommRing.add_assoc c (mul (mul k x) c)]

theorem evalCoeffs_mulOnePlusKX {R : Type} [LawfulCommRing R] (k : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (mulOnePlusKX k p) x =
        mul (add one (mul k x)) (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [mulOnePlusKX, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [mulOnePlusKX, RoundPoly.evalCoeffs, evalCoeffs_mulLinearAux]
    rw [LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (add one (mul k x)),
        LawfulCommRing.right_distrib one (mul k x) c, LawfulCommRing.one_mul, ← LawfulCommRing.add_assoc]
    have hxc : mul x (mul k c) = mul (mul k x) c := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x k]
    have hxs : mul x (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x)) =
        mul (add one (mul k x)) (mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (add one (mul k x)),
          LawfulCommRing.mul_assoc]
    rw [hxc, hxs]

/-- Raw Lagrange-vanishing polynomial `∏_{x_c ∈ C} (1 - x_c⁻¹ X)` over `[LawfulCommRing R]`. -/
def vanishCorruptRaw {R : Type} [CommRingOps R] (inv : R → R) : List R → List R
  | [] => [one]
  | xc :: rest => mulOnePlusKX (neg (inv xc)) (vanishCorruptRaw inv rest)

theorem vanishCorruptRaw_nonempty {R : Type} [CommRingOps R] (inv : R → R) :
    ∀ (cs : List R), vanishCorruptRaw inv cs ≠ []
  | [] => by simp [vanishCorruptRaw]
  | xc :: rest => by
    have ih := vanishCorruptRaw_nonempty inv rest
    cases h : vanishCorruptRaw inv rest with
    | nil => exact False.elim (ih h)
    | cons c cs => simp [vanishCorruptRaw, h, mulOnePlusKX]

theorem vanishCorruptRaw_length {R : Type} [CommRingOps R] (inv : R → R) :
    ∀ (cs : List R), (vanishCorruptRaw inv cs).length = cs.length + 1
  | [] => rfl
  | _ :: rest => by
    simp only [vanishCorruptRaw, List.length_cons]
    rw [mulOnePlusKX_length _ _ (vanishCorruptRaw_nonempty inv rest), vanishCorruptRaw_length inv rest]

theorem evalCoeffs_replicate_zero {R : Type} [LawfulCommRing R] :
    ∀ (k : Nat) (x : R), RoundPoly.evalCoeffs (List.replicate k (zero : R)) x = zero
  | 0, _ => rfl
  | k + 1, x => by
    simp [List.replicate_succ, RoundPoly.evalCoeffs, evalCoeffs_replicate_zero k x,
          LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem evalCoeffs_padZerosRight {R : Type} [LawfulCommRing R] :
    ∀ (p : List R) (k : Nat) (x : R),
      RoundPoly.evalCoeffs (p ++ List.replicate k (zero : R)) x = RoundPoly.evalCoeffs p x
  | [], k, x => by simp [evalCoeffs_replicate_zero, RoundPoly.evalCoeffs]
  | c :: cs, k, x => by simp [List.cons_append, RoundPoly.evalCoeffs, evalCoeffs_padZerosRight cs k x]

/-- Fixed-length (`t` coefficients, degree `≤ t - 1`) Lagrange rebalance polynomial `L_C(X)`. -/
def vanishCorruptUnit0 {R : Type} [CommRingOps R] (inv : R → R) (t : Nat) (corruptPts : List R) : List R :=
  let raw := vanishCorruptRaw inv corruptPts
  raw ++ List.replicate (t - raw.length) zero

theorem vanishCorruptUnit0_props {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    {t : Nat} {corruptPts : List R}
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero) :
    (vanishCorruptUnit0 inv t corruptPts).length = t ∧
    RoundPoly.evalCoeffs (vanishCorruptUnit0 inv t corruptPts) zero = one ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs (vanishCorruptUnit0 inv t corruptPts) xc = zero) := by
  have hRawLen := vanishCorruptRaw_length inv corruptPts
  have hAtZero : ∀ cs : List R, RoundPoly.evalCoeffs (vanishCorruptRaw inv cs) zero = one := by
    intro cs
    induction cs with
    | nil =>
      simp [vanishCorruptRaw, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons xc rest ih =>
      simp [vanishCorruptRaw, evalCoeffs_mulOnePlusKX, ih,
            LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_one]
  have hAtCorr : ∀ {cs : List R} {x : R},
      (∀ c ∈ cs, c ≠ zero) → x ∈ cs → RoundPoly.evalCoeffs (vanishCorruptRaw inv cs) x = zero := by
    intro cs x hNz hx
    induction cs with
    | nil => cases hx
    | cons xc rest ih =>
      simp only [vanishCorruptRaw, evalCoeffs_mulOnePlusKX]
      rcases List.mem_cons.mp hx with rfl | hMemRest
      · have hxNz : x ≠ zero := hNz x (.head rest)
        have hFactor : add one (mul (neg (inv x)) x) = zero := by
          rw [LawfulCommRing.neg_mul, LawfulCommRing.mul_comm (inv x) x,
              hInv x hxNz, LawfulCommRing.add_right_neg]
        rw [hFactor, LawfulCommRing.zero_mul]
      · rw [ih (fun c hc => hNz c (.tail xc hc)) hMemRest, LawfulCommRing.mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold vanishCorruptUnit0
    dsimp only
    rw [List.length_append, List.length_replicate, hRawLen]
    omega
  · unfold vanishCorruptUnit0
    dsimp only
    rw [evalCoeffs_padZerosRight, hAtZero]
  · intro xc hxc
    unfold vanishCorruptUnit0
    dsimp only
    rw [evalCoeffs_padZerosRight]
    exact hAtCorr hNonZero hxc

/-- Two-sided constructive bijection (`SimpleEquiv`) on degree-`≤ (t - 1)` Shamir pad polynomials. -/
structure SimpleEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

/-- Degree-`≤ (t - 1)` Shamir pad space (`t` field coefficients) over `R`. -/
abbrev ShamirPadPoly (R : Type) (t : Nat) := { p : List R // p.length = t }

/-- **Constructive Polymorphic Shamir Pad-Space Bijection (`shamir_rebalanceEquiv`)**:
    Maps real pad polynomial `P` to `P + w · L_C(X)` (and back via `Q - w · L_C(X)`),
    preserving degree `< t` for any `|C| ≤ t - 1` corrupt evaluation points over any field `R`! -/
@[expose] def shamir_rebalanceEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (t : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ t) :
    SimpleEquiv (ShamirPadPoly R t) (ShamirPadPoly R t) :=
  let delta := polyScale w (vanishCorruptUnit0 inv t corruptPts)
  have hDeltaLen : delta.length = t := by
    rw [polyScale_length]
    unfold vanishCorruptUnit0; dsimp only
    rw [List.length_append, List.length_replicate, vanishCorruptRaw_length]
    omega
  { toFun := fun ⟨p, hp⟩ => ⟨polyAddFixed p delta, by rw [polyAddFixed_length p delta (hp.trans hDeltaLen.symm), hp]⟩
    invFun := fun ⟨q, hq⟩ => ⟨polySubFixed q delta, by rw [polySubFixed_length q delta (hq.trans hDeltaLen.symm), hq]⟩
    left_inv := fun ⟨p, hp⟩ => Subtype.ext (polySub_polyAdd_cancel p delta (hp.trans hDeltaLen.symm))
    right_inv := fun ⟨q, hq⟩ => Subtype.ext (polyAdd_polySub_cancel q delta (hq.trans hDeltaLen.symm)) }

/-- **Characteristic-2 Strict Involution (`shamir_tower_rebalance_involutive`)**:
    Over `BinaryTower256.TowerElem k` (`k = 3` for `GF(2^8)`, `k = 7` for `Tower128`), `add = sub`,
    so `shamir_rebalanceEquiv.toFun` is a strict involution `φ(φ(P)) = P` on `ShamirPadPoly` itself! -/
theorem shamir_tower_rebalance_involutive (k t : Nat)
    (corruptPts : List (TowerElem k)) (w : TowerElem k)
    (hCard : corruptPts.length + 1 ≤ t)
    (P : ShamirPadPoly (TowerElem k) t) :
    let eqv := shamir_rebalanceEquiv (towerInv k) t corruptPts w hCard
    eqv.toFun (eqv.toFun P) = P := by
  intro eqv
  have hAddEqSub : ∀ (u v : List (TowerElem k)), polyAddFixed u v = polySubFixed u v := by
    intro u v
    induction u generalizing v with
    | nil => cases v <;> rfl
    | cons a as ih =>
      cases v with
      | nil => rfl
      | cons b bs =>
        simp only [polyAddFixed, polySubFixed]
        exact congrArg (towerAdd k a b :: ·) (ih bs)
  have hEqInv : eqv.toFun (eqv.toFun P) = eqv.invFun (eqv.toFun P) := by
    apply Subtype.ext
    exact hAddEqSub _ _
  rw [hEqInv, eqv.left_inv]

/-- **Pad-Space Bijection Uniformity & Zero-Knowledge Theorem (`pad_bijection_masked_openings_uniform`)**:
    For ANY secret wire `w : R` and ANY `|C| ≤ t - 1` corrupt evaluation points (`∀ c ∈ C, c ≠ 0`):
    `Q = shamir_rebalanceEquiv.toFun P` satisfies:
    1. **Exact Masked-Opening Match:** `0 + Q(0) = w + P(0)` (real masked opening `w + r` equals
       simulated `0`-secret opening `0 + r'`);
    2. **Exact Corrupt-Share Invariance:** `∀ xc ∈ corruptPts, Q(xc) = P(xc)` (every corrupt party's
       Shamir share is **100% unchanged**!). -/
theorem pad_bijection_masked_openings_uniform {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (t : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (P : ShamirPadPoly R t) :
    let Q := (shamir_rebalanceEquiv inv t corruptPts w hCard).toFun P
    add zero (RoundPoly.evalCoeffs Q.1 zero) =
      add w (RoundPoly.evalCoeffs P.1 zero) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc) := by
  intro Q
  obtain ⟨hULen, hU0, hUCorr⟩ := vanishCorruptUnit0_props inv hInv hCard hNonZero
  have hScaleLen : (polyScale w (vanishCorruptUnit0 inv t corruptPts)).length = t := by
    rw [polyScale_length, hULen]
  refine ⟨?_, ?_⟩
  · change add zero
      (RoundPoly.evalCoeffs (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv t corruptPts))) zero) = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale, hU0,
        LawfulCommRing.zero_add, LawfulCommRing.mul_one, LawfulCommRing.add_comm]
  · intro xc hxc
    change RoundPoly.evalCoeffs (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv t corruptPts))) xc = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale, hUCorr xc hxc,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- Concrete specializations of `pad_bijection_masked_openings_uniform` to `Goldilocks` and `TowerElem k`. -/
theorem pad_bijection_goldilocks_and_tower (k t : Nat)
    (corrGl : List Goldilocks) (wGl : Goldilocks)
    (hCardGl : corrGl.length + 1 ≤ t) (hNzGl : ∀ c ∈ corrGl, c ≠ CommRingOps.zero)
    (PGl : ShamirPadPoly Goldilocks t)
    (corrTw : List (TowerElem k)) (wTw : TowerElem k)
    (hCardTw : corrTw.length + 1 ≤ t) (hNzTw : ∀ c ∈ corrTw, c ≠ CommRingOps.zero)
    (PTw : ShamirPadPoly (TowerElem k) t) :
    let QGl := (shamir_rebalanceEquiv Goldilocks.inv t corrGl wGl hCardGl).toFun PGl
    let QTw := (shamir_rebalanceEquiv (towerInv k) t corrTw wTw hCardTw).toFun PTw
    (add zero (RoundPoly.evalCoeffs QGl.1 zero) = add wGl (RoundPoly.evalCoeffs PGl.1 zero) ∧
     ∀ xc ∈ corrGl, RoundPoly.evalCoeffs QGl.1 xc = RoundPoly.evalCoeffs PGl.1 xc) ∧
    (add zero (RoundPoly.evalCoeffs QTw.1 zero) = add wTw (RoundPoly.evalCoeffs PTw.1 zero) ∧
     ∀ xc ∈ corrTw, RoundPoly.evalCoeffs QTw.1 xc = RoundPoly.evalCoeffs PTw.1 xc) := by
  exact ⟨pad_bijection_masked_openings_uniform Goldilocks.inv (fun _ hx => Goldilocks.mul_inv_cancel hx) t corrGl wGl hCardGl hNzGl PGl,
         pad_bijection_masked_openings_uniform (towerInv k) (towerMul_inv k) t corrTw wTw hCardTw hNzTw PTw⟩

/-- **Negative Tooth 1 (`full_collusion_breaks_hiding`, `|C| = t`)**:
    When `|C| = t` distinct evaluation points are corrupted over any domain `[NoZeroDivisors R]`,
    two degree-`< t` pad polynomials agreeing on all `t` corrupt points MUST agree at `0`
    (`P(0) = Q(0)`), refuting secret hiding for any `w₁ ≠ w₂`! -/
theorem full_collusion_breaks_hiding {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (t : Nat) (corruptPts : List R)
    (hFull : corruptPts.length = t) (hNodup : corruptPts.Nodup)
    (w₁ w₂ : R) (hDistinct : w₁ ≠ w₂)
    (P Q : ShamirPadPoly R t)
    (hSameShares : ∀ xc ∈ corruptPts, RoundPoly.evalCoeffs P.1 xc = RoundPoly.evalCoeffs Q.1 xc) :
    add w₁ (RoundPoly.evalCoeffs P.1 zero) ≠ add w₂ (RoundPoly.evalCoeffs Q.1 zero) := by
  have hZeroEq : RoundPoly.evalCoeffs P.1 zero = RoundPoly.evalCoeffs Q.1 zero := by
    cases t with
    | zero =>
      have hp0 : P.1 = [] := List.eq_nil_of_length_eq_zero P.2
      have hq0 : Q.1 = [] := List.eq_nil_of_length_eq_zero Q.2
      rw [hp0, hq0]
    | succ d =>
      let diff := polySubFixed P.1 Q.1
      have hDiffLen : diff.length ≤ d + 1 := by
        rw [polySubFixed_length P.1 Q.1 (P.2.trans Q.2.symm), P.2]
        exact Nat.le_refl (d + 1)
      if hAt0 : RoundPoly.evalCoeffs P.1 zero = RoundPoly.evalCoeffs Q.1 zero then
        exact hAt0
      else
        exfalso
        have hNz0 : RoundPoly.evalCoeffs diff zero ≠ zero := by
          rw [evalCoeffs_subFixed P.1 Q.1 zero (P.2.trans Q.2.symm)]
          intro hSub0
          have hAdd := congrArg (fun u => add u (RoundPoly.evalCoeffs Q.1 zero)) hSub0
          rw [sub_add_cancel_right, LawfulCommRing.zero_add] at hAdd
          exact hAt0 hAdd
        have hFiltEq : corruptPts.filter (fun r => decide (RoundPoly.evalCoeffs diff r = zero)) =
            corruptPts := by
          apply List.filter_eq_self.mpr
          intro xc hxc
          rw [evalCoeffs_subFixed P.1 Q.1 xc (P.2.trans Q.2.symm), hSameShares xc hxc,
              LawfulCommRing.sub_self]
          exact decide_eq_true rfl
        have hBound := RoundPoly.roots_nodup_length_le d diff corruptPts hNodup hDiffLen ⟨zero, hNz0⟩
        rw [hFiltEq, hFull] at hBound
        omega
  intro hEqOpen
  rw [hZeroEq] at hEqOpen
  have hSub := congrArg (fun u => sub u (RoundPoly.evalCoeffs Q.1 zero)) hEqOpen
  rw [add_sub_cancel_right, add_sub_cancel_right] at hSub
  exact hDistinct hSub

/-- **Negative Tooth 2 (`unpadded_open_refutes_hiding`)**:
    Opening a secret wire with the zero pad (`P(0) = 0`) leaks `w` directly: distinct secrets
    `w₁ ≠ w₂` produce distinct public openings `w₁ + 0 ≠ w₂ + 0`. -/
theorem unpadded_open_refutes_hiding {R : Type} [LawfulCommRing R]
    (w₁ w₂ : R) (hDistinct : w₁ ≠ w₂) :
    add w₁ zero ≠ add w₂ zero := by
  rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  exact hDistinct

end PolymorphicPadBijection

/-! ## 3. Canetti Universal Composability for Signatures (`idealSig`, `ucRealizes_iff_eufCma`) -/

/-- Abstract signature interface for Canetti UC equivalence. -/
structure AbstractSigScheme (PK SK Msg Sig : Type) where
  sign : SK → Msg → Sig
  verify : PK → Msg → Sig → Bool
  complete : PK → SK → Prop
  completeness : ∀ {pk sk}, complete pk sk → ∀ m, verify pk m (sign sk m) = true

/-- Adaptive UC environment interacting with a signature session and outputting a `Bool` bit. -/
inductive UcSigEnv (PK Msg Sig : Type) where
  | halt (verdict : Bool)
  | stepSign (m : Msg) (next : Sig → UcSigEnv PK Msg Sig)
  | stepVerify (m : Msg) (sig : Sig) (next : Bool → UcSigEnv PK Msg Sig)

/-- Real protocol execution `(sign sk, verify pk)` against environment `Z`. -/
def execRealSig {PK SK Msg Sig : Type}
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) :
    UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execRealSig S pk sk (next (S.sign sk m))
  | .stepVerify m sig next => execRealSig S pk sk (next (S.verify pk m sig))

/-- Ideal signature functionality `idealSig` + canonical simulator `Sim` (unforgeable on `m ∉ recorded`). -/
@[expose] def idealSigVerify {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK)
    (recorded : List Msg) (m : Msg) (sig : Sig) : Bool :=
  decide (m ∈ recorded) && S.verify pk m sig

theorem idealSig_unforgeable {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK)
    (recorded : List Msg) (m : Msg) (sig : Sig) (hFresh : m ∉ recorded) :
    idealSigVerify S pk recorded m sig = false := by
  simp [idealSigVerify, hFresh]

def execIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execIdealSig S pk sk (m :: recorded) (next (S.sign sk m))
  | .stepVerify m sig next =>
    execIdealSig S pk sk recorded (next (idealSigVerify S pk recorded m sig))

/-- Constructive extractor scanning a `UcSigEnv` run for an unqueried EUF-CMA forgery `(m*, σ*)`. -/
def findEnvForgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Option (Msg × Sig)
  | .halt _ => none
  | .stepSign m next => findEnvForgery S pk sk (m :: recorded) (next (S.sign sk m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ S.verify pk m sig = true then
      some (m, sig)
    else
      findEnvForgery S pk sk recorded (next (idealSigVerify S pk recorded m sig))

theorem execReal_eq_execIdeal_unless_forgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig),
      findEnvForgery S pk sk recorded Z = none →
      execRealSig S pk sk Z = execIdealSig S pk sk recorded Z
  | .halt _, _ => rfl
  | .stepSign m next, hNone => by
    simp only [findEnvForgery] at hNone
    exact execReal_eq_execIdeal_unless_forgery S pk sk (m :: recorded) (next (S.sign sk m)) hNone
  | .stepVerify m sig next, hNone => by
    simp only [findEnvForgery] at hNone
    by_cases hBad : m ∉ recorded ∧ S.verify pk m sig = true
    · simp [hBad] at hNone
    · simp only [hBad, ↓reduceIte] at hNone
      have hVerdictEq : S.verify pk m sig = idealSigVerify S pk recorded m sig := by
        unfold idealSigVerify
        by_cases hm : m ∈ recorded
        · simp [hm]
        · cases hv : S.verify pk m sig
          · simp [hm]
          · exact False.elim (hBad ⟨hm, hv⟩)
      simp only [execRealSig, execIdealSig, hVerdictEq]
      exact execReal_eq_execIdeal_unless_forgery S pk sk recorded
        (next (idealSigVerify S pk recorded m sig)) hNone

/-- All messages signed along the ideal transcript up to the point `findEnvForgery` halts. -/
def signedBeforeForgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → List Msg
  | .halt _ => recorded
  | .stepSign m next => signedBeforeForgery S pk sk (m :: recorded) (next (S.sign sk m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ S.verify pk m sig = true then
      recorded
    else
      signedBeforeForgery S pk sk recorded (next (idealSigVerify S pk recorded m sig))

theorem findEnvForgery_sound {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig) {mStar : Msg} {sigStar : Sig},
      findEnvForgery S pk sk recorded Z = some (mStar, sigStar) →
      mStar ∉ signedBeforeForgery S pk sk recorded Z ∧ S.verify pk mStar sigStar = true
  | .halt _, _, _, h => by cases h
  | .stepSign m next, _, _, h => by
    simp only [findEnvForgery] at h
    simp only [signedBeforeForgery]
    exact findEnvForgery_sound S pk sk (m :: recorded) (next (S.sign sk m)) h
  | .stepVerify m sig next, _, _, h => by
    simp only [findEnvForgery] at h
    simp only [signedBeforeForgery]
    by_cases hBad : m ∉ recorded ∧ S.verify pk m sig = true
    · simp only [hBad] at h ⊢
      injection h with hPair
      injection hPair with hm hs
      subst hm hs
      exact hBad
    · simp only [hBad] at h ⊢
      exact findEnvForgery_sound S pk sk recorded (next (idealSigVerify S pk recorded m sig)) h

/-- Predicate that `(pk, sk)` admits no unqueried forgery from environment `Z`. -/
@[expose] def UcIndistinguishableOn {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (Z : UcSigEnv PK Msg Sig) : Prop :=
  execRealSig S pk sk Z = execIdealSig S pk sk [] Z

/-- **Canetti UC Signature Equivalence (`ucRealizes_iff_eufCma`)**:
    1. Every UC environment `Z` distinguishing Real signing from `idealSig` constructively yields
       an unqueried EUF-CMA forgery `(m*, σ*)` (`m* ∉ signedBeforeForgery`, `verify pk m* σ* = true`);
    2. Conversely, any fresh forgery `(m*, σ*)` (`verify pk m* σ* = true`) distinguishes Real signing
       from `idealSig` in a 1-step verification environment `Z_forge := .stepVerify m* σ* (.halt ·)`. -/
theorem ucRealizes_iff_eufCma {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) :
    (∀ Z : UcSigEnv PK Msg Sig,
      ¬ UcIndistinguishableOn S pk sk Z →
      ∃ mStar sigStar,
        findEnvForgery S pk sk [] Z = some (mStar, sigStar) ∧
        mStar ∉ signedBeforeForgery S pk sk [] Z ∧
        S.verify pk mStar sigStar = true) ∧
    (∀ mStar sigStar, S.verify pk mStar sigStar = true →
      ¬ UcIndistinguishableOn S pk sk (.stepVerify mStar sigStar (fun b => .halt b))) := by
  refine ⟨?_, ?_⟩
  · intro Z hDist
    cases hFind : findEnvForgery S pk sk [] Z with
    | none =>
      exact False.elim (hDist (execReal_eq_execIdeal_unless_forgery S pk sk [] Z hFind))
    | some pair =>
      rcases pair with ⟨mStar, sigStar⟩
      obtain ⟨hFresh, hVer⟩ := findEnvForgery_sound S pk sk [] Z hFind
      exact ⟨mStar, sigStar, rfl, hFresh, hVer⟩
  · intro mStar sigStar hVer hEq
    have hReal : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) = true := by
      simp [execRealSig, hVer]
    have hIdeal : execIdealSig S pk sk [] (.stepVerify mStar sigStar (fun b => .halt b)) = false := by
      simp [execIdealSig, idealSigVerify]
    have hEq' : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) =
        execIdealSig S pk sk [] (.stepVerify mStar sigStar (fun b => .halt b)) := hEq
    rw [hReal, hIdeal] at hEq'
    cases hEq'

/-- Polymorphic linear Lagrange functional `∑_q λ_q · y_q` and monomial powers `x^d`. -/
def ringDot {R : Type} [CommRingOps R] : List R → List R → R
  | l :: ls, y :: ys => CommRingOps.add (CommRingOps.mul l y) (ringDot ls ys)
  | _, _ => CommRingOps.zero

def ringPow {R : Type} [CommRingOps R] (x : R) : Nat → R
  | 0 => CommRingOps.one
  | k + 1 => CommRingOps.mul (ringPow x k) x

private def evalShifted {R : Type} [CommRingOps R] : List R → Nat → R → R
  | [], _, _ => CommRingOps.zero
  | c :: cs, shift, x => CommRingOps.add (CommRingOps.mul c (ringPow x shift)) (evalShifted cs (shift + 1) x)

private theorem evalShifted_eq_mul_pow {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (shift : Nat) (x : R),
      evalShifted cs shift x = CommRingOps.mul (ringPow x shift) (RoundPoly.evalCoeffs cs x)
  | [], shift, x => by simp [evalShifted, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | c :: cs, shift, x => by
    simp only [evalShifted, RoundPoly.evalCoeffs, evalShifted_eq_mul_pow cs (shift + 1) x, ringPow]
    rw [LawfulCommRing.mul_comm c (ringPow x shift), LawfulCommRing.mul_assoc (ringPow x shift) x _,
        ← LawfulCommRing.left_distrib]

private theorem ringDot_map_zero {R : Type} [LawfulCommRing R] :
    ∀ (ls pts : List R), ringDot ls (pts.map (fun _ => CommRingOps.zero)) = CommRingOps.zero
  | [], _ => by simp [ringDot]
  | _ :: _, [] => by simp [ringDot]
  | l :: ls, _ :: ps => by
    simp only [List.map_cons, ringDot, LawfulCommRing.mul_zero, ringDot_map_zero ls ps, LawfulCommRing.zero_add]

private theorem ringDot_map_add {R : Type} [LawfulCommRing R] (f g : R → R) :
    ∀ (ls pts : List R),
      ringDot ls (pts.map (fun x => CommRingOps.add (f x) (g x))) =
        CommRingOps.add (ringDot ls (pts.map f)) (ringDot ls (pts.map g))
  | [], _ => by simp [ringDot, LawfulCommRing.add_zero]
  | _, [] => by simp [ringDot, LawfulCommRing.add_zero]
  | l :: ls, p :: ps => by
    simp only [List.map_cons, ringDot, ringDot_map_add f g ls ps,
               LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

private theorem ringDot_map_scale {R : Type} [LawfulCommRing R] (c : R) (f : R → R) :
    ∀ (ls pts : List R),
      ringDot ls (pts.map (fun x => CommRingOps.mul c (f x))) =
        CommRingOps.mul c (ringDot ls (pts.map f))
  | [], _ => by simp [ringDot, LawfulCommRing.mul_zero]
  | _, [] => by simp [ringDot, LawfulCommRing.mul_zero]
  | l :: ls, p :: ps => by
    simp only [List.map_cons, ringDot, ringDot_map_scale c f ls ps]
    have hSwap : CommRingOps.mul l (CommRingOps.mul c (f p)) = CommRingOps.mul c (CommRingOps.mul l (f p)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm l c, LawfulCommRing.mul_assoc]
    rw [hSwap, ← LawfulCommRing.left_distrib]

private theorem ringDot_evalShifted_tail_zero {R : Type} [LawfulCommRing R]
    (lambdas pts : List R) (t : Nat)
    (hHigher : ∀ d, 1 ≤ d → d < t → ringDot lambdas (pts.map (fun x => ringPow x d)) = CommRingOps.zero) :
    ∀ (cs : List R) (shift : Nat),
      1 ≤ shift → shift + cs.length ≤ t →
      ringDot lambdas (pts.map (fun x => evalShifted cs shift x)) = CommRingOps.zero
  | [], _, _, _ => ringDot_map_zero lambdas pts
  | c :: cs, shift, hGe1, hBound => by
    simp only [List.length_cons] at hBound
    simp only [evalShifted]
    rw [ringDot_map_add, ringDot_map_scale, hHigher shift hGe1 (by omega),
        LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    exact ringDot_evalShifted_tail_zero lambdas pts t hHigher cs (shift + 1) (by omega) (by omega)

/-- **Polymorphic Vandermonde / Lagrange-at-Zero Reconstruction (`lagrangeAtZero_evalCoeffs`)**:
    For ANY commutative ring `R` (`Goldilocks`, `TowerElem 3`, `TowerElem 7`) and threshold `t`,
    any Lagrange weight vector `lambdas` satisfying Vandermonde-at-zero moment orthogonality
    (`∑ λ_q = 1` and `∀ d ∈ [1, t), ∑ λ_q x_q^d = 0`) reconstructs `RoundPoly.evalCoeffs coeffs 0`
    identically for EVERY Shamir polynomial `coeffs` of length `≤ t`! -/
theorem lagrangeAtZero_evalCoeffs {R : Type} [LawfulCommRing R]
    (lambdas pts coeffs : List R) (t : Nat)
    (hLen : coeffs.length ≤ t)
    (hZero : ringDot lambdas (pts.map (fun _ => CommRingOps.one)) = CommRingOps.one)
    (hHigher : ∀ d, 1 ≤ d → d < t → ringDot lambdas (pts.map (fun x => ringPow x d)) = CommRingOps.zero) :
    ringDot lambdas (pts.map (fun x => RoundPoly.evalCoeffs coeffs x)) =
      RoundPoly.evalCoeffs coeffs CommRingOps.zero := by
  have hToShift : ∀ x : R, RoundPoly.evalCoeffs coeffs x = evalShifted coeffs 0 x := by
    intro x
    rw [evalShifted_eq_mul_pow coeffs 0 x, ringPow, LawfulCommRing.one_mul]
  have hMapEq : pts.map (fun x => RoundPoly.evalCoeffs coeffs x) =
      pts.map (fun x => evalShifted coeffs 0 x) := List.map_congr_left (fun x _ => hToShift x)
  rw [hMapEq]
  cases coeffs with
  | nil => exact ringDot_map_zero lambdas pts
  | cons c0 rest =>
    simp only [List.length_cons] at hLen
    simp only [evalShifted, ringPow, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [ringDot_map_add, ringDot_map_scale, hZero, LawfulCommRing.mul_one,
        ringDot_evalShifted_tail_zero lambdas pts t hHigher rest 1 (by omega) (by omega),
        LawfulCommRing.add_zero]

/-- Multi-session real vs ideal execution across `S` concurrent `(pk_s, sk_s, Z_s)` sessions. -/
def execMultiRealSig {PK SK Msg Sig : Type}
    (S_sig : AbstractSigScheme PK SK Msg Sig) : List (PK × SK × UcSigEnv PK Msg Sig) → List Bool
  | [] => []
  | (pk, sk, Z) :: rest => execRealSig S_sig pk sk Z :: execMultiRealSig S_sig rest

def execMultiIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S_sig : AbstractSigScheme PK SK Msg Sig) : List (PK × SK × UcSigEnv PK Msg Sig) → List Bool
  | [] => []
  | (pk, sk, Z) :: rest => execIdealSig S_sig pk sk [] Z :: execMultiIdealSig S_sig rest

/-- **Explicit `S`-Session UC Realization & Hybrid Telescope (`multi_session_uc_realizes`)**:
    (1) Across any `S`-session bundle `sessions`, multi-session real execution matches `idealSig`
        iff NO individual session produces an EUF-CMA forgery; and
    (2) Quantitatively across `S` adjacent hybrids, `|score(0) - score(S)| ≤ S * eps`! -/
theorem multi_session_uc_realizes {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S_sig : AbstractSigScheme PK SK Msg Sig) :
    (∀ (sessions : List (PK × SK × UcSigEnv PK Msg Sig)),
      execMultiRealSig S_sig sessions = execMultiIdealSig S_sig sessions ∨
      ∃ pk sk Z mStar sigStar,
        (pk, sk, Z) ∈ sessions ∧
        mStar ∉ signedBeforeForgery S_sig pk sk [] Z ∧
        S_sig.verify pk mStar sigStar = true) ∧
    (∀ (S eps : Nat) (score : Nat → Nat),
      (∀ i, i < S → natAbsDiff (score i) (score (i + 1)) ≤ eps) →
      natAbsDiff (score 0) (score S) ≤ S * eps) := by
  refine ⟨?_, ?_⟩
  · intro sessions
    induction sessions with
    | nil => exact .inl rfl
    | cons hd rest ih =>
      rcases hd with ⟨pk, sk, Z⟩
      by_cases hHead : execRealSig S_sig pk sk Z = execIdealSig S_sig pk sk [] Z
      · rcases ih with hRestEq | ⟨pk', sk', Z', mStar, sigStar, hMem, hFresh, hVer⟩
        · exact .inl (by simp [execMultiRealSig, execMultiIdealSig, hHead, hRestEq])
        · exact .inr ⟨pk', sk', Z', mStar, sigStar, .tail _ hMem, hFresh, hVer⟩
      · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ := (ucRealizes_iff_eufCma S_sig pk sk).1 Z hHead
        exact .inr ⟨pk, sk, Z, mStar, sigStar, .head _, hFresh, hVer⟩
  · intro S eps score hStep
    induction S with
    | zero => simp [natAbsDiff]
    | succ s ih =>
      have ih' := ih (fun i hi => hStep i (Nat.lt_succ_of_lt hi))
      have hLast := hStep s (Nat.lt_succ_self s)
      have hTri := natAbsDiff_triangle (score 0) (score s) (score (s + 1))
      have hLe := Nat.le_trans hTri (Nat.add_le_add ih' hLast)
      rwa [Nat.succ_mul]

/-- Calling protocol `ρ` wrapping a signature subroutine into a higher-level protocol interface. -/
structure CallingProtocol (HighIn HighOut PK Msg Sig : Type) where
  compileEnv : (HighIn → HighOut → Bool) → HighIn → UcSigEnv PK Msg Sig

/-- **Canetti Universal Composition Theorem (`uc_composition_theorem`)**:
    For ANY calling protocol `ρ` and high-level environment `(inp, post)`, executing `ρ` over the
    real signing protocol agrees with executing `ρ` over `idealSig` unless `ρ`'s induced signature
    environment `ρ.compileEnv post inp` produces an explicit EUF-CMA forgery! -/
theorem uc_composition_theorem {HighIn HighOut PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK)
    (ρ : CallingProtocol HighIn HighOut PK Msg Sig)
    (inp : HighIn) (post : HighIn → HighOut → Bool) :
    let Z := ρ.compileEnv post inp
    execRealSig S pk sk Z = execIdealSig S pk sk [] Z ∨
    (∃ mStar sigStar,
      mStar ∉ signedBeforeForgery S pk sk [] Z ∧
      S.verify pk mStar sigStar = true) := by
  intro Z
  by_cases hEq : execRealSig S pk sk Z = execIdealSig S pk sk [] Z
  · exact .inl hEq
  · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ := (ucRealizes_iff_eufCma S pk sk).1 Z hEq
    exact .inr ⟨mStar, sigStar, hFresh, hVer⟩

end Obend.Crypto.ThresholdMpcUcGames
end
