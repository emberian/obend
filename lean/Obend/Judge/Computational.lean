module
/-
# Obend.Judge.Computational — 0-Axiom Constructive Cryptographic `ComputationalJudge`

Closes Chasm 5 in CIC without `sorry` or custom `axiom`s:
deterministic `check r o c = .ok → Meaning o` is unprovable without axioms for succinct
cryptographic commitments/SNARKs against unbounded adversaries, because collisions and short
lattice kernel vectors exist information-theoretically. Generalizing `Obend.Receipt`'s constructive
collision disjunct (`∨ HashBytes.Collision H`), `ComputationalJudge` replaces axiomatic soundness
with:

1. **Algebraic `AssumptionSet` & Constructive `BreakWitness` (`Type`)**:
   - `.none` (`PEmpty`), `.hashCollision256 H maxBytes` (explicit `HashBytes.CollisionAmong` / `Collision`),
     `.moduleSISShortVec q normBound matrix` (explicit nonzero `z` with `‖z‖_∞ ≤ normBound` and
     `matrix · z ≡ 0 (mod q)`), `.rlweDistinguish q noiseBound matrixA targetB`,
     `.conj a b` (`BreakWitness a ⊕ BreakWitness b`), and `.disj a b` (`BreakWitness a × BreakWitness b`).
2. **Universal `k`-Special-Soundness & `2`-Special-Soundness Constructive Rewinder (`SpecialSoundK`, `SpecialSound2`)**:
   - Deterministically extracts `PSum { w // Rel x w } (BreakWitness assumptions)` from `k` accepting
     transcripts on distinct challenges in `Fin Q`.
   - **Universal Bad-Challenge Counting Bound (`specialSoundK_bad_challenge_count_le`)**: in pure
     finite combinatorics over `Fin Q` with `0` axioms, whenever `(∀ w, ¬ Rel x w)` and
     `Unbroken assumptions`, at most `k - 1` challenges in `Fin Q` can accept (`≤ (k - 1) / Q`).
   - Concrete 2-special-sound instantiations for **Ajtai / Module-SIS** (`sisOpening2SpecialSound`,
     extracting either a short witness or `Δz = z₀ - z₁ ≠ 0` with `‖Δz‖_∞ ≤ 2β` in `ker_q(M)`)
     and **Hash-Committed Linear / Polynomial IOP** (`hashLinear2SpecialSound`, extracting either
     the exact polynomial witness or an explicit `Obend.Digest.HashBytes.Collision H`).
3. **`class ComputationalJudge` & Compositional Combinators**:
   - `CompJudge.both`: conjunction of two cryptographic judges ($\varepsilon = \varepsilon_1 + \varepsilon_2$,
     assumption floor `.conj A₁ A₂`).
   - `CompJudge.dualAssumption`: cross-assumption `DualPCS` combinator accepting iff *both* verifiers
     accept; breaking soundness requires exhibiting **both** `BreakWitness A₁` **and** `BreakWitness A₂`
     simultaneously (`.disj A₁ A₂`), tightening soundness error to $\min(\varepsilon_1, \varepsilon_2)$.
   - `CompJudge.ofDeterministicJudge`: embeds any exact `Obend.Judge` with `assumptions := .none`
     and `soundnessErr := (0, 1)` ($\varepsilon = 0$).
-/
public import Obend.Judge.Class
public import Obend.Digest.HashBytes

public section
namespace Obend.Judge.Computational

open Obend
open Obend.Digest

set_option autoImplicit false
set_option maxHeartbeats 200000

/-! ## 1. Integer Matrix-Vector & Infinity-Norm Primitives for Lattice Reductions -/

/-- Infinity norm `‖v‖_∞ = max_i |v_i|` of an integer vector. -/
def vecInfNorm : List Int → Nat
  | [] => 0
  | x :: xs => max x.natAbs (vecInfNorm xs)

/-- Componentwise subtraction `u - v` of two integer vectors. -/
def vecSub : List Int → List Int → List Int
  | x :: xs, y :: ys => (x - y) :: vecSub xs ys
  | _, _ => []

/-- Componentwise addition `u + v` of two integer vectors. -/
def vecAdd : List Int → List Int → List Int
  | x :: xs, y :: ys => (x + y) :: vecAdd xs ys
  | _, _ => []

/-- Standard dot product `⟨row, v⟩` over `Int`. -/
def dotProd : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dotProd as bs
  | _, _ => 0

/-- Matrix-vector product `M · v` over `Int`. -/
def matVecMul (matrix : List (List Int)) (v : List Int) : List Int :=
  matrix.map (fun row => dotProd row v)

/-- Decidable check that `M · z ≡ 0 (mod q)` entrywise with matching column widths. -/
def matVecModZero (q : Nat) (matrix : List (List Int)) (z : List Int) : Bool :=
  decide (0 < q) &&
  matrix.all (fun row => decide (row.length = z.length) && decide ((dotProd row z) % (q : Int) = 0))

/-- Decidable check that `u ≡ v (mod q)` entrywise for equal-length integer vectors. -/
def vecCongrMod (q : Nat) : List Int → List Int → Bool
  | x :: xs, y :: ys => decide (x % (q : Int) = y % (q : Int)) && vecCongrMod q xs ys
  | [], [] => true
  | _, _ => false

theorem vecInfNorm_pos_of_ne : ∀ {u v : List Int},
    u.length = v.length → u ≠ v → 0 < vecInfNorm (vecSub u v)
  | [], [], _, hne => False.elim (hne rfl)
  | x :: xs, y :: ys, hlen, hne => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [vecSub, vecInfNorm]
    if hxy : x = y then
      subst hxy
      have hneTail : xs ≠ ys := fun h => hne (by rw [h])
      have ih := vecInfNorm_pos_of_ne hlen hneTail
      omega
    else
      have hpos : 0 < (x - y).natAbs := Int.natAbs_pos.2 (by omega)
      omega

theorem vecInfNorm_sub_le : ∀ (u v : List Int) (β : Nat),
    vecInfNorm u ≤ β → vecInfNorm v ≤ β → vecInfNorm (vecSub u v) ≤ 2 * β
  | [], _, _, _, _ => by simp [vecSub, vecInfNorm]
  | _ :: _, [], _, _, _ => by simp [vecSub, vecInfNorm]
  | x :: xs, y :: ys, β, hu, hv => by
    simp only [vecInfNorm] at hu hv
    have hx : x.natAbs ≤ β := Nat.le_trans (Nat.le_max_left _ _) hu
    have hxs : vecInfNorm xs ≤ β := Nat.le_trans (Nat.le_max_right _ _) hu
    have hy : y.natAbs ≤ β := Nat.le_trans (Nat.le_max_left _ _) hv
    have hys : vecInfNorm ys ≤ β := Nat.le_trans (Nat.le_max_right _ _) hv
    have hdiff : (x - y).natAbs ≤ 2 * β := by omega
    have ih := vecInfNorm_sub_le xs ys β hxs hys
    simp only [vecSub, vecInfNorm]
    exact Nat.max_le.2 ⟨hdiff, ih⟩

theorem vecSub_length : ∀ (u v : List Int), u.length = v.length → (vecSub u v).length = u.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [vecSub, vecSub_length xs ys h]

theorem dotProd_sub : ∀ (row u v : List Int),
    u.length = v.length → dotProd row (vecSub u v) = dotProd row u - dotProd row v
  | [], _, _, _ => by simp [dotProd]
  | _ :: _, [], [], _ => by simp [vecSub, dotProd]
  | r :: rs, x :: xs, y :: ys, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [vecSub, dotProd, dotProd_sub rs xs ys hlen]
    rw [Int.mul_sub]
    omega

private theorem sub_emod_eq_zero_of_emod_eq {a b m : Int} (h : a % m = b % m) :
    (a - b) % m = 0 := by
  rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod]

/-! ## 2. Algebraic `AssumptionSet` & Constructive `BreakWitness` -/

/-- Explicit algebraic lattice/hash assumption floor carried by a `ComputationalJudge`.
    - `.hashCollision256 H maxBytes`: bounded-length byte-hash collision (`maxBytes ≤ 32` in the
      non-compressing `NonPigeonhole` regime; use `.hashCollisionAmong` or `PSum` extractors for
      longer messages!).
    - `.hashCollisionAmong H traceMsgs`: collision pinned to a finite list of executed trace preimages.
    - `.conj a b`: relies on *both* `a` and `b` (breaking either breaks the conjunction).
    - `.disj a b`: relies on *at least one* of `a` or `b` (breaking requires breaking **both**). -/
inductive AssumptionSet where
  | none
  | hashCollision256 (H : HashBytes.Hash) (maxBytes : Nat)
  | hashCollisionAmong (H : HashBytes.Hash) (traceMsgs : List (List UInt8))
  | moduleSISShortVec (q normBound : Nat) (matrix : List (List Int))
  | rlweDistinguish (q noiseBound : Nat) (matrixA : List (List Int)) (targetB : List Int)
  | conj (a b : AssumptionSet)
  | disj (a b : AssumptionSet)

/-- Constructive witness of a 256-bit byte-hash collision on inputs of length `≤ maxBytes`,
    directly projecting to `Obend.Digest.HashBytes.CollisionAmong` and `Collision`. -/
structure HashCollisionWitness (H : HashBytes.Hash) (maxBytes : Nat) where
  msgA : List UInt8
  msgB : List UInt8
  lenA : msgA.length ≤ maxBytes
  lenB : msgB.length ≤ maxBytes
  distinct : msgA ≠ msgB
  sameDigest : HashBytes.ofBE (H msgA) = HashBytes.ofBE (H msgB)
  deriving DecidableEq

/-- Constructive witness of a byte-hash collision pinned to a finite executed trace `domain`.
    Unlike global unbounded collision predicates over `List UInt8` (which are trivially `True` by
    Pigeonhole), `PinnedCollision H domain` is empty (`Unbroken`) on every collision-free trace! -/
structure PinnedCollision (H : HashBytes.Hash) (domain : List (List UInt8)) where
  msgA : List UInt8
  msgB : List UInt8
  memA : msgA ∈ domain
  memB : msgB ∈ domain
  distinct : msgA ≠ msgB
  sameDigest : HashBytes.ofBE (H msgA) = HashBytes.ofBE (H msgB)
  deriving DecidableEq

/-- Every `PinnedCollision` induces `Obend.Digest.HashBytes.CollisionAmong` over `domain` membership. -/
theorem PinnedCollision.toCollisionAmong {H : HashBytes.Hash} {domain : List (List UInt8)}
    (w : PinnedCollision H domain) :
    HashBytes.CollisionAmong H (fun m => m ∈ domain) :=
  ⟨w.msgA, w.msgB, w.memA, w.memB, w.distinct, w.sameDigest⟩

/-- Every `PinnedCollision` induces a bounded `HashCollisionWitness` at `max (msgA.length) (msgB.length)`. -/
def PinnedCollision.toHashCollisionWitness {H : HashBytes.Hash} {domain : List (List UInt8)}
    (w : PinnedCollision H domain) :
    HashCollisionWitness H (max w.msgA.length w.msgB.length) where
  msgA := w.msgA
  msgB := w.msgB
  lenA := Nat.le_max_left _ _
  lenB := Nat.le_max_right _ _
  distinct := w.distinct
  sameDigest := w.sameDigest

/-- Type-valued constructive soundness-or-pinned-collision combinator (`0 Classical`). -/
abbrev ConstructiveCollisionOrSound (P : Prop) (H : HashBytes.Hash) (domain : List (List UInt8)) : Type :=
  PSum (PLift P) (PinnedCollision H domain)

/-- Constructive `0 Classical` equality-or-collision comparator on a concrete two-preimage pair `[m₁, m₂]`. -/
def pinnedCompare (H : HashBytes.Hash) (m₁ m₂ : List UInt8)
    (hSame : HashBytes.ofBE (H m₁) = HashBytes.ofBE (H m₂)) :
    ConstructiveCollisionOrSound (m₁ = m₂) H [m₁, m₂] :=
  if hEq : m₁ = m₂ then
    .inl ⟨hEq⟩
  else
    .inr
      { msgA := m₁
        msgB := m₂
        memA := .head _
        memB := .tail _ (.head _)
        distinct := hEq
        sameDigest := hSame }

/-- Decidable check that all distinct messages in finite executed trace `traceMsgs` have distinct digests. -/
def traceCollisionFree (H : HashBytes.Hash) (traceMsgs : List (List UInt8)) : Bool :=
  traceMsgs.all fun a =>
    traceMsgs.all fun b =>
      decide (HashBytes.ofBE (H a) = HashBytes.ofBE (H b) → a = b)

/-- Every `HashCollisionWitness` induces `Obend.Digest.HashBytes.CollisionAmong` on bounded inputs. -/
theorem HashCollisionWitness.toCollisionAmong {H : HashBytes.Hash} {maxBytes : Nat}
    (w : HashCollisionWitness H maxBytes) :
    HashBytes.CollisionAmong H (fun m => m.length ≤ maxBytes) :=
  ⟨w.msgA, w.msgB, w.lenA, w.lenB, w.distinct, w.sameDigest⟩

/-- Every `HashCollisionWitness` induces `Obend.Digest.HashBytes.Collision H` (matching `Obend.Receipt`). -/
theorem HashCollisionWitness.toCollision {H : HashBytes.Hash} {maxBytes : Nat}
    (w : HashCollisionWitness H maxBytes) :
    HashBytes.Collision H :=
  w.toCollisionAmong.global

/-- Constructive witness breaking homogeneous Module-SIS `(q, normBound, matrix)`:
    a nonzero integer vector `z` with `‖z‖_∞ ≤ normBound` and `matrix · z ≡ 0 (mod q)`. -/
structure SISShortVecWitness (q normBound : Nat) (matrix : List (List Int)) where
  shortVec : List Int
  nonZero : 0 < vecInfNorm shortVec
  shortNorm : vecInfNorm shortVec ≤ normBound
  inKernel : matVecModZero q matrix shortVec = true
  deriving DecidableEq

/-- Constructive witness breaking unique bounded-noise LWE/RLWE decoding `(q, noiseBound, matrixA, targetB)`:
    requires non-degenerate modulus/noise parameters (`0 < q`, `2 * noiseBound < q`), conforming row widths,
    and **two distinct** canonical secret/short-error openings `(secretS, errorE) ≠ (secretS₂, errorE₂)`
    satisfying `0 ≤ s_i < q`, `‖e‖_∞ ≤ noiseBound`, and `A·s + e ≡ b (mod q)`. -/
structure RLWEBreakWitness (q noiseBound : Nat) (matrixA : List (List Int)) (targetB : List Int) where
  modulusPos : 0 < q
  nonPigeonholeNoise : 2 * noiseBound < q
  secretS : List Int
  errorE : List Int
  secretS₂ : List Int
  errorE₂ : List Int
  canonicalS : secretS.all (fun x => decide (0 ≤ x ∧ x < (q : Int))) = true
  canonicalS₂ : secretS₂.all (fun x => decide (0 ≤ x ∧ x < (q : Int))) = true
  colsConsistent : matrixA.all (fun row => decide (row.length = secretS.length ∧ row.length = secretS₂.length)) = true
  rowsConsistent : errorE.length = targetB.length ∧ errorE₂.length = targetB.length
  shortNoise : vecInfNorm errorE ≤ noiseBound
  shortNoise₂ : vecInfNorm errorE₂ ≤ noiseBound
  distinctDecoding : (secretS, errorE) ≠ (secretS₂, errorE₂)
  consistent : vecCongrMod q (vecAdd (matVecMul matrixA secretS) errorE) targetB = true
  consistent₂ : vecCongrMod q (vecAdd (matVecMul matrixA secretS₂) errorE₂) targetB = true
  deriving DecidableEq

/-- Type-valued constructive break witness for an `AssumptionSet`.
    Notice the exact duality:
    - `BreakWitness (.conj a b) = Sum (BreakWitness a) (BreakWitness b)`
    - `BreakWitness (.disj a b) = BreakWitness a × BreakWitness b` -/
@[expose] def BreakWitness : AssumptionSet → Type
  | .none => PEmpty
  | .hashCollision256 H maxBytes => HashCollisionWitness H maxBytes
  | .hashCollisionAmong H traceMsgs => PinnedCollision H traceMsgs
  | .moduleSISShortVec q normBound matrix => SISShortVecWitness q normBound matrix
  | .rlweDistinguish q noiseBound matrixA targetB => RLWEBreakWitness q noiseBound matrixA targetB
  | .conj a b => Sum (BreakWitness a) (BreakWitness b)
  | .disj a b => BreakWitness a × BreakWitness b

/-- Explicit non-compressing / non-pigeonhole parameter regime for an `AssumptionSet`:
    - `.hashCollision256 _ maxBytes`: non-compressing `maxBytes ≤ 32` for 256-bit digests;
    - `.hashCollisionAmong _ traceMsgs`: finite executed trace `traceMsgs.length ≤ 2 ^ 256`;
    - `.moduleSISShortVec q normBound matrix`: integer lattice box `(2 * normBound + 1)^cols ≤ q^rows`;
    - `.rlweDistinguish q noiseBound _ _`: unique-decoding noise regime `2 * noiseBound < q`. -/
@[expose] def NonPigeonhole : AssumptionSet → Prop
  | .none => True
  | .hashCollision256 _ maxBytes => maxBytes ≤ 32
  | .hashCollisionAmong _ traceMsgs => traceMsgs.length ≤ 2 ^ 256
  | .moduleSISShortVec q normBound matrix =>
      (2 * normBound + 1) ^ (matrix.headD []).length ≤ q ^ matrix.length
  | .rlweDistinguish q noiseBound _ _ => 2 * noiseBound < q
  | .conj a b => NonPigeonhole a ∧ NonPigeonhole b
  | .disj a b => NonPigeonhole a ∨ NonPigeonhole b

/-- Proposition that `AssumptionSet` `A` has a constructive break witness. -/
@[expose] def Broken (A : AssumptionSet) : Prop := Nonempty (BreakWitness A)

/-- Proposition that `AssumptionSet` `A` is unbroken in a non-pigeonhole regime:
    enforces `maxBytes ≤ 32` on `.hashCollision256` and `traceMsgs.length ≤ 2 ^ 256` on
    `.hashCollisionAmong`, while reducing definitionally to `¬ Nonempty (SISShortVecWitness ...)`
    on `.moduleSISShortVec` for direct lattice kernel proofs. -/
@[expose] def Unbroken : AssumptionSet → Prop
  | .none => True
  | .hashCollision256 H maxBytes => maxBytes ≤ 32 ∧ ¬ Nonempty (HashCollisionWitness H maxBytes)
  | .hashCollisionAmong H traceMsgs =>
      traceMsgs.length ≤ 2 ^ 256 ∧ ¬ Nonempty (PinnedCollision H traceMsgs)
  | .moduleSISShortVec q normBound matrix => ¬ Nonempty (SISShortVecWitness q normBound matrix)
  | .rlweDistinguish q noiseBound matrixA targetB =>
      ¬ Nonempty (RLWEBreakWitness q noiseBound matrixA targetB)
  | .conj a b => Unbroken a ∧ Unbroken b
  | .disj a b => Unbroken a ∨ Unbroken b

theorem unbroken_none : Unbroken .none := trivial

theorem nonPigeonhole_none : NonPigeonhole .none := trivial

theorem nonPigeonhole_disj_of_or {a b : AssumptionSet}
    (h : NonPigeonhole a ∨ NonPigeonhole b) :
    NonPigeonhole (.disj a b) := h

theorem broken_conj_iff (a b : AssumptionSet) :
    Broken (.conj a b) ↔ Broken a ∨ Broken b := by
  constructor
  · rintro ⟨w | w⟩
    · exact .inl ⟨w⟩
    · exact .inr ⟨w⟩
  · intro h
    cases h with
    | inl ha => obtain ⟨wa⟩ := ha; exact ⟨.inl wa⟩
    | inr hb => obtain ⟨wb⟩ := hb; exact ⟨.inr wb⟩

theorem unbroken_conj_iff (a b : AssumptionSet) :
    Unbroken (.conj a b) ↔ Unbroken a ∧ Unbroken b := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb⟩

theorem broken_disj_iff (a b : AssumptionSet) :
    Broken (.disj a b) ↔ Broken a ∧ Broken b := by
  constructor
  · rintro ⟨⟨wa, wb⟩⟩; exact ⟨⟨wa⟩, ⟨wb⟩⟩
  · rintro ⟨⟨wa⟩, ⟨wb⟩⟩; exact ⟨(wa, wb)⟩

theorem unbroken_disj_of_or {a b : AssumptionSet} (h : Unbroken a ∨ Unbroken b) :
    Unbroken (.disj a b) := h

/-- Structural soundness of `Unbroken` in a `NonPigeonhole` regime:
    any `Unbroken A` accompanied by `NonPigeonhole A` refutes `Broken A`. -/
theorem Unbroken.not_broken {A : AssumptionSet}
    (hNonPig : NonPigeonhole A) (hUnbroken : Unbroken A) : ¬ Broken A := by
  intro hBrk
  have hTriv : True := let _ := hNonPig; trivial
  clear hNonPig hTriv
  induction A with
  | none => rcases hBrk with ⟨w⟩; cases w
  | hashCollision256 _ _ => exact hUnbroken.2 hBrk
  | hashCollisionAmong _ _ => exact hUnbroken.2 hBrk
  | moduleSISShortVec _ _ _ => exact hUnbroken hBrk
  | rlweDistinguish _ _ _ _ => exact hUnbroken hBrk
  | conj a b iha ihb =>
      exact ((broken_conj_iff a b).1 hBrk).elim (iha hUnbroken.1) (ihb hUnbroken.2)
  | disj a b iha ihb =>
      rcases (broken_disj_iff a b).1 hBrk with ⟨ha, hb⟩
      exact hUnbroken.elim (fun una => iha una ha) (fun unb => ihb unb hb)

/-- Decidable `traceCollisionFree` establishes `Unbroken (.hashCollisionAmong H traceMsgs)`
    whenever `traceMsgs.length ≤ 2 ^ 256`. -/
theorem unbroken_hashCollisionAmong_of_traceCollisionFree
    (H : HashBytes.Hash) (traceMsgs : List (List UInt8))
    (hLen : traceMsgs.length ≤ 2 ^ 256)
    (hFree : traceCollisionFree H traceMsgs = true) :
    Unbroken (.hashCollisionAmong H traceMsgs) := by
  refine ⟨hLen, ?_⟩
  rintro ⟨w⟩
  simp only [traceCollisionFree, List.all_eq_true, decide_eq_true_eq] at hFree
  exact w.distinct (hFree w.msgA w.memA w.msgB w.memB w.sameDigest)

private theorem length_eraseFirst {α : Type} [DecidableEq α] :
    ∀ {y : α} {ys : List α}, y ∈ ys → (ys.erase y).length + 1 = ys.length
  | _, [], h => by cases h
  | y, z :: zs, h => by
    simp only [List.erase_cons]
    if hyz : z == y then
      have hzEq : z = y := beq_iff_eq.1 hyz
      simp [hzEq]
    else
      have hne : z ≠ y := fun heq => hyz (beq_iff_eq.2 heq)
      cases h with
      | head => exact False.elim (hne rfl)
      | tail _ hm =>
        have ih := length_eraseFirst hm
        simp [hyz, ih]

private theorem mem_erase_of_ne {α : Type} [DecidableEq α] {a b : α} (hne : a ≠ b) :
    ∀ {ys : List α}, a ∈ ys → a ∈ ys.erase b
  | [], h => h
  | z :: zs, h => by
    simp only [List.erase_cons]
    if hzb : z == b then
      have hzEq : z = b := beq_iff_eq.1 hzb
      cases h with
      | head => exact False.elim (hne hzEq)
      | tail _ hm =>
        have hm' : a ∈ zs := hm
        simpa [hzb, hzEq] using hm'
    else
      have hneZB : z ≠ b := fun heq => hzb (beq_iff_eq.2 heq)
      cases h with
      | head => simp [hzb, hneZB]
      | tail _ hm =>
        have ih : a ∈ zs.erase b := mem_erase_of_ne hne hm
        simp [hzb, ih]

/-- **Constructive Finite Pigeonhole Principle (`0` axioms)**:
    Any duplicate-free list `xs` mapped into a strictly shorter codomain list `ys` (`ys.length < xs.length`)
    admits two distinct `a, b ∈ xs` with `f a = f b`. -/
theorem list_pigeonhole_of_lt {α β : Type} [DecidableEq α] [DecidableEq β] :
    ∀ (xs : List α) (ys : List β) (f : α → β),
      xs.Nodup → (∀ x ∈ xs, f x ∈ ys) → ys.length < xs.length →
      ∃ a ∈ xs, ∃ b ∈ xs, a ≠ b ∧ f a = f b
  | [], _, _, _, _, hlt => by simp at hlt
  | x :: xs, ys, f, .cons hxNotMem hNd, hMap, hlt => by
    cases hHit : xs.any (fun x' => decide (f x' = f x)) with
    | true =>
      obtain ⟨x', hx', hEqB⟩ := List.any_eq_true.1 hHit
      have hEq : f x' = f x := of_decide_eq_true hEqB
      exact ⟨x, .head _, x', .tail _ hx', fun h => hxNotMem x' hx' h, hEq.symm⟩
    | false =>
      have hSubMap : ∀ x' ∈ xs, f x' ∈ ys.erase (f x) := by
        intro x' hx'
        have hNeF : f x' ≠ f x := by
          intro hEq
          have hTrue : xs.any (fun z => decide (f z = f x)) = true :=
            List.any_eq_true.2 ⟨x', hx', decide_eq_true hEq⟩
          rw [hHit] at hTrue
          cases hTrue
        exact mem_erase_of_ne hNeF (hMap x' (.tail _ hx'))
      have hEraseLen := length_eraseFirst (hMap x (.head _))
      have hSubLt : (ys.erase (f x)).length < xs.length := by
        simp only [List.length_cons] at hlt; omega
      obtain ⟨a, ha, b, hb, hne, hfeq⟩ := list_pigeonhole_of_lt xs (ys.erase (f x)) f hNd hSubMap hSubLt
      exact ⟨a, .tail _ ha, b, .tail _ hb, hne, hfeq⟩

/-- **Explicit Pigeonhole Refutation of Compressing `.hashCollision256` (`hashCollision256_broken_of_pigeonhole`)**:
    Whenever a set `xs` of pairwise-distinct inputs of length `≤ maxBytes` maps into a digest image `digests`
    with `digests.length < xs.length` (e.g., `256^33 > 2^256` for `maxBytes ≥ 33` on any 32-byte digest `H`),
    `.hashCollision256 H maxBytes` is **constructively `Broken`**! -/
theorem hashCollision256_broken_of_pigeonhole
    (H : HashBytes.Hash) (maxBytes : Nat)
    (xs : List (List UInt8)) (digests : List Nat)
    (hNd : xs.Nodup)
    (hLen : ∀ m ∈ xs, m.length ≤ maxBytes)
    (hImg : ∀ m ∈ xs, HashBytes.ofBE (H m) ∈ digests)
    (hComp : digests.length < xs.length) :
    Broken (.hashCollision256 H maxBytes) := by
  obtain ⟨a, ha, b, hb, hne, hsame⟩ :=
    list_pigeonhole_of_lt xs digests (fun m => HashBytes.ofBE (H m)) hNd hImg hComp
  exact ⟨⟨a, b, hLen a ha, hLen b hb, hne, hsame⟩⟩

/-! ## 3. Exact Rational Soundness Error Arithmetic (`RatErr := Nat × Nat`) -/

/-- Non-negative rational soundness bound `(num, den)` representing `num / den` (`0 < den`). -/
abbrev RatErr := Nat × Nat

/-- Exact zero soundness error `0 / 1`. -/
@[expose] def ratZero : RatErr := (0, 1)

/-- Rational addition `(n₁ / d₁) + (n₂ / d₂) = (n₁ d₂ + n₂ d₁) / (d₁ d₂)` (union bound). -/
@[expose] def ratAdd (e₁ e₂ : RatErr) : RatErr :=
  (e₁.1 * e₂.2 + e₂.1 * e₁.2, e₁.2 * e₂.2)

/-- Rational minimum `min(e₁, e₂)` via cross-multiplied comparison (tightened dual bound). -/
@[expose] def ratMin (e₁ e₂ : RatErr) : RatErr :=
  if e₁.1 * e₂.2 ≤ e₂.1 * e₁.2 then e₁ else e₂

/-- Exact cross-multiplied rational inequality `n₁ / d₁ ≤ n₂ / d₂` (for positive denominators). -/
@[expose] def ratLe (e₁ e₂ : RatErr) : Prop :=
  e₁.1 * e₂.2 ≤ e₂.1 * e₁.2

theorem ratAdd_den_pos {e₁ e₂ : RatErr} (h₁ : 0 < e₁.2) (h₂ : 0 < e₂.2) :
    0 < (ratAdd e₁ e₂).2 :=
  Nat.mul_pos h₁ h₂

theorem ratMin_den_pos {e₁ e₂ : RatErr} (h₁ : 0 < e₁.2) (h₂ : 0 < e₂.2) :
    0 < (ratMin e₁ e₂).2 := by
  unfold ratMin
  split
  · exact h₁
  · exact h₂

theorem ratMin_le_left (e₁ e₂ : RatErr) : ratLe (ratMin e₁ e₂) e₁ := by
  unfold ratMin ratLe
  split
  · exact Nat.le_refl _
  · omega

theorem ratMin_le_right (e₁ e₂ : RatErr) : ratLe (ratMin e₁ e₂) e₂ := by
  unfold ratMin ratLe
  split
  · assumption
  · exact Nat.le_refl _

/-! ## 4. Finite Challenge Enumeration & Universal `k`-Special-Soundness Rewinder + Counting Bound -/

/-- Canonical duplicate-free enumeration `[0, 1, ..., Q - 1]` of `Fin Q`. -/
def finEnum : (Q : Nat) → List (Fin Q)
  | 0 => []
  | Q + 1 => ⟨0, Nat.zero_lt_succ Q⟩ :: (finEnum Q).map Fin.succ

theorem finEnum_length (Q : Nat) : (finEnum Q).length = Q := by
  induction Q with
  | zero => rfl
  | succ n ih => simp [finEnum, ih]

theorem mem_finEnum {Q : Nat} (x : Fin Q) : x ∈ finEnum Q := by
  induction Q with
  | zero => exact Fin.elim0 x
  | succ n ih =>
    rcases x with ⟨val, isLt⟩
    cases val with
    | zero => exact List.Mem.head _
    | succ k =>
      apply List.Mem.tail
      exact List.mem_map.2 ⟨⟨k, Nat.lt_of_succ_lt_succ isLt⟩, ih _, rfl⟩

private theorem nodup_map_of_inj {α β : Type} {f : α → β}
    (hinj : ∀ x y, f x = f y → x = y) : ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail =>
    .cons
      (fun b hb heq => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        exact hrel y hy (hinj _ _ heq))
      (nodup_map_of_inj hinj htail)

private theorem mem_of_mem_filter_aux {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | [], h => by cases h
  | a :: as, h => by
    simp only [List.filter] at h
    split at h
    · cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_of_mem_filter_aux hm)
    · exact .tail _ (mem_of_mem_filter_aux h)

private theorem pred_of_mem_filter_aux {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → p x = true
  | [], h => by cases h
  | a :: as, h => by
    simp only [List.filter] at h
    split at h
    · rename_i hpa
      cases h with
      | head => exact hpa
      | tail _ hm => exact pred_of_mem_filter_aux hm
    · exact pred_of_mem_filter_aux h

private theorem nodup_filter_aux {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]
    split
    · exact .cons (fun b hb => hrel b (mem_of_mem_filter_aux hb)) (nodup_filter_aux p htail)
    · exact nodup_filter_aux p htail

private theorem mem_of_mem_take_aux {α : Type} {x : α} :
    ∀ {k : Nat} {l : List α}, x ∈ l.take k → x ∈ l
  | 0, _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: as, h => by
    simp only [List.take] at h
    cases h with
    | head => exact .head _
    | tail _ hm => exact .tail _ (mem_of_mem_take_aux hm)

private theorem nodup_take_aux {α : Type} :
    ∀ (k : Nat) {l : List α}, l.Nodup → (l.take k).Nodup
  | 0, _, _ => .nil
  | _ + 1, [], _ => .nil
  | k + 1, _ :: _, .cons hrel htail =>
    .cons (fun b hb => hrel b (mem_of_mem_take_aux hb)) (nodup_take_aux k htail)

theorem finEnum_nodup (Q : Nat) : (finEnum Q).Nodup := by
  induction Q with
  | zero => exact .nil
  | succ n ih =>
    refine .cons (fun b hb heq => ?_) (nodup_map_of_inj (fun x y h => Fin.ext (by
      have hv := congrArg Fin.val h; dsimp at hv; omega)) ih)
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hb
    have hv := congrArg Fin.val heq
    dsimp at hv
    omega

/-- **Universal `k`-Special-Soundness Protocol (`SpecialSoundK`)**:
    Given `k` accepting transcripts sharing statement `x` and commitment `cm` on pairwise-distinct
    challenges in `Fin Q`, `extractOrBreak` deterministically computes either a valid witness
    `{ w : Wit // Rel x w }` or a constructive `BreakWitness assumptions`. -/
structure SpecialSoundK (Stmt Wit Commit Resp : Type) (Q k : Nat) where
  hk : 1 ≤ k
  Rel : Stmt → Wit → Prop
  assumptions : AssumptionSet
  accept : Stmt → Commit → Fin Q → Resp → Bool
  extractOrBreak :
    ∀ (x : Stmt) (cm : Commit) (trs : List (Fin Q × Resp)),
      trs.length = k →
      (trs.map Prod.fst).Nodup →
      (∀ p : Fin Q × Resp, p ∈ trs → accept x cm p.1 p.2 = true) →
      PSum { w : Wit // Rel x w } (BreakWitness assumptions)

/-- **Universal `2`-Special-Soundness Protocol (`SpecialSound2`)**:
    Given two accepting transcripts `(ch₁, z₁)` and `(ch₂, z₂)` sharing commitment `cm` on distinct
    challenges `ch₁ ≠ ch₂`, deterministically computes either `{ w : Wit // Rel x w }` or a
    `BreakWitness assumptions`. -/
structure SpecialSound2 (Stmt Wit Commit Resp : Type) (Q : Nat) where
  Rel : Stmt → Wit → Prop
  assumptions : AssumptionSet
  accept : Stmt → Commit → Fin Q → Resp → Bool
  extractOrBreak2 :
    ∀ (x : Stmt) (cm : Commit) (ch₁ ch₂ : Fin Q) (z₁ z₂ : Resp),
      ch₁ ≠ ch₂ →
      accept x cm ch₁ z₁ = true →
      accept x cm ch₂ z₂ = true →
      PSum { w : Wit // Rel x w } (BreakWitness assumptions)

/-- Canonical embedding of any `SpecialSound2` protocol into `SpecialSoundK` (`k = 2`). -/
def SpecialSound2.toSpecialSoundK {Stmt Wit Commit Resp : Type} {Q : Nat}
    (P : SpecialSound2 Stmt Wit Commit Resp Q) :
    SpecialSoundK Stmt Wit Commit Resp Q 2 where
  hk := by decide
  Rel := P.Rel
  assumptions := P.assumptions
  accept := P.accept
  extractOrBreak x cm trs hLen hNodup hAcc :=
    match trs, hLen, hNodup, hAcc with
    | [p₁, p₂], _, hNd, hAcc =>
      have hNe : p₁.1 ≠ p₂.1 := by
        cases hNd with
        | cons hRel _ => exact hRel p₂.1 (.head _)
      P.extractOrBreak2 x cm p₁.1 p₂.1 p₁.2 p₂.2
        hNe
        (hAcc p₁ (.head _))
        (hAcc p₂ (.tail _ (.head _)))

/-- All challenges in `Fin Q` on which deterministic prover strategy `respOf` makes `P.accept` return `true`. -/
def acceptingChallenges {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp) : List (Fin Q) :=
  (finEnum Q).filter (fun ch => P.accept x cm ch (respOf ch))

theorem mem_acceptingChallenges_iff {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp) (ch : Fin Q) :
    ch ∈ acceptingChallenges P x cm respOf ↔ P.accept x cm ch (respOf ch) = true := by
  unfold acceptingChallenges
  constructor
  · exact pred_of_mem_filter_aux
  · intro hAcc
    exact List.mem_filter.2 ⟨mem_finEnum ch, hAcc⟩

/-- **Universal `k`-Special-Sound Constructive Rewinder (`rewindStrategy`)**:
    Whenever a prover strategy `respOf : Fin Q → Resp` succeeds on at least `k` challenges in `Fin Q`,
    taking the first `k` accepting challenges deterministically extracts either a valid witness `w`
    for `P.Rel x w` OR an explicit `BreakWitness P.assumptions`! -/
def SpecialSoundK.rewindStrategy {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp)
    (hGe : k ≤ (acceptingChallenges P x cm respOf).length) :
    PSum { w : Wit // P.Rel x w } (BreakWitness P.assumptions) :=
  let chs := (acceptingChallenges P x cm respOf).take k
  let trs := chs.map (fun ch => (ch, respOf ch))
  have hMapFst : trs.map Prod.fst = chs := by
    simp [trs, List.map_map]
    exact List.map_id chs
  have hLen : trs.length = k := by
    simp [trs, chs, List.length_take, Nat.min_eq_left hGe]
  have hNodup : (trs.map Prod.fst).Nodup := by
    rw [hMapFst]
    exact nodup_take_aux k (nodup_filter_aux _ (finEnum_nodup Q))
  have hAcc : ∀ p : Fin Q × Resp, p ∈ trs → P.accept x cm p.1 p.2 = true := by
    intro p hp
    obtain ⟨ch, hMemTake, rfl⟩ := List.mem_map.1 hp
    dsimp only
    have hMemFilter : ch ∈ acceptingChallenges P x cm respOf := mem_of_mem_take_aux hMemTake
    exact (mem_acceptingChallenges_iff P x cm respOf ch).1 hMemFilter
  P.extractOrBreak x cm trs hLen hNodup hAcc

/-- **Unconditional Constructive `k`-Special-Soundness Dichotomy (`specialSoundK_count_or_break`)**:
    With **zero** cryptographic assumptions (`0` axioms, `0 Classical`), whenever `x` has no valid
    witness (`∀ w, ¬ P.Rel x w`), either at most `k - 1` challenges in `Fin Q` accept OR deterministic
    rewinding constructively outputs an explicit `BreakWitness P.assumptions`! -/
def specialSoundK_count_or_break
    {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp)
    (hFalse : ∀ w : Wit, ¬ P.Rel x w) :
    PSum (PLift ((acceptingChallenges P x cm respOf).length ≤ k - 1))
         (BreakWitness P.assumptions) :=
  if hLt : (acceptingChallenges P x cm respOf).length < k then
    .inl ⟨by have hk := P.hk; omega⟩
  else
    have hGe : k ≤ (acceptingChallenges P x cm respOf).length := Nat.le_of_not_lt hLt
    match P.rewindStrategy x cm respOf hGe with
    | .inl hw => False.elim (hFalse hw.1 hw.2)
    | .inr brk => .inr brk

/-- **Unconditional Constructive 2-Special-Soundness Dichotomy (`specialSound2_count_or_break`)**:
    With **zero** cryptographic assumptions, whenever `∀ w, ¬ P.Rel x w`, either at most `1` challenge
    in `Fin Q` accepts OR rewinding constructively outputs `BreakWitness P.assumptions`. -/
def specialSound2_count_or_break
    {Stmt Wit Commit Resp : Type} {Q : Nat}
    (P : SpecialSound2 Stmt Wit Commit Resp Q)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp)
    (hFalse : ∀ w : Wit, ¬ P.Rel x w) :
    PSum (PLift ((acceptingChallenges P.toSpecialSoundK x cm respOf).length ≤ 1))
         (BreakWitness P.assumptions) :=
  specialSoundK_count_or_break P.toSpecialSoundK x cm respOf hFalse

/-- **Universal `k`-Special-Soundness Bad-Challenge Counting Bound** (0 axioms, pure finite combinatorics):
    Whenever `x` has no valid witness (`∀ w, ¬ P.Rel x w`) and `P.assumptions` is both `NonPigeonhole`
    and `Unbroken`, **at most `k - 1` challenges** in `Fin Q` can accept for any `cm` and `respOf`! -/
theorem specialSoundK_bad_challenge_count_le
    {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp)
    (hFalse : ∀ w : Wit, ¬ P.Rel x w)
    (hNonPig : NonPigeonhole P.assumptions)
    (hUnbroken : Unbroken P.assumptions) :
    (acceptingChallenges P x cm respOf).length ≤ k - 1 := by
  cases specialSoundK_count_or_break P x cm respOf hFalse with
  | inl hBound => exact hBound.down
  | inr hBrk => exact False.elim (Unbroken.not_broken hNonPig hUnbroken ⟨hBrk⟩)

/-- **Exact Rational Soundness Bound `(k - 1) / Q` for `SpecialSoundK`**:
    Under `∀ w, ¬ P.Rel x w`, `NonPigeonhole P.assumptions`, and `Unbroken P.assumptions`, the accepting
    fraction `(acceptCount, Q)` satisfies `ratLe (acceptCount, Q) (k - 1, Q)`. -/
theorem specialSoundK_rational_bound
    {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp)
    (hFalse : ∀ w : Wit, ¬ P.Rel x w)
    (hNonPig : NonPigeonhole P.assumptions)
    (hUnbroken : Unbroken P.assumptions) :
    ratLe ((acceptingChallenges P x cm respOf).length, Q) (k - 1, Q) := by
  unfold ratLe
  exact Nat.mul_le_mul_right Q
    (specialSoundK_bad_challenge_count_le P x cm respOf hFalse hNonPig hUnbroken)

/-- **2-Special-Soundness Bad-Challenge Bound (`≤ 1` accepting challenge out of `Q`)**:
    Under `∀ w, ¬ P.Rel x w`, `NonPigeonhole P.assumptions`, and `Unbroken P.assumptions`,
    at most **1** challenge in `Fin Q` accepts! -/
theorem specialSound2_bad_challenge_count_le
    {Stmt Wit Commit Resp : Type} {Q : Nat}
    (P : SpecialSound2 Stmt Wit Commit Resp Q)
    (x : Stmt) (cm : Commit) (respOf : Fin Q → Resp)
    (hFalse : ∀ w : Wit, ¬ P.Rel x w)
    (hNonPig : NonPigeonhole P.assumptions)
    (hUnbroken : Unbroken P.assumptions) :
    (acceptingChallenges P.toSpecialSoundK x cm respOf).length ≤ 1 :=
  specialSoundK_bad_challenge_count_le P.toSpecialSoundK x cm respOf hFalse hNonPig hUnbroken

/-! ## 5. Concrete 2-Special-Sound Constructive Extractors (Ajtai-SIS & Hash-Committed IOP) -/

/-- Statement for an Ajtai / Module-SIS 2-round committed opening protocol:
    proves knowledge of a short integer vector `v` (`v.length = numCols`, `‖v‖_∞ ≤ beta`) committed
    under `matrix · v ≡ cm (mod q)` that simultaneously satisfies both round predicates `check0` and `check1`
    (e.g. linear relation `check0` and binary/range constraint `check1`). -/
structure SISOpeningStmt where
  numCols : Nat
  check0 : List Int → Bool
  check1 : List Int → Bool

/--Decidable single-challenge verifier for the Ajtai-SIS 2-special-sound protocol over `Fin 2`. -/
def sisOpeningAccept (q beta : Nat) (matrix : List (List Int))
    (x : SISOpeningStmt) (cm : List Int) (ch : Fin 2) (z : List Int) : Bool :=
  decide (0 < q) &&
  decide (z.length = x.numCols) &&
  decide (vecInfNorm z ≤ beta) &&
  matrix.all (fun row => decide (row.length = x.numCols)) &&
  vecCongrMod q (matVecMul matrix z) cm &&
  (if ch.val == 0 then x.check0 z else x.check1 z)

/-- True witness relation for `sisOpeningAccept`: `z` is short, validly opens `cm` under `matrix`,
    and satisfies **both** `check0` and `check1`. -/
def SISOpeningRel (q beta : Nat) (matrix : List (List Int))
    (x : SISOpeningStmt) (cm : List Int) (z : List Int) : Prop :=
  0 < q ∧ z.length = x.numCols ∧ vecInfNorm z ≤ beta ∧
  (∀ row, row ∈ matrix → row.length = x.numCols) ∧
  vecCongrMod q (matVecMul matrix z) cm = true ∧
  x.check0 z = true ∧ x.check1 z = true

private theorem matVecModZero_of_congr_eq
    {q cols : Nat} {u v cm : List Int}
    (hq : 0 < q) (hu : u.length = cols) (hv : v.length = cols) :
    ∀ {matrix : List (List Int)},
      (∀ row, row ∈ matrix → row.length = cols) →
      vecCongrMod q (matVecMul matrix u) cm = true →
      vecCongrMod q (matVecMul matrix v) cm = true →
      matVecModZero q matrix (vecSub u v) = true
  | [], _, _, _ => by simp [matVecModZero, hq]
  | row :: rows, hRows, hCu, hCv => by
    cases cm with
    | nil => simp [matVecMul, vecCongrMod] at hCu
    | cons c cs =>
      simp only [matVecMul, List.map_cons, vecCongrMod, Bool.and_eq_true, decide_eq_true_eq] at hCu hCv
      have hRowLen : row.length = cols := hRows row (.head _)
      have hSubLen : (vecSub u v).length = cols := by
        rw [vecSub_length u v (hu.trans hv.symm), hu]
      have hDot : (dotProd row (vecSub u v)) % (q : Int) = 0 := by
        rw [dotProd_sub row u v (hu.trans hv.symm)]
        exact sub_emod_eq_zero_of_emod_eq (hCu.1.trans hCv.1.symm)
      have ih := matVecModZero_of_congr_eq hq hu hv (fun r hr => hRows r (.tail _ hr)) hCu.2 hCv.2
      simp only [matVecModZero, Bool.and_eq_true, decide_eq_true_eq, List.all_cons] at ih ⊢
      exact ⟨hq, ⟨hRowLen.trans hSubLen.symm, hDot⟩, ih.2⟩

/-- **Constructive 2-Special-Sound Extractor for Ajtai / Module-SIS (`sisOpening2SpecialSound`)**:
    Given two accepting transcripts `(ch₁, z₁)` and `(ch₂, z₂)` with `ch₁ ≠ ch₂` sharing commitment `cm`:
    - If `z₁ = z₂`, extracts the valid short witness `z₁` satisfying both `check0` and `check1`.
    - If `z₁ ≠ z₂`, extracts the nonzero difference vector `Δz = z₁ - z₂` with `‖Δz‖_∞ ≤ 2β` and
      `matrix · Δz ≡ 0 (mod q)`, constructively breaking `.moduleSISShortVec q (2 * beta) matrix`! -/
def sisOpening2SpecialSound (q beta : Nat) (matrix : List (List Int)) (cm : List Int) :
    SpecialSound2 SISOpeningStmt (List Int) PUnit (List Int) 2 where
  Rel x z := SISOpeningRel q beta matrix x cm z
  assumptions := .moduleSISShortVec q (2 * beta) matrix
  accept x _ ch z := sisOpeningAccept q beta matrix x cm ch z
  extractOrBreak2 x _ ch₁ ch₂ z₁ z₂ hNe hAcc₁ hAcc₂ :=
    if hEqZ : z₁ = z₂ then
      .inl ⟨z₁, by
        subst hEqZ
        simp only [sisOpeningAccept, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hAcc₁ hAcc₂
        rcases hAcc₁ with ⟨⟨⟨⟨⟨hq, hLen₁⟩, hNorm₁⟩, hRows⟩, hCongr₁⟩, hChk₁⟩
        rcases hAcc₂ with ⟨_, hChk₂⟩
        have hBoth : x.check0 z₁ = true ∧ x.check1 z₁ = true := by
          rcases ch₁ with ⟨v₁, lt₁⟩; rcases ch₂ with ⟨v₂, lt₂⟩
          have hNeVal : v₁ ≠ v₂ := fun h => hNe (Fin.ext h)
          rcases (by omega : (v₁ = 0 ∧ v₂ = 1) ∨ (v₁ = 1 ∧ v₂ = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hChk₁, hChk₂⟩
          · exact ⟨hChk₂, hChk₁⟩
        exact ⟨hq, hLen₁, hNorm₁, hRows, hCongr₁, hBoth⟩⟩
    else
      have hFacts :
          0 < vecInfNorm (vecSub z₁ z₂) ∧
          vecInfNorm (vecSub z₁ z₂) ≤ 2 * beta ∧
          matVecModZero q matrix (vecSub z₁ z₂) = true := by
        simp only [sisOpeningAccept, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hAcc₁ hAcc₂
        rcases hAcc₁ with ⟨⟨⟨⟨⟨hq, hLen₁⟩, hNorm₁⟩, hRows⟩, hCongr₁⟩, _⟩
        rcases hAcc₂ with ⟨⟨⟨⟨⟨_, hLen₂⟩, hNorm₂⟩, _⟩, hCongr₂⟩, _⟩
        exact ⟨vecInfNorm_pos_of_ne (hLen₁.trans hLen₂.symm) hEqZ,
               vecInfNorm_sub_le z₁ z₂ beta hNorm₁ hNorm₂,
               matVecModZero_of_congr_eq hq hLen₁ hLen₂ hRows hCongr₁ hCongr₂⟩
      .inr
        { shortVec := vecSub z₁ z₂
          nonZero := hFacts.1
          shortNorm := hFacts.2.1
          inKernel := hFacts.2.2 }

/-- Statement for a Hash-Committed Degree-1 Polynomial / Linear IOP over arbitrary challenge space `Fin Q`:
    prover commits via 256-bit byte hash `H` (`cm = HashBytes.ofBE (H payload)`) to a payload encoding
    linear coefficients `(c₀, c₁ : Int)` claiming `c₀ = targetC0 ∧ c₁ = targetC1`. -/
structure HashLinearStmt where
  targetC0 : Int
  targetC1 : Int
  commitVal : Nat

/-- Response in the Hash-Committed Linear IOP: byte opening `payload` (`length ≤ maxBytes`)
    decoded via `decodeCoeffs : List UInt8 → Int × Int`. -/
def hashLinearAccept (H : HashBytes.Hash) (maxBytes Q : Nat)
    (decodeCoeffs : List UInt8 → Int × Int)
    (x : HashLinearStmt) (_ : PUnit) (ch : Fin Q) (payload : List UInt8) : Bool :=
  let (c₀, c₁) := decodeCoeffs payload
  decide (payload.length ≤ maxBytes) &&
  decide (HashBytes.ofBE (H payload) = x.commitVal) &&
  decide (c₀ + (ch.val : Int) * c₁ = x.targetC0 + (ch.val : Int) * x.targetC1)

/-- True witness relation for `hashLinearAccept`: `payload` is a valid bounded hash opening whose
    decoded polynomial `(c₀, c₁)` equals `(targetC0, targetC1)`. -/
def HashLinearRel (H : HashBytes.Hash) (maxBytes : Nat)
    (decodeCoeffs : List UInt8 → Int × Int)
    (x : HashLinearStmt) (payload : List UInt8) : Prop :=
  payload.length ≤ maxBytes ∧
  HashBytes.ofBE (H payload) = x.commitVal ∧
  decodeCoeffs payload = (x.targetC0, x.targetC1)

/-- **Constructive 2-Special-Sound Extractor for Non-Compressing Hash-Committed Linear IOP (`hashLinear2SpecialSound`)**:
    Over **any** challenge space `Fin Q` in the non-compressing preimage regime (`maxBytes ≤ 32`):
    - If `payload₁ ≠ payload₂`, both hash under `H` to `x.commitVal`, constructively producing a
      `HashCollisionWitness H maxBytes` (and hence `Obend.Digest.HashBytes.Collision H`)!
    - If `payload₁ = payload₂`, subtracting the two linear evaluations at `ch₁ ≠ ch₂` proves
      `decodeCoeffs payload₁ = (x.targetC0, x.targetC1)` via `Int.mul_eq_zero`! -/
def hashLinear2SpecialSound (H : HashBytes.Hash) (maxBytes Q : Nat)
    (decodeCoeffs : List UInt8 → Int × Int)
    (hNonPig : maxBytes ≤ 32 := by decide) :
    SpecialSound2 HashLinearStmt (List UInt8) PUnit (List UInt8) Q where
  Rel x payload := HashLinearRel H maxBytes decodeCoeffs x payload
  assumptions := .hashCollision256 H maxBytes
  accept x u ch payload := hashLinearAccept H maxBytes Q decodeCoeffs x u ch payload
  extractOrBreak2 x _ ch₁ ch₂ p₁ p₂ hNe hAcc₁ hAcc₂ :=
    let _ : maxBytes ≤ 32 := hNonPig
    if hEqP : p₁ = p₂ then
      .inl ⟨p₁, by
        subst hEqP
        simp only [hashLinearAccept, Bool.and_eq_true, decide_eq_true_eq] at hAcc₁ hAcc₂
        rcases hAcc₁ with ⟨⟨hLen₁, hDig₁⟩, hEval₁⟩
        rcases hAcc₂ with ⟨_, hEval₂⟩
        have hNeVal : (ch₁.val : Int) - (ch₂.val : Int) ≠ 0 := by
          intro hZero; apply hNe; apply Fin.ext; omega
        let c := decodeCoeffs p₁
        have hSub : ((ch₁.val : Int) - (ch₂.val : Int)) * (c.2 - x.targetC1) = 0 := by
          have e1 : c.1 + (ch₁.val : Int) * c.2 = x.targetC0 + (ch₁.val : Int) * x.targetC1 := hEval₁
          have e2 : c.1 + (ch₂.val : Int) * c.2 = x.targetC0 + (ch₂.val : Int) * x.targetC1 := hEval₂
          rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
        have hc1 : c.2 = x.targetC1 := by
          rcases Int.mul_eq_zero.1 hSub with hBad | hDiff0
          · exact False.elim (hNeVal hBad)
          · omega
        have hc0 : c.1 = x.targetC0 := by
          have e1 : c.1 + (ch₁.val : Int) * c.2 = x.targetC0 + (ch₁.val : Int) * x.targetC1 := hEval₁
          rw [hc1] at e1; omega
        have hPair : decodeCoeffs p₁ = (x.targetC0, x.targetC1) := by
          cases hDec : decodeCoeffs p₁ with
          | mk a b =>
            have ha : a = c.1 := by simp [c, hDec]
            have hb : b = c.2 := by simp [c, hDec]
            rw [ha, hb, hc0, hc1]
        exact ⟨hLen₁, hDig₁, hPair⟩⟩
    else
      have hCol : p₁.length ≤ maxBytes ∧ p₂.length ≤ maxBytes ∧
          HashBytes.ofBE (H p₁) = HashBytes.ofBE (H p₂) := by
        simp only [hashLinearAccept, Bool.and_eq_true, decide_eq_true_eq] at hAcc₁ hAcc₂
        exact ⟨hAcc₁.1.1, hAcc₂.1.1, hAcc₁.1.2.trans hAcc₂.1.2.symm⟩
      .inr
        { msgA := p₁
          msgB := p₂
          lenA := hCol.1
          lenB := hCol.2.1
          distinct := hEqP
          sameDigest := hCol.2.2 }

/-- Executed-trace variant of `hashLinearAccept` for arbitrarily long openings (`maxBytes > 32`),
    restricting candidate openings to a finite executed trace `traceMsgs` so `.hashCollisionAmong`
    is completely free of Pigeonhole vacuity! -/
def hashLinearTraceAccept (H : HashBytes.Hash) (traceMsgs : List (List UInt8)) (Q : Nat)
    (decodeCoeffs : List UInt8 → Int × Int)
    (x : HashLinearStmt) (_ : PUnit) (ch : Fin Q) (payload : List UInt8) : Bool :=
  let (c₀, c₁) := decodeCoeffs payload
  decide (payload ∈ traceMsgs) &&
  decide (HashBytes.ofBE (H payload) = x.commitVal) &&
  decide (c₀ + (ch.val : Int) * c₁ = x.targetC0 + (ch.val : Int) * x.targetC1)

/-- Executed-trace witness relation for `hashLinearTraceAccept`. -/
def HashLinearTraceRel (H : HashBytes.Hash) (traceMsgs : List (List UInt8))
    (decodeCoeffs : List UInt8 → Int × Int)
    (x : HashLinearStmt) (payload : List UInt8) : Prop :=
  payload ∈ traceMsgs ∧
  HashBytes.ofBE (H payload) = x.commitVal ∧
  decodeCoeffs payload = (x.targetC0, x.targetC1)

/-- **Constructive 2-Special-Sound Extractor for Arbitrarily Long Executed-Trace Linear IOP
    (`hashLinearTrace2SpecialSound`)**:
    Extracts either `HashLinearTraceRel` OR a `PinnedCollision H traceMsgs` without any `maxBytes ≤ 32`
    restriction! -/
def hashLinearTrace2SpecialSound (H : HashBytes.Hash) (traceMsgs : List (List UInt8)) (Q : Nat)
    (decodeCoeffs : List UInt8 → Int × Int) :
    SpecialSound2 HashLinearStmt (List UInt8) PUnit (List UInt8) Q where
  Rel x payload := HashLinearTraceRel H traceMsgs decodeCoeffs x payload
  assumptions := .hashCollisionAmong H traceMsgs
  accept x u ch payload := hashLinearTraceAccept H traceMsgs Q decodeCoeffs x u ch payload
  extractOrBreak2 x _ ch₁ ch₂ p₁ p₂ hNe hAcc₁ hAcc₂ :=
    if hEqP : p₁ = p₂ then
      .inl ⟨p₁, by
        subst hEqP
        simp only [hashLinearTraceAccept, Bool.and_eq_true, decide_eq_true_eq] at hAcc₁ hAcc₂
        rcases hAcc₁ with ⟨⟨hMem₁, hDig₁⟩, hEval₁⟩
        rcases hAcc₂ with ⟨_, hEval₂⟩
        have hNeVal : (ch₁.val : Int) - (ch₂.val : Int) ≠ 0 := by
          intro hZero; apply hNe; apply Fin.ext; omega
        let c := decodeCoeffs p₁
        have hSub : ((ch₁.val : Int) - (ch₂.val : Int)) * (c.2 - x.targetC1) = 0 := by
          have e1 : c.1 + (ch₁.val : Int) * c.2 = x.targetC0 + (ch₁.val : Int) * x.targetC1 := hEval₁
          have e2 : c.1 + (ch₂.val : Int) * c.2 = x.targetC0 + (ch₂.val : Int) * x.targetC1 := hEval₂
          rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
        have hc1 : c.2 = x.targetC1 := by
          rcases Int.mul_eq_zero.1 hSub with hBad | hDiff0
          · exact False.elim (hNeVal hBad)
          · omega
        have hc0 : c.1 = x.targetC0 := by
          have e1 : c.1 + (ch₁.val : Int) * c.2 = x.targetC0 + (ch₁.val : Int) * x.targetC1 := hEval₁
          rw [hc1] at e1; omega
        have hPair : decodeCoeffs p₁ = (x.targetC0, x.targetC1) := by
          cases hDec : decodeCoeffs p₁ with
          | mk a b =>
            have ha : a = c.1 := by simp [c, hDec]
            have hb : b = c.2 := by simp [c, hDec]
            rw [ha, hb, hc0, hc1]
        exact ⟨hMem₁, hDig₁, hPair⟩⟩
    else
      have hCol : p₁ ∈ traceMsgs ∧ p₂ ∈ traceMsgs ∧
          HashBytes.ofBE (H p₁) = HashBytes.ofBE (H p₂) := by
        simp only [hashLinearTraceAccept, Bool.and_eq_true, decide_eq_true_eq] at hAcc₁ hAcc₂
        exact ⟨hAcc₁.1.1, hAcc₂.1.1, hAcc₁.1.2.trans hAcc₂.1.2.symm⟩
      .inr
        { msgA := p₁
          msgB := p₂
          memA := hCol.1
          memB := hCol.2.1
          distinct := hEqP
          sameDigest := hCol.2.2 }

/-! ## 6. `class ComputationalJudge` & Constructive Soundness Laws -/

/-- **0-Axiom Constructive Cryptographic / Probabilistic Judge (`ComputationalJudge`)**:
    Unifies deterministic certificate checkers (`Obend.Judge`) and succinct cryptographic argument
    verifiers under one constructive typeclass with:
    - explicit algebraic `assumptions : AssumptionSet` and rational error `soundnessErr : Nat × Nat` (`0 < den`),
    - fuel-monotone total `verify : Nat → Obj → Cert → Judge.Verdict Clause`,
    - constructive white-box knowledge/break reduction `extractOrBreak` producing
      `PSum (Witness o) (BreakWitness assumptions)` from an accepted certificate and valid rewind bundle. -/
class ComputationalJudge (Obj Cert : Type) where
  Clause : Type
  Meaning : Obj → Prop
  Witness : Obj → Type
  witnessSound : ∀ {o : Obj}, Witness o → Meaning o
  assumptions : AssumptionSet
  soundnessErr : RatErr
  den_pos : 0 < soundnessErr.2
  verify : Nat → Obj → Cert → Judge.Verdict Clause
  mono : ∀ {r r' : Nat} {o : Obj} {c : Cert},
    r ≤ r' → verify r o c ≠ .uncovered → verify r' o c = verify r o c
  RewindBundle : Obj → Cert → Type
  rewindValid : Nat → (o : Obj) → (c : Cert) → RewindBundle o c → Prop
  extractOrBreak : ∀ {r : Nat} {o : Obj} {c : Cert} (b : RewindBundle o c),
    verify r o c = .ok → rewindValid r o c b → PSum (Witness o) (BreakWitness assumptions)

namespace ComputationalJudge
variable {Obj Cert : Type} [J : ComputationalJudge Obj Cert]

/-- A decided verdict agrees at every larger fuel grade. -/
theorem verify_decided_agree {r r' : Nat} {o : Obj} {c : Cert}
    (hle : r ≤ r') (hNe : J.verify r o c ≠ .uncovered) :
    J.verify r' o c = J.verify r o c :=
  J.mono hle hNe

/-- **Constructive Knowledge / Break Soundness (`extractOrBreak_sound`)**:
    Whenever `J.verify r o c = .ok` and rewind bundle `b` is valid, either `J.Meaning o` holds OR
    `J.assumptions` is constructively broken (`Broken J.assumptions`)! -/
theorem extractOrBreak_sound {r : Nat} {o : Obj} {c : Cert} (b : J.RewindBundle o c)
    (hOk : J.verify r o c = .ok) (hRew : J.rewindValid r o c b) :
    J.Meaning o ∨ Broken J.assumptions := by
  cases J.extractOrBreak b hOk hRew with
  | inl w => exact .inl (J.witnessSound w)
  | inr brk => exact .inr ⟨brk⟩

/-- **Conditional Meaning under Non-Pigeonhole Unbroken Assumptions (`meaning_of_unbroken`)**:
    Under `NonPigeonhole J.assumptions` and `Unbroken J.assumptions`, acceptance plus valid rewind
    establishes `J.Meaning o`. -/
theorem meaning_of_unbroken {r : Nat} {o : Obj} {c : Cert} (b : J.RewindBundle o c)
    (hOk : J.verify r o c = .ok) (hRew : J.rewindValid r o c b)
    (hNonPig : NonPigeonhole J.assumptions)
    (hUnbroken : Unbroken J.assumptions) :
    J.Meaning o := by
  rcases extractOrBreak_sound b hOk hRew with hM | hBrk
  · exact hM
  · exact False.elim (Unbroken.not_broken hNonPig hUnbroken hBrk)

end ComputationalJudge

/-! ## 7. Compositional Combinators (`ofSpecialSoundK`, `both`, `dualAssumption`, `ofDeterministicJudge`) -/

namespace CompJudge

/-- Monotone sequential composition of two `Judge.Verdict`s:
    returns `.ok` iff both return `.ok`, prioritizing left verdict before right verdict so
    fuel monotonicity is strictly preserved. -/
def combineVerdict {C₁ C₂ : Type}
    (v₁ : Judge.Verdict C₁) (v₂ : Judge.Verdict C₂) : Judge.Verdict (Sum C₁ C₂) :=
  match v₁ with
  | .refused k p => .refused (.inl k) (0 :: p)
  | .uncovered => .uncovered
  | .ok =>
    match v₂ with
    | .refused k p => .refused (.inr k) (1 :: p)
    | .uncovered => .uncovered
    | .ok => .ok

theorem combineVerdict_eq_ok {C₁ C₂ : Type} {v₁ : Judge.Verdict C₁} {v₂ : Judge.Verdict C₂}
    (h : combineVerdict v₁ v₂ = .ok) :
    v₁ = .ok ∧ v₂ = .ok := by
  cases v₁ <;> cases v₂ <;> simp [combineVerdict] at h
  exact ⟨rfl, rfl⟩

theorem combineVerdict_mono {C₁ C₂ : Type}
    {v₁ v₁' : Judge.Verdict C₁} {v₂ v₂' : Judge.Verdict C₂}
    (hNe : combineVerdict v₁ v₂ ≠ .uncovered)
    (hm₁ : v₁ ≠ .uncovered → v₁' = v₁)
    (hm₂ : v₂ ≠ .uncovered → v₂' = v₂) :
    combineVerdict v₁' v₂' = combineVerdict v₁ v₂ := by
  cases hv₁ : v₁ with
  | refused k p =>
    rw [hv₁] at hm₁
    have e₁ := hm₁ (fun h => by cases h)
    rw [e₁]; rfl
  | uncovered =>
    rw [hv₁] at hNe
    exact False.elim (hNe rfl)
  | ok =>
    rw [hv₁] at hm₁ hNe
    have e₁ := hm₁ (fun h => by cases h)
    rw [e₁]
    cases hv₂ : v₂ with
    | refused k p =>
      rw [hv₂] at hm₂
      rw [hm₂ (fun h => by cases h)]
    | uncovered =>
      rw [hv₂] at hNe
      exact False.elim (hNe rfl)
    | ok =>
      rw [hv₂] at hm₂
      rw [hm₂ (fun h => by cases h)]

/-- Lift any `SpecialSoundK` protocol (`0 < Q`) into a `ComputationalJudge` over `(Stmt × Commit)`
    and single-execution certificate `(Fin Q × Resp)`, with rational soundness error `(k - 1, Q)`. -/
@[instance_reducible] def ofSpecialSoundK {Stmt Wit Commit Resp : Type} {Q k : Nat}
    (P : SpecialSoundK Stmt Wit Commit Resp Q k) (hQ : 0 < Q) :
    ComputationalJudge (Stmt × Commit) (Fin Q × Resp) where
  Clause := Unit
  Meaning oc := ∃ w : Wit, P.Rel oc.1 w
  Witness oc := { w : Wit // P.Rel oc.1 w }
  witnessSound w := ⟨w.1, w.2⟩
  assumptions := P.assumptions
  soundnessErr := (k - 1, Q)
  den_pos := hQ
  verify _ oc tr := if P.accept oc.1 oc.2 tr.1 tr.2 then .ok else .refused () []
  mono _ _ := rfl
  RewindBundle _ tr :=
    { extra : List (Fin Q × Resp) //
      extra.length = k - 1 ∧ ((tr :: extra).map Prod.fst).Nodup }
  rewindValid _ oc _ b := ∀ p : Fin Q × Resp, p ∈ b.1 → P.accept oc.1 oc.2 p.1 p.2 = true
  extractOrBreak {_ oc tr} b hOk hRew :=
    have hAcc0 : P.accept oc.1 oc.2 tr.1 tr.2 = true := by
      cases h : P.accept oc.1 oc.2 tr.1 tr.2
      · simp [h] at hOk
      · rfl
    have hLen : (tr :: b.1).length = k := by
      have hk := P.hk; have hb := b.2.1; simp only [List.length_cons, hb]; omega
    have hAll : ∀ p : Fin Q × Resp, p ∈ tr :: b.1 → P.accept oc.1 oc.2 p.1 p.2 = true := by
      intro p hp
      cases hp with
      | head => exact hAcc0
      | tail _ hm => exact hRew p hm
    P.extractOrBreak oc.1 oc.2 (tr :: b.1) hLen b.2.2 hAll

/-- Lift any `SpecialSound2` protocol (`0 < Q`) into a `ComputationalJudge` with soundness error `(1, Q)`. -/
@[instance_reducible] def ofSpecialSound2 {Stmt Wit Commit Resp : Type} {Q : Nat}
    (P : SpecialSound2 Stmt Wit Commit Resp Q) (hQ : 0 < Q) :
    ComputationalJudge (Stmt × Commit) (Fin Q × Resp) :=
  ofSpecialSoundK P.toSpecialSoundK hQ

/-- **Combinator 1 (`CompJudge.both`)**: Conjunction of two `ComputationalJudge`s over a shared object `Obj`
    (e.g. a TLS transcript proof + a VPA policy proof over a shared commitment):
    - `Meaning o := J₁.Meaning o ∧ J₂.Meaning o`
    - `assumptions := .conj J₁.assumptions J₂.assumptions` (relies on both assumption floors)
    - `soundnessErr := ratAdd J₁.soundnessErr J₂.soundnessErr` ($\varepsilon_1 + \varepsilon_2$ union bound). -/
@[instance_reducible] def both {Obj Cert₁ Cert₂ : Type}
    (J₁ : ComputationalJudge Obj Cert₁)
    (J₂ : ComputationalJudge Obj Cert₂) :
    ComputationalJudge Obj (Cert₁ × Cert₂) where
  Clause := Sum (@ComputationalJudge.Clause Obj Cert₁ J₁) (@ComputationalJudge.Clause Obj Cert₂ J₂)
  Meaning o := @ComputationalJudge.Meaning Obj Cert₁ J₁ o ∧ @ComputationalJudge.Meaning Obj Cert₂ J₂ o
  Witness o := @ComputationalJudge.Witness Obj Cert₁ J₁ o × @ComputationalJudge.Witness Obj Cert₂ J₂ o
  witnessSound w := ⟨@ComputationalJudge.witnessSound Obj Cert₁ J₁ _ w.1,
                     @ComputationalJudge.witnessSound Obj Cert₂ J₂ _ w.2⟩
  assumptions := .conj (@ComputationalJudge.assumptions Obj Cert₁ J₁) (@ComputationalJudge.assumptions Obj Cert₂ J₂)
  soundnessErr := ratAdd (@ComputationalJudge.soundnessErr Obj Cert₁ J₁) (@ComputationalJudge.soundnessErr Obj Cert₂ J₂)
  den_pos := ratAdd_den_pos (@ComputationalJudge.den_pos Obj Cert₁ J₁) (@ComputationalJudge.den_pos Obj Cert₂ J₂)
  verify r o c := combineVerdict (@ComputationalJudge.verify Obj Cert₁ J₁ r o c.1)
                                 (@ComputationalJudge.verify Obj Cert₂ J₂ r o c.2)
  mono hle hNe := combineVerdict_mono hNe (@ComputationalJudge.mono Obj Cert₁ J₁ _ _ _ _ hle)
                                          (@ComputationalJudge.mono Obj Cert₂ J₂ _ _ _ _ hle)
  RewindBundle o c := @ComputationalJudge.RewindBundle Obj Cert₁ J₁ o c.1 ×
                      @ComputationalJudge.RewindBundle Obj Cert₂ J₂ o c.2
  rewindValid r o c b := @ComputationalJudge.rewindValid Obj Cert₁ J₁ r o c.1 b.1 ∧
                         @ComputationalJudge.rewindValid Obj Cert₂ J₂ r o c.2 b.2
  extractOrBreak b hOk hRew :=
    let hBoth := combineVerdict_eq_ok hOk
    match @ComputationalJudge.extractOrBreak Obj Cert₁ J₁ _ _ _ b.1 hBoth.1 hRew.1,
          @ComputationalJudge.extractOrBreak Obj Cert₂ J₂ _ _ _ b.2 hBoth.2 hRew.2 with
    | .inl w₁, .inl w₂ => .inl (w₁, w₂)
    | .inr brk₁, _ => .inr (.inl brk₁)
    | .inl _, .inr brk₂ => .inr (.inr brk₂)

theorem both_sound {Obj Cert₁ Cert₂ : Type}
    (J₁ : ComputationalJudge Obj Cert₁) (J₂ : ComputationalJudge Obj Cert₂)
    {r : Nat} {o : Obj} {c : Cert₁ × Cert₂}
    (b : (@ComputationalJudge.RewindBundle Obj (Cert₁ × Cert₂) (both J₁ J₂) o c))
    (hOk : @ComputationalJudge.verify Obj (Cert₁ × Cert₂) (both J₁ J₂) r o c = .ok)
    (hRew : @ComputationalJudge.rewindValid Obj (Cert₁ × Cert₂) (both J₁ J₂) r o c b) :
    (@ComputationalJudge.Meaning Obj Cert₁ J₁ o ∧ @ComputationalJudge.Meaning Obj Cert₂ J₂ o) ∨
      Broken (@ComputationalJudge.assumptions Obj Cert₁ J₁) ∨
      Broken (@ComputationalJudge.assumptions Obj Cert₂ J₂) := by
  rcases @ComputationalJudge.extractOrBreak_sound _ _ (both J₁ J₂) r o c b hOk hRew with hM | hBrk
  · exact .inl hM
  · exact .inr ((broken_conj_iff _ _).1 hBrk)

/-- **Combinator 2 (`CompJudge.dualAssumption`)**: Cross-assumption `DualPCS` combinator!
    Given two cryptographic judges `J₁` (e.g. `HashUDR`) and `J₂` (e.g. `LatticeSIS`) certifying
    a common semantic claim `Claim : Obj → Prop`:
    - Accepts `(c₁, c₂)` iff **both** `J₁.verify` and `J₂.verify` accept;
    - `assumptions := .disj J₁.assumptions J₂.assumptions`: breaking soundness requires constructively
      exhibiting **BOTH** `BreakWitness J₁.assumptions` **AND** `BreakWitness J₂.assumptions` simultaneously!
    - `soundnessErr := ratMin J₁.soundnessErr J₂.soundnessErr` ($\min(\varepsilon_1, \varepsilon_2)$)! -/
@[instance_reducible] def dualAssumption {Obj Cert₁ Cert₂ : Type}
    (Claim : Obj → Prop)
    (J₁ : ComputationalJudge Obj Cert₁)
    (J₂ : ComputationalJudge Obj Cert₂)
    (hImp₁ : ∀ {o : Obj}, @ComputationalJudge.Meaning Obj Cert₁ J₁ o → Claim o)
    (hImp₂ : ∀ {o : Obj}, @ComputationalJudge.Meaning Obj Cert₂ J₂ o → Claim o) :
    ComputationalJudge Obj (Cert₁ × Cert₂) where
  Clause := Sum (@ComputationalJudge.Clause Obj Cert₁ J₁) (@ComputationalJudge.Clause Obj Cert₂ J₂)
  Meaning := Claim
  Witness o := Sum (@ComputationalJudge.Witness Obj Cert₁ J₁ o) (@ComputationalJudge.Witness Obj Cert₂ J₂ o)
  witnessSound
    | .inl w₁ => hImp₁ (@ComputationalJudge.witnessSound Obj Cert₁ J₁ _ w₁)
    | .inr w₂ => hImp₂ (@ComputationalJudge.witnessSound Obj Cert₂ J₂ _ w₂)
  assumptions := .disj (@ComputationalJudge.assumptions Obj Cert₁ J₁) (@ComputationalJudge.assumptions Obj Cert₂ J₂)
  soundnessErr := ratMin (@ComputationalJudge.soundnessErr Obj Cert₁ J₁) (@ComputationalJudge.soundnessErr Obj Cert₂ J₂)
  den_pos := ratMin_den_pos (@ComputationalJudge.den_pos Obj Cert₁ J₁) (@ComputationalJudge.den_pos Obj Cert₂ J₂)
  verify r o c := combineVerdict (@ComputationalJudge.verify Obj Cert₁ J₁ r o c.1)
                                 (@ComputationalJudge.verify Obj Cert₂ J₂ r o c.2)
  mono hle hNe := combineVerdict_mono hNe (@ComputationalJudge.mono Obj Cert₁ J₁ _ _ _ _ hle)
                                          (@ComputationalJudge.mono Obj Cert₂ J₂ _ _ _ _ hle)
  RewindBundle o c := @ComputationalJudge.RewindBundle Obj Cert₁ J₁ o c.1 ×
                      @ComputationalJudge.RewindBundle Obj Cert₂ J₂ o c.2
  rewindValid r o c b := @ComputationalJudge.rewindValid Obj Cert₁ J₁ r o c.1 b.1 ∧
                         @ComputationalJudge.rewindValid Obj Cert₂ J₂ r o c.2 b.2
  extractOrBreak b hOk hRew :=
    let hBoth := combineVerdict_eq_ok hOk
    match @ComputationalJudge.extractOrBreak Obj Cert₁ J₁ _ _ _ b.1 hBoth.1 hRew.1,
          @ComputationalJudge.extractOrBreak Obj Cert₂ J₂ _ _ _ b.2 hBoth.2 hRew.2 with
    | .inl w₁, _ => .inl (.inl w₁)
    | .inr _, .inl w₂ => .inl (.inr w₂)
    | .inr brk₁, .inr brk₂ => .inr (brk₁, brk₂)

/-- Soundness of `CompJudge.dualAssumption`: acceptance plus valid rewind yields either `Claim o` OR
    simultaneous constructive breaks of **both** `J₁.assumptions` **and** `J₂.assumptions`, with
    tightened rational soundness bound `min(ε₁, ε₂)`! -/
theorem dualAssumption_sound {Obj Cert₁ Cert₂ : Type}
    (Claim : Obj → Prop)
    (J₁ : ComputationalJudge Obj Cert₁) (J₂ : ComputationalJudge Obj Cert₂)
    (hImp₁ : ∀ {o : Obj}, @ComputationalJudge.Meaning Obj Cert₁ J₁ o → Claim o)
    (hImp₂ : ∀ {o : Obj}, @ComputationalJudge.Meaning Obj Cert₂ J₂ o → Claim o)
    {r : Nat} {o : Obj} {c : Cert₁ × Cert₂}
    (b : (@ComputationalJudge.RewindBundle Obj (Cert₁ × Cert₂) (dualAssumption Claim J₁ J₂ hImp₁ hImp₂) o c))
    (hOk : @ComputationalJudge.verify Obj (Cert₁ × Cert₂) (dualAssumption Claim J₁ J₂ hImp₁ hImp₂) r o c = .ok)
    (hRew : @ComputationalJudge.rewindValid Obj (Cert₁ × Cert₂) (dualAssumption Claim J₁ J₂ hImp₁ hImp₂) r o c b) :
    Claim o ∨
      (Broken (@ComputationalJudge.assumptions Obj Cert₁ J₁) ∧
       Broken (@ComputationalJudge.assumptions Obj Cert₂ J₂)) := by
  let JD := dualAssumption Claim J₁ J₂ hImp₁ hImp₂
  rcases @ComputationalJudge.extractOrBreak_sound _ _ JD r o c b hOk hRew with hC | hBrk
  · exact .inl hC
  · exact .inr ((broken_disj_iff _ _).1 hBrk)

theorem dualAssumption_error_tightens {Obj Cert₁ Cert₂ : Type}
    (Claim : Obj → Prop)
    (J₁ : ComputationalJudge Obj Cert₁) (J₂ : ComputationalJudge Obj Cert₂)
    (hImp₁ : ∀ {o : Obj}, @ComputationalJudge.Meaning Obj Cert₁ J₁ o → Claim o)
    (hImp₂ : ∀ {o : Obj}, @ComputationalJudge.Meaning Obj Cert₂ J₂ o → Claim o) :
    ratLe (@ComputationalJudge.soundnessErr Obj (Cert₁ × Cert₂) (dualAssumption Claim J₁ J₂ hImp₁ hImp₂))
          (@ComputationalJudge.soundnessErr Obj Cert₁ J₁) ∧
    ratLe (@ComputationalJudge.soundnessErr Obj (Cert₁ × Cert₂) (dualAssumption Claim J₁ J₂ hImp₁ hImp₂))
          (@ComputationalJudge.soundnessErr Obj Cert₂ J₂) :=
  ⟨ratMin_le_left _ _, ratMin_le_right _ _⟩

/-- **Combinator 3 (`CompJudge.ofDeterministicJudge`)**:
    Embeds any exact `Obend.Judge Obj Cert` into `ComputationalJudge Obj Cert` with
    `assumptions := .none` (`BreakWitness .none = PEmpty`) and `soundnessErr := (0, 1)` (`ε = 0`),
    unifying deterministic kernel judges and cryptographic judges in one category! -/
@[instance_reducible] def ofDeterministicJudge {Obj Cert : Type} [J : Obend.Judge Obj Cert] :
    ComputationalJudge Obj Cert where
  Clause := J.Clause
  Meaning o := ∃ c : Cert, J.Meaning o c
  Witness o := { c : Cert // J.Meaning o c }
  witnessSound w := ⟨w.1, w.2⟩
  assumptions := .none
  soundnessErr := ratZero
  den_pos := by decide
  verify := J.check
  mono := J.mono
  RewindBundle _ _ := PUnit
  rewindValid _ _ _ _ := True
  extractOrBreak {_ _ c} _ hOk _ := .inl ⟨c, J.sound hOk⟩

/-- Exact unconditional soundness (`ε = 0`, `assumptions = .none`) of `ofDeterministicJudge`. -/
theorem ofDeterministicJudge_sound {Obj Cert : Type} [J : Obend.Judge Obj Cert]
    {r : Nat} {o : Obj} {c : Cert}
    (hOk : @ComputationalJudge.verify Obj Cert (ofDeterministicJudge (J := J)) r o c = .ok) :
    ∃ c' : Cert, J.Meaning o c' :=
  @ComputationalJudge.meaning_of_unbroken _ _ (ofDeterministicJudge (J := J))
    r o c PUnit.unit hOk trivial nonPigeonhole_none unbroken_none

end CompJudge

/-! ## 8. Concrete Inhabited Witnesses & Anti-Vacuity Checks (`HypothesisLedger`) -/

/-- Exact `Obend.Judge` checking positive equality `o = c ∧ o ≠ 0` on `Nat`, with genuine
    object-level refusal (`Clause := Bool`, `refutes true = true` certifying `o = 0 → ∀ c', ¬ Meaning o c'`). -/
instance natEqDeterministicJudge : Obend.Judge Nat Nat where
  Clause := Bool
  Meaning o c := o = c ∧ o ≠ 0
  check _ o c :=
    if o == 0 then .refused true [0]
    else if o == c then .ok
    else .refused false [1]
  sound {_ o c} h := by
    if ho : o = 0 then
      subst ho; simp at h
    else if heq : o = c then
      exact ⟨heq, ho⟩
    else
      have hoB : (o == 0) = false := beq_eq_false_iff_ne.2 ho
      have hneB : (o == c) = false := beq_eq_false_iff_ne.2 heq
      simp [hoB, hneB] at h
  refutes b := b
  refuted {_ o c k _} hChk hRef c' hM := by
    if ho : o = 0 then
      exact hM.2 ho
    else
      have hoB : (o == 0) = false := beq_eq_false_iff_ne.2 ho
      if heq : o = c then
        have heqB : (o == c) = true := beq_iff_eq.2 heq
        simp [hoB, heqB] at hChk
      else
        have hneB : (o == c) = false := beq_eq_false_iff_ne.2 heq
        simp only [hoB, hneB, Bool.false_eq_true, ↓reduceIte, Judge.Verdict.refused.injEq] at hChk
        rw [← hChk.1] at hRef
        cases hRef
  Fragment o := o ≠ 0
  complete {o} hFrag _ := ⟨o, 0, by
    have hoB : (o == 0) = false := beq_eq_false_iff_ne.2 hFrag
    simp [hoB]⟩
  mono _ _ := rfl

/-- Concrete 1×2 Ajtai matrix `[[1, 10]]` mod `q = 97`, `beta = 2`, commitment `cm = [11]`,
    in the genuinely `NonPigeonhole` (`9^2 = 81 ≤ 97`) and `Unbroken` (`2 * beta = 4`) regime. -/
@[instance_reducible] def sampleSISJudge :
    ComputationalJudge (SISOpeningStmt × PUnit) (Fin 2 × List Int) :=
  CompJudge.ofSpecialSound2 (sisOpening2SpecialSound 97 2 [[1, 10]] [11]) (by decide)

/-- Concrete Hash-Committed Linear IOP judge over `Fin 5` (`ε = 1/5`). -/
@[instance_reducible] def sampleHashJudge :
    ComputationalJudge (HashLinearStmt × PUnit) (Fin 5 × List UInt8) :=
  CompJudge.ofSpecialSound2
    (hashLinear2SpecialSound (fun bs => bs) 8 5
      (fun bs => match bs with | a :: b :: _ => (a.toNat, b.toNat) | _ => (0, 0)))
    (by decide)

/-- Concrete positive witness exercising `ComputationalJudge.verify`, `rewindValid`,
    `CompJudge.both`, `CompJudge.dualAssumption`, and `CompJudge.ofDeterministicJudge`
    so every soundness theorem premise in this module is non-vacuous. -/
theorem compJudge_pipeline_inhabited :
    @ComputationalJudge.verify Nat Nat
      (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge)) 0 42 42 = .ok ∧
    @ComputationalJudge.verify _ _ sampleSISJudge 0
      ({ numCols := 2, check0 := fun _ => true, check1 := fun _ => true }, PUnit.unit)
      (⟨0, by decide⟩, [1, 1]) = .ok ∧
    (∃ b, @ComputationalJudge.rewindValid _ _ sampleSISJudge 0
      ({ numCols := 2, check0 := fun _ => true, check1 := fun _ => true }, PUnit.unit)
      (⟨0, by decide⟩, [1, 1]) b) ∧
    @ComputationalJudge.verify _ _
      (CompJudge.both
        (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge))
        (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge))) 0 7 (7, 7) = .ok ∧
    @ComputationalJudge.verify _ _
      (CompJudge.dualAssumption
        (@ComputationalJudge.Meaning Nat Nat (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge)))
        (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge))
        (CompJudge.ofDeterministicJudge (J := natEqDeterministicJudge))
        (fun h => h) (fun h => h)) 0 7 (7, 7) = .ok := by
  refine ⟨rfl, rfl, ⟨⟨[(⟨1, by decide⟩, [1, 1])], rfl, by decide⟩, ?_⟩, rfl, rfl⟩
  intro p hp
  cases hp with
  | head => decide
  | tail _ hNil => cases hNil

end Obend.Judge.Computational
end
