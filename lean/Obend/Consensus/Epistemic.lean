module
/-
# Obend.Consensus.Epistemic — Epistemic Consensus for Solver and Proof Races

Absorbs `minidregg/Theory/EpistemicConsensus.lean` and `NEXT-MATHEMATICA.md:135`
into Obend's consensus architecture.

## The Core Problem:
Multiple untrusted solvers / provers race in parallel to solve optimization or
verification goals (e.g. DrEX primal-dual LP clearing, real analysis interval/SOS
judges, LawDial repair synthesis).
Each solver submits a candidate certificate `c`.
Epistemic Consensus allows all validators to converge deterministically on the
exact same winning certificate without interactive voting rounds.

## Metatheorems:
- `winner_is_valid`: Winner certificate is strictly valid and admissible.
- `winner_mem`: Winner certificate belongs to the input candidate pool.
- `frontrunning_resistant_pair`: Flooding with inferior or invalid certificates cannot displace winner.
- `order_insensitive_pair`: Candidate arrival permutation does not affect winner.
- `verified_world_independent`: Validity is world-independent distributed knowledge.
- `no_dist_knowledge_of_invalid`: Byzantine subset cannot forge distributed knowledge of an invalid certificate.
-/

public import Obend.Core.Data
public import Obend.Digest.Cshake256.Seam
public import Obend.Judge.Clearing
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis

@[expose] public section
namespace Obend.Consensus.Epistemic

open Obend.Core.Data
open Obend.Digest.Cshake256
open Obend.Digest.Cshake256.Native

set_option autoImplicit false

/-! ## §1. Canonical Lexical Ordering on Byte Sequences -/

/-- Lexical comparison on lists of bytes (strict total order). -/
def byteListLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x.toNat < y.toNat then true
    else if y.toNat < x.toNat then false
    else byteListLt xs ys

/-- Canonical lexical comparison on `ByteArray`. -/
def byteArrayLt (a b : ByteArray) : Bool :=
  byteListLt a.toList b.toList

theorem byteListLt_irreflexive (bs : List UInt8) : byteListLt bs bs = false := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    unfold byteListLt
    have hnot : ¬ (b.toNat < b.toNat) := Nat.lt_irrefl b.toNat
    simp [hnot, ih]

theorem byteArrayLt_irreflexive (b : ByteArray) : byteArrayLt b b = false :=
  byteListLt_irreflexive b.toList

theorem byteListLt_asymmetric {a b : List UInt8} (h : byteListLt a b = true) :
    byteListLt b a = false := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => contradiction
    | cons y ys => rfl
  | cons x xs ih =>
    cases b with
    | nil => contradiction
    | cons y ys =>
      unfold byteListLt at h ⊢
      by_cases hxy : x.toNat < y.toNat
      · have hyx : ¬ (y.toNat < x.toNat) := by omega
        simp only [hxy, ↓reduceIte] at h
        simp [hyx, hxy]
      · by_cases hyx : y.toNat < x.toNat
        · simp [hxy, hyx] at h
        · have hnot_xy : ¬ (x.toNat < y.toNat) := hxy
          have hnot_yx : ¬ (y.toNat < x.toNat) := hyx
          simp only [hnot_xy, hnot_yx, ↓reduceIte] at h ⊢
          exact ih h

theorem byteArrayLt_asymmetric {a b : ByteArray} (h : byteArrayLt a b = true) :
    byteArrayLt b a = false :=
  byteListLt_asymmetric h

/-! ## §2. Verifiable Race Specification -/

/-- A verifiable race over problem query `Q` and candidate certificate `Cert`. -/
class VerifiableRace (Q Cert : Type) where
  /-- Verification check: does certificate `c` validly discharge query `q`? -/
  isValid : Q → Cert → Bool
  /-- Cost metric: lower cost indicates a superior certificate. -/
  cost : Q → Cert → Nat
  /-- Deterministic canonical tie-breaker digest (e.g. cSHAKE256 hash). -/
  digest : Cert → ByteArray

variable {Q Cert : Type} [instRace : VerifiableRace Q Cert]

def certCost (q : Q) (c : Cert) : Nat :=
  instRace.cost q c

def certDigest (_ : Q) (c : Cert) : ByteArray :=
  instRace.digest c

def certValid (q : Q) (c : Cert) : Bool :=
  instRace.isValid q c

/-- Strict preference comparison between two candidate certificates:
    First compares cost (lower is strictly better).
    Breaks ties using canonical lexical hash digest. -/
def betterCert (q : Q) (c₁ c₂ : Cert) : Bool :=
  let k1 := certCost q c₁
  let k2 := certCost q c₂
  if k1 < k2 then true
  else if k2 < k1 then false
  else byteArrayLt (certDigest q c₁) (certDigest q c₂)

theorem betterCert_irreflexive (q : Q) (c : Cert) : betterCert q c c = false := by
  unfold betterCert
  have hnot : ¬ (certCost q c < certCost q c) := Nat.lt_irrefl _
  simp [hnot, byteArrayLt_irreflexive (certDigest q c)]

theorem betterCert_asymmetric {q : Q} {c₁ c₂ : Cert} (h : betterCert q c₁ c₂ = true) :
    betterCert q c₂ c₁ = false := by
  unfold betterCert at h ⊢
  by_cases h12 : certCost q c₁ < certCost q c₂
  · have h21 : ¬ (certCost q c₂ < certCost q c₁) := by omega
    simp only [h12, ↓reduceIte] at h
    simp [h21, h12]
  · by_cases h21 : certCost q c₂ < certCost q c₁
    · simp [h12, h21] at h
    · have hnot1 : ¬ (certCost q c₁ < certCost q c₂) := h12
      have hnot2 : ¬ (certCost q c₂ < certCost q c₁) := h21
      simp only [hnot1, hnot2, ↓reduceIte] at h ⊢
      exact byteArrayLt_asymmetric h

/-! ## §3. Deterministic Winner Selection -/

/-- Structural helper finding the best candidate in a list. -/
def pickBest (q : Q) : List Cert → Option Cert
  | [] => none
  | c :: cs =>
    match pickBest q cs with
    | none => some c
    | some best => if betterCert q c best then some c else some best

@[simp] theorem pickBest_nil (q : Q) : pickBest (Cert := Cert) q [] = none := rfl

@[simp] theorem pickBest_singleton (q : Q) (c : Cert) : pickBest q [c] = some c := rfl

@[simp] theorem pickBest_cons_two (q : Q) (c₁ c₂ : Cert) :
    pickBest q [c₁, c₂] = if betterCert q c₁ c₂ then some c₁ else some c₂ := rfl

/-- Select the winning certificate among a list of candidates:
    1. Filter candidates for validity (`isValid q c`).
    2. If no valid candidates exist, return `none`.
    3. Otherwise pick the best valid candidate. -/
def selectWinner (q : Q) (candidates : List Cert) : Option Cert :=
  pickBest q (candidates.filter (certValid q))

/-! ## §4. Consensus Metatheorems -/

theorem pickBest_mem (q : Q) (candidates : List Cert) :
    ∀ w, pickBest q candidates = some w → w ∈ candidates := by
  induction candidates with
  | nil => intro w h; contradiction
  | cons c cs ih =>
    intro w h
    unfold pickBest at h
    cases hbest : pickBest q cs with
    | none =>
      rw [hbest] at h
      injection h with hw
      subst hw
      exact List.Mem.head cs
    | some best =>
      rw [hbest] at h
      by_cases hcb : betterCert q c best = true
      · simp [hcb] at h
        subst h
        exact List.Mem.head cs
      · simp [hcb] at h
        subst h
        exact List.Mem.tail c (ih best hbest)

theorem mem_filter (p : Cert → Bool) (l : List Cert) (x : Cert) (h : x ∈ l.filter p) :
    x ∈ l ∧ p x = true := by
  induction l with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.filter_cons] at h
    by_cases hp : p y = true
    · simp only [hp, ↓reduceIte] at h
      cases h with
      | head =>
        exact ⟨List.Mem.head ys, hp⟩
      | tail _ hmem =>
        have ⟨h1, h2⟩ := ih hmem
        exact ⟨List.Mem.tail y h1, h2⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      have ⟨h1, h2⟩ := ih h
      exact ⟨List.Mem.tail y h1, h2⟩

/-- Winner belongs to the candidate list. -/
theorem winner_mem {q : Q} {candidates : List Cert} {w : Cert}
    (h : selectWinner q candidates = some w) : w ∈ candidates := by
  unfold selectWinner at h
  have hmem := pickBest_mem q (candidates.filter (certValid q)) w h
  exact (mem_filter (certValid q) candidates w hmem).1

/-- Winner satisfies the verification check. -/
theorem winner_is_valid {q : Q} {candidates : List Cert} {w : Cert}
    (h : selectWinner q candidates = some w) : certValid q w = true := by
  unfold selectWinner at h
  have hmem := pickBest_mem q (candidates.filter (certValid q)) w h
  exact (mem_filter (certValid q) candidates w hmem).2

/-- No candidates yields no winner. -/
theorem selectWinner_nil (q : Q) : (selectWinner (Cert := Cert) q []) = none := rfl

/-- If all candidates are invalid, no winner is selected. -/
theorem selectWinner_all_invalid {q : Q} {candidates : List Cert}
    (hall : ∀ c ∈ candidates, certValid q c = false) :
    selectWinner q candidates = none := by
  unfold selectWinner
  have hfilt : candidates.filter (certValid q) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    have := hall c hc
    simp [this]
  rw [hfilt]
  rfl

/-- Single valid candidate is immediately selected as winner. -/
theorem selectWinner_singleton_valid {q : Q} {c : Cert}
    (hval : certValid q c = true) :
    selectWinner q [c] = some c := by
  unfold selectWinner
  simp [hval]

/-- Resistance to Solver Front-running / Race Malleability:
    An adversary injecting an inferior candidate cannot displace an established winner. -/
theorem frontrunning_resistant_pair {q : Q} {w b : Cert}
    (hw_val : certValid q w = true)
    (hbetter : betterCert q w b = true) :
    selectWinner q [w, b] = some w := by
  unfold selectWinner
  by_cases hb_val : certValid q b = true
  · simp only [List.filter_cons, hw_val, hb_val, List.filter_nil]
    simp [pickBest_cons_two, hbetter]
  · simp only [List.filter_cons, hw_val, hb_val, Bool.false_eq_true, List.filter_nil]
    simp [pickBest_singleton]

/-- Determinism on permutations of two candidates:
    Order of arrival does not affect the selected winner. -/
theorem order_insensitive_pair {q : Q} {c₁ c₂ : Cert}
    (h1 : certValid q c₁ = true)
    (h2 : certValid q c₂ = true)
    (hdiff : betterCert q c₁ c₂ = true) :
    selectWinner q [c₁, c₂] = selectWinner q [c₂, c₁] := by
  unfold selectWinner
  simp only [List.filter_cons, h1, h2, List.filter_nil]
  have hasym := betterCert_asymmetric hdiff
  simp [pickBest_cons_two, hdiff, hasym]

/-! ## §5. Epistemic Kripke Frame Integration -/

/-- An Epistemic Frame with Byzantine participants (Goubault et al.). -/
structure EpistemicFrame (Ω Agent : Type) where
  actual : Ω
  Indist : Agent → Ω → Ω → Prop
  indist_refl : ∀ a w, Indist a w w
  Faulty : Agent → Prop

/-- The proposition that certificate `c` discharges query `q`. -/
def verifiedProp {Ω : Type} (q : Q) (c : Cert) : Ω → Prop :=
  fun _ => certValid q c = true

namespace EpistemicFrame

variable {Ω Agent : Type} (F : EpistemicFrame Ω Agent)

def Honest (a : Agent) : Prop := ¬ F.Faulty a

def Knows (a : Agent) (φ : Ω → Prop) (w : Ω) : Prop :=
  ∀ w', F.Indist a w' w → φ w'

def DistKnows (B : Agent → Prop) (φ : Ω → Prop) (w : Ω) : Prop :=
  ∀ w', (∀ a, B a → F.Indist a w' w) → φ w'

/-- World-independence: validity of a verified certificate does not depend on world state. -/
theorem verified_world_independent (q : Q) (c : Cert) (w w' : Ω) :
    verifiedProp (Ω := Ω) q c w ↔ verifiedProp (Ω := Ω) q c w' :=
  Iff.rfl

/-- Every agent knows a valid certificate, regardless of network or local perspective. -/
theorem all_know_verified (q : Q) (c : Cert) (hval : certValid q c = true) (a : Agent) :
    F.Knows a (verifiedProp (Ω := Ω) q c) F.actual :=
  fun _ _ => hval

/-- Distributed knowledge of the honest committee over a verified certificate. -/
theorem honest_distKnows_verified (q : Q) (c : Cert) (hval : certValid q c = true) :
    F.DistKnows F.Honest (verifiedProp (Ω := Ω) q c) F.actual :=
  fun _ _ => hval

/-- Byzantine subset cannot forge distributed knowledge of an invalid certificate. -/
theorem no_dist_knowledge_of_invalid (q : Q) (c : Cert) (hinval : certValid q c = false) :
    ¬ F.DistKnows F.Honest (verifiedProp (Ω := Ω) q c) F.actual := by
  intro hdk
  have h := hdk F.actual (fun a _ => F.indist_refl a F.actual)
  unfold verifiedProp at h
  rw [hinval] at h
  contradiction

end EpistemicFrame

/-! ## §6. Concrete Instantiations -/

/-! ### Instantiation 1: DrEX LP Clearing Race (`drex-clearing@1`) -/

namespace DrEXRace

open Obend.Judge

/-- The DrEX LP clearing certificate wrapper for epistemic racing. -/
structure ClearingCert where
  cert : Certificate
  turnDigest : ByteArray

/-- Deterministic digest for DrEX clearing certificate using cSHAKE256. -/
def clearingCertDigest (c : ClearingCert) : ByteArray :=
  cshake256Kernel (ByteArray.mk #[0x44, 0x52, 0x45, 0x58]) c.turnDigest

/-- Cleared matched volume at `c.cert.price`: `min(demand(p), supply(p))` across `q.orders`. -/
def clearedMatchedVolume (q : ClearingQuery) (c : ClearingCert) : Nat :=
  let p := c.cert.price
  if p == 0 then 0
  else
    let demand :=
      (q.orders.filter (fun o => o.side == .bid && o.qty > 0 && p * o.qty ≤ o.total)).foldl
        (fun acc o => acc + o.qty) 0
    let supply :=
      (q.orders.filter (fun o => o.side == .ask && o.qty > 0 && o.total ≤ p * o.qty)).foldl
        (fun acc o => acc + o.qty) 0
    min demand supply

/-- Non-negative primal-dual duality gap `max(0, dualCap - objVol)` for `(q, c)`. -/
def computeDualityGap (q : ClearingQuery) (c : ClearingCert) : Nat :=
  let objVol := Obend.Judge.finSum q.orders.length (fun i => (q.orders.get i).fill q.market q.transfers)
  let dualCap := Obend.Judge.finSum q.orders.length (fun i =>
    let cap := if (q.orders.get i).crosses c.cert.price then ((q.orders.get i).qty : Int) else 0
    let s := c.cert.slacks.getD i.val 0
    cap * s)
  Int.toNat (dualCap - objVol)

/-- Boolean wrapper for `Obend.Judge.judge` on `(q, c.cert)`. -/
def checkClearing (q : ClearingQuery) (c : ClearingCert) : Bool :=
  match Obend.Judge.judge q.market q.orders q.transfers c.cert with
  | .ok () => (0 < c.cert.price) && (c.cert.price ≤ 1000000000)
  | .error _ => false

/-- VerifiableRace instance for parallel LP clearing solvers racing on an order book. -/
instance : VerifiableRace ClearingQuery ClearingCert where
  isValid q c := checkClearing q c
  cost q c :=
    -- Rank primarily by negated cleared volume, secondarily by duality gap, then potential spread
    let volPenalty := (1000000 - min 1000000 (clearedMatchedVolume q c)) * 1000000
    let gapPenalty := (computeDualityGap q c) * 1000
    volPenalty + gapPenalty + q.market.epsilon + Int.natAbs (c.cert.potentials.1 - c.cert.potentials.2)
  digest c := clearingCertDigest c

end DrEXRace

/-! ### Instantiation 2: Real Analysis Interval Bounding Race (`interval@1`) -/

namespace IntervalRace

open Obend.Judge
open Obend.Analysis

structure IntervalCertWrapper where
  cert : IntervalCert
  boundDigest : ByteArray
  refinedBound : Option Interval := none

def intervalCertDigest (c : IntervalCertWrapper) : ByteArray :=
  cshake256Kernel (ByteArray.mk #[0x49, 0x4E, 0x54, 0x56]) c.boundDigest

instance : VerifiableRace IntervalQuery IntervalCertWrapper where
  isValid q c :=
    let baseOk :=
      match intervalCheck 100 q c.cert with
      | .ok => true
      | _ => false
    match c.refinedBound with
    | none => baseOk
    | some refIv =>
      baseOk &&
      match evalInterval q.env q.expr with
      | some comp =>
        decide (q.claimedBound.lo ≤ refIv.lo ∧ refIv.lo ≤ comp.lo ∧
                comp.hi ≤ refIv.hi ∧ refIv.hi ≤ q.claimedBound.hi)
      | none => false
  cost q c :=
    -- Cost is the certificate's refined interval width (or evaluated enclosure width): tighter bounds achieve strictly lower cost
    let iv := match c.refinedBound with
      | some refIv => refIv
      | none => (evalInterval q.env q.expr).getD q.claimedBound
    (iv.hi - iv.lo).num.natAbs
  digest c := intervalCertDigest c

end IntervalRace

/-! ## §7. Weighted Trust-Graph Seed-Cut Sybil Bound (`sybilSeedCutBound`, `epistemic_sybil_bounded_by_seed_cut`) -/

/-- Directed trust edge from `source` to `target` carrying `flow` (routed epistemic influence)
    bounded by `capacity` (trust weight). -/
structure TrustEdge where
  source   : Nat
  target   : Nat
  flow     : Nat
  capacity : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Check whether `e` crosses the honest-to-Sybil seed cut (`!isSybil e.source && isSybil e.target`). -/
def isSeedCutEdge (isSybil : Nat → Bool) (e : TrustEdge) : Bool :=
  !(isSybil e.source) && isSybil e.target

/-- Capacity of the honest-to-Sybil seed cut (`sybilSeedCutBound`):
    total trust capacity of edges crossing from honest nodes into the Sybil region. -/
def sybilSeedCutBound (isSybil : Nat → Bool) : List TrustEdge → Nat
  | [] => 0
  | e :: rest =>
    (if isSeedCutEdge isSybil e then e.capacity else 0) +
      sybilSeedCutBound isSybil rest

/-- Total routed influence entering the Sybil region across the honest-to-Sybil seed cut. -/
def sybilTotalInfluence (isSybil : Nat → Bool) : List TrustEdge → Nat
  | [] => 0
  | e :: rest =>
    (if isSeedCutEdge isSybil e then e.flow else 0) +
      sybilTotalInfluence isSybil rest

/-- Proposition that every edge in the trust graph respects its capacity (`e.flow ≤ e.capacity`). -/
def EdgesRespectCapacity : List TrustEdge → Prop
  | [] => True
  | e :: rest => e.flow ≤ e.capacity ∧ EdgesRespectCapacity rest

/-- Boolean checker for `EdgesRespectCapacity`. -/
def checkEdgesRespectCapacity : List TrustEdge → Bool
  | [] => true
  | e :: rest => decide (e.flow ≤ e.capacity) && checkEdgesRespectCapacity rest

theorem edgesRespectCapacity_of_check
    {edges : List TrustEdge}
    (h : checkEdgesRespectCapacity edges = true) :
    EdgesRespectCapacity edges := by
  induction edges with
  | nil => trivial
  | cons e rest ih =>
    simp only [checkEdgesRespectCapacity, Bool.and_eq_true, decide_eq_true_iff] at h
    exact ⟨h.1, ih h.2⟩

/-- Adding arbitrary internal Sybil-to-Sybil edges (`isSybil e.source = true`) leaves
    `sybilSeedCutBound` strictly invariant. -/
theorem sybilSeedCutBound_invariant_under_sybil_cloning
    (isSybil : Nat → Bool)
    (e : TrustEdge)
    (edges : List TrustEdge)
    (h_sybil_src : isSybil e.source = true) :
    sybilSeedCutBound isSybil (e :: edges) = sybilSeedCutBound isSybil edges := by
  simp [sybilSeedCutBound, isSeedCutEdge, h_sybil_src]

/-- Total influence crossing the honest-to-Sybil cut is bounded by `sybilSeedCutBound`. -/
theorem sybilTotalInfluence_le_seedCutBound
    (isSybil : Nat → Bool) :
    ∀ (edges : List TrustEdge),
      EdgesRespectCapacity edges →
      sybilTotalInfluence isSybil edges ≤ sybilSeedCutBound isSybil edges
  | [], _ => Nat.le_refl 0
  | e :: rest, ⟨h_cap, h_rest⟩ => by
    simp only [sybilTotalInfluence, sybilSeedCutBound]
    have ih := sybilTotalInfluence_le_seedCutBound isSybil rest h_rest
    cases isSeedCutEdge isSybil e <;> simp <;> omega

/-- **Weighted Trust-Graph Sybil Seed-Cut Theorem (`epistemic_sybil_bounded_by_seed_cut`)**:
    For any Sybil region `isSybil`, weighted trust graph `edges` respecting edge capacities
    (`EdgesRespectCapacity edges`), and any net Sybil region influence `sybilRegionInfluence`
    conserved by the cut (`sybilRegionInfluence ≤ sybilTotalInfluence isSybil edges`),
    the total influence of the Sybil region is bounded by the capacity of the honest-to-Sybil
    seed cut (`sybilSeedCutBound isSybil edges`). -/
theorem epistemic_sybil_bounded_by_seed_cut
    (isSybil : Nat → Bool)
    (edges : List TrustEdge)
    (sybilRegionInfluence : Nat)
    (h_cap : EdgesRespectCapacity edges)
    (h_conservation : sybilRegionInfluence ≤ sybilTotalInfluence isSybil edges) :
    sybilRegionInfluence ≤ sybilSeedCutBound isSybil edges :=
  Nat.le_trans h_conservation (sybilTotalInfluence_le_seedCutBound isSybil edges h_cap)

end Obend.Consensus.Epistemic
