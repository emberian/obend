module
/-
# Obend.Consensus.Epistemic — S5 Epistemic Consensus, Distributed Knowledge, and Solver Races

Mathlib-free port of `minidregg/Theory/EpistemicConsensus.lean` integrated with
Obend's `VerifiableRace` deterministic race selector and `Simplex` quorum intersection:

## Metatheorems:
- `winner_is_valid` & `winner_mem`: selected winner belongs to the pool and passes verification.
- `frontrunning_resistant_pair`: inferior or invalid candidates cannot displace a better winner.
- `order_insensitive_perm` & `order_insensitive_pair`: candidate arrival permutation (`List.Perm`)
  does not affect the selected winner whenever candidate digests distinguish valid entries.
- S5 Kripke frames (`EpistemicFrame` with `indist_refl`, `indist_symm`, `indist_trans`):
  `knows_truth` (T), `knows_pos_introspection` (4), `knows_neg_introspection` (5),
  `distKnows_truth`, `distKnows_mono_group`, `knows_imp_distKnows`.
- Byzantine-proof verification (`dischargedProp`, `knows_discharged_iff`,
  `distKnows_discharged_iff`, `knows_discharged_frame_independent`,
  `holds_of_honest_distKnows`, `no_dist_knowledge_of_invalid`,
  `honest_dist_knowledge_composes`).
- `epistemic_quorum_pooled_knowledge` & `epistemic_quorum_agreement`: bridges
  `Simplex.honest_quorum_intersection` with S5 `Knows`/`DistKnows` to prove two `2f + 1`
  epistemic quorums in a `3f + 1` committee pool consistent knowledge and cannot disagree.
-/

public import Obend.Core.Data
public import Obend.Consensus.Simplex
public import Obend.Digest.Cshake256.Seam
public import Obend.Judge.Clearing
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis

@[expose] public section
namespace Obend.Consensus.Epistemic

open Obend.Core.Data
open Obend.Consensus.Simplex (NodeId honest_quorum_intersection)
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
  byteListLt a.data.toList b.data.toList

theorem byteListLt_irreflexive (bs : List UInt8) : byteListLt bs bs = false := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    unfold byteListLt
    have hnot : ¬ (b.toNat < b.toNat) := Nat.lt_irrefl b.toNat
    simp [hnot, ih]

theorem byteArrayLt_irreflexive (b : ByteArray) : byteArrayLt b b = false :=
  byteListLt_irreflexive b.data.toList

theorem byteListLt_asymmetric {a b : List UInt8} (h : byteListLt a b = true) :
    byteListLt b a = false := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => contradiction
    | cons _ _ => rfl
  | cons x xs ih =>
    cases b with
    | nil => contradiction
    | cons y ys =>
      unfold byteListLt at h ⊢
      by_cases hxy : x.toNat < y.toNat
      · have hyx : ¬ (y.toNat < x.toNat) := by omega
        simp [hyx, hxy]
      · by_cases hyx : y.toNat < x.toNat
        · simp [hxy, hyx] at h
        · simp only [hxy, hyx, ↓reduceIte] at h ⊢
          exact ih h

theorem byteArrayLt_asymmetric {a b : ByteArray} (h : byteArrayLt a b = true) :
    byteArrayLt b a = false :=
  byteListLt_asymmetric h

theorem byteListLt_trans {a b c : List UInt8}
    (hab : byteListLt a b = true) (hbc : byteListLt b c = true) :
    byteListLt a c = true := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => simp [byteListLt] at hab
    | cons y ys =>
      cases c with
      | nil => simp [byteListLt] at hbc
      | cons _ _ => rfl
  | cons x xs ih =>
    cases b with
    | nil => simp [byteListLt] at hab
    | cons y ys =>
      cases c with
      | nil => simp [byteListLt] at hbc
      | cons z zs =>
        unfold byteListLt at hab hbc ⊢
        by_cases hxy : x.toNat < y.toNat
        · simp only [hxy, ↓reduceIte] at hab
          by_cases hyz : y.toNat < z.toNat
          · have hxz : x.toNat < z.toNat := Nat.lt_trans hxy hyz
            simp [hxz]
          · by_cases hzy : z.toNat < y.toNat
            · simp [hyz, hzy] at hbc
            · have hyz_eq : y.toNat = z.toNat := by omega
              have hxz : x.toNat < z.toNat := hyz_eq ▸ hxy
              simp [hxz]
        · by_cases hyx : y.toNat < x.toNat
          · simp [hxy, hyx] at hab
          · simp only [hxy, hyx, ↓reduceIte] at hab
            have hxy_eq : x.toNat = y.toNat := by omega
            by_cases hyz : y.toNat < z.toNat
            · have hxz : x.toNat < z.toNat := hxy_eq ▸ hyz
              simp [hxz]
            · by_cases hzy : z.toNat < y.toNat
              · simp [hyz, hzy] at hbc
              · simp only [hyz, hzy, ↓reduceIte] at hbc
                have hyz_eq : y.toNat = z.toNat := by omega
                have hnot1 : ¬ (x.toNat < z.toNat) := by omega
                have hnot2 : ¬ (z.toNat < x.toNat) := by omega
                simp only [hnot1, hnot2, ↓reduceIte]
                exact ih hab hbc

private theorem uint8_eq_of_toNat_eq {x y : UInt8} (h : x.toNat = y.toNat) : x = y := by
  cases x with
  | ofBitVec bx =>
    cases y with
    | ofBitVec by_ =>
      cases bx with
      | ofFin fx =>
        cases by_ with
        | ofFin fy =>
          cases fx with
          | mk vx hx =>
            cases fy with
            | mk vy hy =>
              simp [UInt8.toNat] at h
              subst h
              rfl

theorem byteListLt_trichotomous (a b : List UInt8) :
    a = b ∨ byteListLt a b = true ∨ byteListLt b a = true := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact .inl rfl
    | cons _ _ => exact .inr (.inl rfl)
  | cons x xs ih =>
    cases b with
    | nil => exact .inr (.inr rfl)
    | cons y ys =>
      unfold byteListLt
      by_cases hxy : x.toNat < y.toNat
      · exact .inr (.inl (by simp [hxy]))
      · by_cases hyx : y.toNat < x.toNat
        · have hnot : ¬ (x.toNat < y.toNat) := hxy
          exact .inr (.inr (by simp [hyx]))
        · have heq_nat : x.toNat = y.toNat := by omega
          have heq : x = y := uint8_eq_of_toNat_eq heq_nat
          subst heq
          have hnot : ¬ (x.toNat < x.toNat) := Nat.lt_irrefl _
          simp only [hnot, ↓reduceIte]
          rcases ih ys with rfl | hab | hba
          · exact .inl rfl
          · exact .inr (.inl hab)
          · exact .inr (.inr hba)

theorem byteArray_eq_of_data_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      cases da with
      | mk la =>
        cases db with
        | mk lb =>
          cases h
          rfl

theorem byteArrayLt_trans {a b c : ByteArray}
    (hab : byteArrayLt a b = true) (hbc : byteArrayLt b c = true) :
    byteArrayLt a c = true :=
  byteListLt_trans hab hbc

theorem byteArrayLt_trichotomous (a b : ByteArray) :
    a = b ∨ byteArrayLt a b = true ∨ byteArrayLt b a = true := by
  rcases byteListLt_trichotomous a.data.toList b.data.toList with heq | hab | hba
  · exact .inl (byteArray_eq_of_data_toList_eq heq)
  · exact .inr (.inl hab)
  · exact .inr (.inr hba)

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
    simp [h21, h12]
  · by_cases h21 : certCost q c₂ < certCost q c₁
    · simp [h12, h21] at h
    · simp only [h12, h21, ↓reduceIte] at h ⊢
      exact byteArrayLt_asymmetric h

theorem betterCert_trans {q : Q} {a b c : Cert}
    (hab : betterCert q a b = true) (hbc : betterCert q b c = true) :
    betterCert q a c = true := by
  unfold betterCert at hab hbc ⊢
  by_cases hab_cost : certCost q a < certCost q b
  · by_cases hbc_cost : certCost q b < certCost q c
    · have hac : certCost q a < certCost q c := Nat.lt_trans hab_cost hbc_cost
      simp [hac]
    · by_cases hcb_cost : certCost q c < certCost q b
      · simp [hbc_cost, hcb_cost] at hbc
      · have hbc_eq : certCost q b = certCost q c := by omega
        have hac : certCost q a < certCost q c := hbc_eq ▸ hab_cost
        simp [hac]
  · by_cases hba_cost : certCost q b < certCost q a
    · simp [hab_cost, hba_cost] at hab
    · simp only [hab_cost, hba_cost, ↓reduceIte] at hab
      have hab_eq : certCost q a = certCost q b := by omega
      by_cases hbc_cost : certCost q b < certCost q c
      · have hac : certCost q a < certCost q c := hab_eq ▸ hbc_cost
        simp [hac]
      · by_cases hcb_cost : certCost q c < certCost q b
        · simp [hbc_cost, hcb_cost] at hbc
        · simp only [hbc_cost, hcb_cost, ↓reduceIte] at hbc
          have hbc_eq : certCost q b = certCost q c := by omega
          have hnot1 : ¬ (certCost q a < certCost q c) := by omega
          have hnot2 : ¬ (certCost q c < certCost q a) := by omega
          simp only [hnot1, hnot2, ↓reduceIte]
          exact byteArrayLt_trans hab hbc

/-- Pairwise trichotomy of `betterCert q` on a candidate list `l`. -/
def TrichotomousOn (q : Q) (l : List Cert) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, x = y ∨ betterCert q x y = true ∨ betterCert q y x = true

/-- Digest collision-freedom on a candidate list `l`. -/
def DigestInjOn (q : Q) (l : List Cert) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, certDigest q x = certDigest q y → x = y

theorem trichotomousOn_of_digestInj {q : Q} {l : List Cert}
    (hinj : DigestInjOn q l) : TrichotomousOn q l := by
  intro x hx y hy
  unfold betterCert
  by_cases hxy : certCost q x < certCost q y
  · exact .inr (.inl (by simp [hxy]))
  · by_cases hyx : certCost q y < certCost q x
    · exact .inr (.inr (by simp [hyx]))
    · simp only [hxy, hyx, ↓reduceIte]
      rcases byteArrayLt_trichotomous (certDigest q x) (certDigest q y) with hdig | hlt | hgt
      · exact .inl (hinj x hx y hy hdig)
      · exact .inr (.inl hlt)
      · exact .inr (.inr hgt)

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

/-! ## §4. Consensus & `List.Perm` Order-Insensitivity Metatheorems -/

theorem pickBest_mem (q : Q) (candidates : List Cert) :
    ∀ w, pickBest q candidates = some w → w ∈ candidates := by
  induction candidates with
  | nil => intro _ h; contradiction
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
      | head => exact ⟨List.Mem.head ys, hp⟩
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

private def chooseBetter (q : Q) (x y : Cert) : Cert :=
  if betterCert q x y then x else y

private theorem chooseBetter_comm {q : Q} {a b : Cert}
    (htri : a = b ∨ betterCert q a b = true ∨ betterCert q b a = true) :
    chooseBetter q a b = chooseBetter q b a := by
  rcases htri with rfl | hab | hba
  · rfl
  · simp [chooseBetter, hab, betterCert_asymmetric hab]
  · simp [chooseBetter, hba, betterCert_asymmetric hba]

private theorem chooseBetter_left_comm {q : Q} {a b m : Cert}
    (ht_ab : a = b ∨ betterCert q a b = true ∨ betterCert q b a = true)
    (ht_am : a = m ∨ betterCert q a m = true ∨ betterCert q m a = true)
    (ht_bm : b = m ∨ betterCert q b m = true ∨ betterCert q m b = true) :
    chooseBetter q a (chooseBetter q b m) = chooseBetter q b (chooseBetter q a m) := by
  unfold chooseBetter
  cases hbm : betterCert q b m with
  | true =>
    cases ham : betterCert q a m with
    | true =>
      exact chooseBetter_comm ht_ab
    | false =>
      rcases ht_am with rfl | ham_t | hma
      · simp [betterCert_asymmetric hbm, hbm]
      · rw [ham_t] at ham; cases ham
      · have hba : betterCert q b a = true := betterCert_trans hbm hma
        simp [betterCert_asymmetric hba, hbm]
  | false =>
    cases ham : betterCert q a m with
    | true =>
      rcases ht_bm with rfl | hbm_t | hmb
      · simp [ham, betterCert_asymmetric ham]
      · rw [hbm_t] at hbm; cases hbm
      · have hab : betterCert q a b = true := betterCert_trans ham hmb
        simp [ham, betterCert_asymmetric hab]
    | false =>
      simp [ham, hbm]

private theorem perm_mem_right {α : Type} {l₁ l₂ : List α} (hp : l₁.Perm l₂) :
    ∀ {x : α}, x ∈ l₂ → x ∈ l₁ := by
  induction hp with
  | nil => intro _ h; exact h
  | cons y _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hmem
    · exact .head _
    · exact .tail y (ih hmem)
  | swap y z l =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hmem
    · exact .tail z (.head l)
    · rcases List.mem_cons.1 hmem with rfl | hmem'
      · exact .head _
      · exact .tail z (.tail y hmem')
  | trans _ _ ih₁ ih₂ =>
    intro x hx
    exact ih₁ (ih₂ hx)

private theorem perm_filter_local {α : Type} (p : α → Bool) {l₁ l₂ : List α}
    (hp : l₁.Perm l₂) : (l₁.filter p).Perm (l₂.filter p) := by
  induction hp with
  | nil => exact .nil
  | cons x _ ih =>
    simp only [List.filter_cons]
    cases p x with
    | true => exact .cons x ih
    | false => exact ih
  | swap x y l =>
    simp only [List.filter_cons]
    cases p x <;> cases p y
    · exact List.Perm.refl _
    · exact List.Perm.refl _
    · exact List.Perm.refl _
    · exact .swap x y (l.filter p)
  | trans _ _ ih₁ ih₂ =>
    exact ih₁.trans ih₂

theorem pickBest_swap {q : Q} {a b : Cert} {cs : List Cert}
    (htri : TrichotomousOn q (a :: b :: cs)) :
    pickBest q (a :: b :: cs) = pickBest q (b :: a :: cs) := by
  have ht_ab : a = b ∨ betterCert q a b = true ∨ betterCert q b a = true :=
    htri a (.head _) b (.tail a (.head cs))
  simp only [pickBest]
  cases hcs : pickBest q cs with
  | none =>
    have hc := chooseBetter_comm ht_ab
    unfold chooseBetter at hc
    cases hab : betterCert q a b <;> cases hba : betterCert q b a <;> simp_all
  | some m =>
    have hm : m ∈ cs := pickBest_mem q cs m hcs
    have ht_am : a = m ∨ betterCert q a m = true ∨ betterCert q m a = true :=
      htri a (.head _) m (.tail a (.tail b hm))
    have ht_bm : b = m ∨ betterCert q b m = true ∨ betterCert q m b = true :=
      htri b (.tail a (.head cs)) m (.tail a (.tail b hm))
    have hc := chooseBetter_left_comm ht_ab ht_am ht_bm
    unfold chooseBetter at hc
    cases hbm : betterCert q b m <;> cases ham : betterCert q a m <;>
      cases hab : betterCert q a b <;> cases hba : betterCert q b a <;>
      simp_all

theorem pickBest_perm {q : Q} {l₁ l₂ : List Cert}
    (hp : l₁.Perm l₂) (htri : TrichotomousOn q l₁) :
    pickBest q l₁ = pickBest q l₂ := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    have htri_tail : TrichotomousOn q _ :=
      fun a ha b hb => htri a (.tail x ha) b (.tail x hb)
    unfold pickBest
    rw [ih htri_tail]
  | swap x y l =>
    exact pickBest_swap htri
  | trans hp₁ _ ih₁ ih₂ =>
    have htri₂ : TrichotomousOn q _ :=
      fun a ha b hb => htri a (perm_mem_right hp₁ ha) b (perm_mem_right hp₁ hb)
    exact (ih₁ htri).trans (ih₂ htri₂)

/-- **General Permutation Invariance (`order_insensitive_perm`)**:
    For any candidate arrival permutation `l₁.Perm l₂` whose valid candidates satisfy
    pairwise trichotomy (`TrichotomousOn q (l₁.filter (certValid q))`), `selectWinner`
    selects the exact same winner regardless of arrival order. -/
theorem order_insensitive_perm {q : Q} {l₁ l₂ : List Cert}
    (hp : l₁.Perm l₂)
    (htri : TrichotomousOn q (l₁.filter (certValid q))) :
    selectWinner q l₁ = selectWinner q l₂ :=
  pickBest_perm (perm_filter_local (certValid q) hp) htri

/-- Permutation invariance specialized to candidate pools with distinct digests on valid entries. -/
theorem order_insensitive_perm_of_digestInj {q : Q} {l₁ l₂ : List Cert}
    (hp : l₁.Perm l₂)
    (hinj : DigestInjOn q (l₁.filter (certValid q))) :
    selectWinner q l₁ = selectWinner q l₂ :=
  order_insensitive_perm hp (trichotomousOn_of_digestInj hinj)

/-- Determinism on permutations of two candidates (`[c₁, c₂]` vs `[c₂, c₁]`),
    derived directly from `order_insensitive_perm`. -/
theorem order_insensitive_pair {q : Q} {c₁ c₂ : Cert}
    (h1 : certValid q c₁ = true)
    (h2 : certValid q c₂ = true)
    (hdiff : betterCert q c₁ c₂ = true) :
    selectWinner q [c₁, c₂] = selectWinner q [c₂, c₁] := by
  apply order_insensitive_perm (.swap c₂ c₁ [])
  intro x hx y hy
  simp only [List.filter_cons, h1, h2, ↓reduceIte, List.filter_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl hdiff)
  · exact .inr (.inr hdiff)
  · exact .inl rfl

/-! ## §5. S5 Epistemic Kripke Frames & Distributed Knowledge (`minidregg` Port) -/

/-- An **S5 Epistemic Frame** with Byzantine participants (Goubault–Kniazev–Ledent–Rajsbaum):
    each agent's indistinguishability relation `Indist a` is an equivalence relation
    (`indist_refl`, `indist_symm`, `indist_trans`). -/
structure EpistemicFrame (Ω Agent : Type) where
  actual : Ω
  Indist : Agent → Ω → Ω → Prop
  indist_refl : ∀ a w, Indist a w w
  indist_symm : ∀ a {w₁ w₂}, Indist a w₁ w₂ → Indist a w₂ w₁
  indist_trans : ∀ a {w₁ w₂ w₃}, Indist a w₁ w₂ → Indist a w₂ w₃ → Indist a w₁ w₃
  Faulty : Agent → Prop

/-- The world-independent proposition that certificate `c` validly discharges query `q`. -/
def dischargedProp {Ω : Type} (q : Q) (c : Cert) : Ω → Prop :=
  fun _ => certValid q c = true

namespace EpistemicFrame

variable {Ω Agent : Type} (F : EpistemicFrame Ω Agent)

def Honest (a : Agent) : Prop := ¬ F.Faulty a

/-- Single-agent knowledge modality `Kₐ φ` at world `w`. -/
def Knows (a : Agent) (φ : Ω → Prop) (w : Ω) : Prop :=
  ∀ w', F.Indist a w' w → φ w'

/-- Group mutual knowledge `E_B φ` at world `w`: every member of `B` knows `φ`. -/
def EveryoneKnows (B : Agent → Prop) (φ : Ω → Prop) (w : Ω) : Prop :=
  ∀ a, B a → F.Knows a φ w

/-- Distributed knowledge `D_B φ` at world `w`: `φ` holds at every world that *every*
    member of `B` confuses with `w`. -/
def DistKnows (B : Agent → Prop) (φ : Ω → Prop) (w : Ω) : Prop :=
  ∀ w', (∀ a, B a → F.Indist a w' w) → φ w'

/-! ### S5 Modal Laws (K, T, 4, 5) -/

/-- **Axiom K (Distribution)**: `Kₐ (φ → ψ) → Kₐ φ → Kₐ ψ`. -/
theorem knows_mp {a : Agent} {φ ψ : Ω → Prop} {w : Ω}
    (himp : F.Knows a (fun w' => φ w' → ψ w') w)
    (hφ : F.Knows a φ w) :
    F.Knows a ψ w :=
  fun w' hind => himp w' hind (hφ w' hind)

/-- **Axiom T (Veridicality / Truth)**: what an agent knows actually holds (`Kₐ φ → φ`). -/
theorem knows_truth {a : Agent} {φ : Ω → Prop} {w : Ω}
    (hk : F.Knows a φ w) : φ w :=
  hk w (F.indist_refl a w)

/-- **Axiom 4 (Positive Introspection)**: `Kₐ φ → Kₐ (Kₐ φ)`. -/
theorem knows_pos_introspection {a : Agent} {φ : Ω → Prop} {w : Ω}
    (hk : F.Knows a φ w) : F.Knows a (fun w' => F.Knows a φ w') w :=
  fun _ hw' w'' hw'' => hk w'' (F.indist_trans a hw'' hw')

/-- **Axiom 5 (Negative Introspection)**: `¬ Kₐ φ → Kₐ (¬ Kₐ φ)`. -/
theorem knows_neg_introspection {a : Agent} {φ : Ω → Prop} {w : Ω}
    (hnk : ¬ F.Knows a φ w) : F.Knows a (fun w' => ¬ F.Knows a φ w') w :=
  fun _ hw' hk' => hnk (fun w'' hw'' => hk' w'' (F.indist_trans a hw'' (F.indist_symm a hw')))

/-- **Distributed Truth**: what a group distributedly knows holds at `w`. -/
theorem distKnows_truth {B : Agent → Prop} {φ : Ω → Prop} {w : Ω}
    (hdk : F.DistKnows B φ w) : φ w :=
  hdk w (fun a _ => F.indist_refl a w)

/-- **Group Monotonicity**: a larger group distributedly knows at least as much (`B ⊆ B'`). -/
theorem distKnows_mono_group {B B' : Agent → Prop}
    (hsub : ∀ a, B a → B' a) {φ : Ω → Prop} {w : Ω}
    (h : F.DistKnows B φ w) : F.DistKnows B' φ w :=
  fun w' hall => h w' (fun a ha => hall a (hsub a ha))

/-- **Single-Agent Entails Distributed Knowledge**: if `a ∈ B` knows `φ`, `B` distributedly knows `φ`. -/
theorem knows_imp_distKnows {B : Agent → Prop} {a : Agent} (ha : B a)
    {φ : Ω → Prop} {w : Ω} (hk : F.Knows a φ w) :
    F.DistKnows B φ w :=
  fun w' hall => hk w' (hall a ha)

/-! ### Fault-Tolerant Distributed Knowledge by Verification -/

/-- World-independence: validity of a discharged certificate does not depend on world state. -/
theorem discharged_world_independent (q : Q) (c : Cert) (w w' : Ω) :
    dischargedProp (Ω := Ω) q c w ↔ dischargedProp (Ω := Ω) q c w' :=
  Iff.rfl

/-- Every agent knows a valid certificate, regardless of network or local perspective. -/
theorem all_know_verified (q : Q) (c : Cert) (hval : certValid q c = true) (a : Agent) :
    F.Knows a (dischargedProp (Ω := Ω) q c) F.actual :=
  fun _ _ => hval

/-- Single-agent knowledge of `dischargedProp q c` is equivalent to `certValid q c = true`. -/
theorem knows_discharged_iff (q : Q) (c : Cert) (a : Agent) (w : Ω) :
    F.Knows a (dischargedProp (Ω := Ω) q c) w ↔ certValid q c = true :=
  ⟨fun hk => hk w (F.indist_refl a w), fun hval _ _ => hval⟩

/-- Distributed knowledge of `dischargedProp q c` is equivalent to `certValid q c = true`
    for ANY group `B`, independent of which agents are `Faulty`. -/
theorem distKnows_discharged_iff (q : Q) (c : Cert) (B : Agent → Prop) (w : Ω) :
    F.DistKnows B (dischargedProp (Ω := Ω) q c) w ↔ certValid q c = true :=
  ⟨fun hdk => hdk w (fun a _ => F.indist_refl a w), fun hval _ _ => hval⟩

/-- Frame-independence: two arbitrary S5 frames agree on knowledge of `dischargedProp`. -/
theorem knows_discharged_frame_independent (q : Q) (c : Cert)
    (F₁ F₂ : EpistemicFrame Ω Agent) (a₁ a₂ : Agent) (w₁ w₂ : Ω) :
    F₁.Knows a₁ (dischargedProp (Ω := Ω) q c) w₁ ↔
      F₂.Knows a₂ (dischargedProp (Ω := Ω) q c) w₂ :=
  (F₁.knows_discharged_iff q c a₁ w₁).trans (F₂.knows_discharged_iff q c a₂ w₂).symm

/-- Distributed knowledge of the honest committee over a valid certificate. -/
theorem honest_distKnows_verified (q : Q) (c : Cert) (hval : certValid q c = true) :
    F.DistKnows F.Honest (dischargedProp (Ω := Ω) q c) F.actual :=
  fun _ _ => hval

/-- Unforgeability: honest distributed knowledge of `dischargedProp` implies validity. -/
theorem holds_of_honest_distKnows (q : Q) (c : Cert)
    (hdk : F.DistKnows F.Honest (dischargedProp (Ω := Ω) q c) F.actual) :
    certValid q c = true :=
  (F.distKnows_discharged_iff q c F.Honest F.actual).mp hdk

/-- Byzantine subset cannot forge distributed knowledge of an invalid certificate. -/
theorem no_dist_knowledge_of_invalid (q : Q) (c : Cert) (hinval : certValid q c = false) :
    ¬ F.DistKnows F.Honest (dischargedProp (Ω := Ω) q c) F.actual := by
  intro hdk
  have h := F.holds_of_honest_distKnows q c hdk
  rw [hinval] at h
  contradiction

/-- Static composition: honest distributed knowledge of two valid certificates pools into
    distributed knowledge of their conjunction. -/
theorem honest_dist_knowledge_composes (q₁ q₂ : Q) (c₁ c₂ : Cert)
    (h₁ : F.DistKnows F.Honest (dischargedProp (Ω := Ω) q₁ c₁) F.actual)
    (h₂ : F.DistKnows F.Honest (dischargedProp (Ω := Ω) q₂ c₂) F.actual) :
    F.DistKnows F.Honest
      (fun w => dischargedProp (Ω := Ω) q₁ c₁ w ∧ dischargedProp (Ω := Ω) q₂ c₂ w) F.actual :=
  fun w' hall => ⟨h₁ w' hall, h₂ w' hall⟩

end EpistemicFrame

/-! ### Epistemic Quorum Agreement (Bridging `Simplex.honest_quorum_intersection` to S5 `DistKnows`) -/

/-- **Epistemic Quorum Pooled Knowledge**:
    In any S5 `EpistemicFrame Ω NodeId` over a `3f + 1` committee with at most `f` faulty
    validators, if every honest member of quorum `q₁` (`≥ 2f + 1`) knows `φ₁` at `F.actual`
    and every honest member of quorum `q₂` (`≥ 2f + 1`) knows `φ₂` at `F.actual`, then
    there exists an honest validator in both quorums who knows `φ₁ ∧ φ₂`, and the honest
    committee holds distributed knowledge `F.DistKnows F.Honest (fun w => φ₁ w ∧ φ₂ w) F.actual`. -/
theorem epistemic_quorum_pooled_knowledge {Ω : Type}
    (F : EpistemicFrame Ω NodeId)
    (committee : List NodeId) (f : Nat)
    (q₁ q₂ faulty : NodeId → Bool)
    (φ₁ φ₂ : Ω → Prop)
    (h_faulty_align : ∀ n, F.Faulty n ↔ faulty n = true)
    (h_size : committee.length = 3 * f + 1)
    (h_q1 : 2 * f + 1 ≤ (committee.filter q₁).length)
    (h_q2 : 2 * f + 1 ≤ (committee.filter q₂).length)
    (h_faulty : (committee.filter faulty).length ≤ f)
    (hk₁ : ∀ n ∈ committee, q₁ n = true → F.Honest n → F.Knows n φ₁ F.actual)
    (hk₂ : ∀ n ∈ committee, q₂ n = true → F.Honest n → F.Knows n φ₂ F.actual) :
    (∃ n ∈ committee, F.Honest n ∧ F.Knows n (fun w => φ₁ w ∧ φ₂ w) F.actual) ∧
    F.DistKnows F.Honest (fun w => φ₁ w ∧ φ₂ w) F.actual ∧
    (φ₁ F.actual ∧ φ₂ F.actual) := by
  obtain ⟨n, hn_mem, h1, h2, hnf⟩ :=
    honest_quorum_intersection committee f q₁ q₂ faulty h_size h_q1 h_q2 h_faulty
  have h_honest : F.Honest n := by
    intro hf
    have hft := (h_faulty_align n).mp hf
    rw [hnf] at hft
    cases hft
  have h_both : F.Knows n (fun w => φ₁ w ∧ φ₂ w) F.actual :=
    fun w' hind => ⟨hk₁ n hn_mem h1 h_honest w' hind, hk₂ n hn_mem h2 h_honest w' hind⟩
  have h_dk : F.DistKnows F.Honest (fun w => φ₁ w ∧ φ₂ w) F.actual :=
    F.knows_imp_distKnows h_honest h_both
  exact ⟨⟨n, hn_mem, h_honest, h_both⟩, h_dk, F.distKnows_truth h_dk⟩

/-- **Epistemic Quorum Agreement**:
    If `φ₁` and `φ₂` witness decisions `val₁` and `val₂` that cannot co-hold on any world
    unless `val₁ = val₂`, then any two `2f + 1` epistemic quorums in a `3f + 1` committee
    must agree (`val₁ = val₂`). -/
theorem epistemic_quorum_agreement {Ω α : Type} {val₁ val₂ : α}
    (F : EpistemicFrame Ω NodeId)
    (committee : List NodeId) (f : Nat)
    (q₁ q₂ faulty : NodeId → Bool)
    (φ₁ φ₂ : Ω → Prop)
    (h_faulty_align : ∀ n, F.Faulty n ↔ faulty n = true)
    (h_size : committee.length = 3 * f + 1)
    (h_q1 : 2 * f + 1 ≤ (committee.filter q₁).length)
    (h_q2 : 2 * f + 1 ≤ (committee.filter q₂).length)
    (h_faulty : (committee.filter faulty).length ≤ f)
    (hk₁ : ∀ n ∈ committee, q₁ n = true → F.Honest n → F.Knows n φ₁ F.actual)
    (hk₂ : ∀ n ∈ committee, q₂ n = true → F.Honest n → F.Knows n φ₂ F.actual)
    (h_exclusive : ∀ w, φ₁ w → φ₂ w → val₁ = val₂) :
    val₁ = val₂ := by
  have ⟨_, _, hφ₁, hφ₂⟩ :=
    epistemic_quorum_pooled_knowledge F committee f q₁ q₂ faulty φ₁ φ₂
      h_faulty_align h_size h_q1 h_q2 h_faulty hk₁ hk₂
  exact h_exclusive F.actual hφ₁ hφ₂

/-! ### Finite S5 Discriminating Keystone Frame -/

namespace Keystone

/-- Two-world (`Bool`), two-agent (`Fin 2`) S5 frame:
    agent `0` distinguishes worlds (`w₁ = w₂`), agent `1` confuses them (`True`) and is faulty. -/
def frame : EpistemicFrame Bool (Fin 2) where
  actual := true
  Indist := fun i w₁ w₂ => i = 0 → w₁ = w₂
  indist_refl := fun _ _ _ => rfl
  indist_symm := by intro _ _ _ h hi; exact (h hi).symm
  indist_trans := by intro _ _ _ _ h₁ h₂ hi; exact (h₁ hi).trans (h₂ hi)
  Faulty := fun i => i = 1

def actualWorldProp : Bool → Prop := fun w => w = true

def everyoneGroup : Fin 2 → Prop := fun _ => True

/-- Satisfiable (`Knows`): seeing agent `0` knows `actualWorldProp`. -/
theorem agent0_knows : frame.Knows 0 actualWorldProp frame.actual :=
  fun _ h => h rfl

/-- Teeth (`Knows`): blind agent `1` does NOT know `actualWorldProp`. -/
theorem agent1_not_knows : ¬ frame.Knows 1 actualWorldProp frame.actual := by
  intro hk
  have hfalse : actualWorldProp false := hk false (fun h10 => absurd h10 (by decide))
  cases hfalse

/-- Satisfiable (`DistKnows`): the pooled group `{0, 1}` distributedly knows `actualWorldProp`. -/
theorem group_distKnows : frame.DistKnows everyoneGroup actualWorldProp frame.actual :=
  fun _ hall => hall 0 trivial rfl

/-- Teeth (`DistKnows`): the Byzantine subset `{1}` alone does NOT distributedly know `actualWorldProp`. -/
theorem faulty_alone_not_distKnows : ¬ frame.DistKnows frame.Faulty actualWorldProp frame.actual := by
  intro hdk
  have hfalse : actualWorldProp false :=
    hdk false (fun i hi => by subst hi; intro h10; exact absurd h10 (by decide))
  cases hfalse

end Keystone

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
    let iv := match c.refinedBound with
      | some refIv => refIv
      | none => (evalInterval q.env q.expr).getD q.claimedBound
    (iv.hi - iv.lo).num.natAbs
  digest c := intervalCertDigest c

end IntervalRace

/-! ## §7. Weighted Trust-Graph Seed-Cut Sybil Bound -/

/-- Directed trust edge from `source` to `target` carrying `flow` bounded by `capacity`. -/
structure TrustEdge where
  source   : Nat
  target   : Nat
  flow     : Nat
  capacity : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def isSeedCutEdge (isSybil : Nat → Bool) (e : TrustEdge) : Bool :=
  !(isSybil e.source) && isSybil e.target

def sybilSeedCutBound (isSybil : Nat → Bool) : List TrustEdge → Nat
  | [] => 0
  | e :: rest =>
    (if isSeedCutEdge isSybil e then e.capacity else 0) +
      sybilSeedCutBound isSybil rest

def sybilTotalInfluence (isSybil : Nat → Bool) : List TrustEdge → Nat
  | [] => 0
  | e :: rest =>
    (if isSeedCutEdge isSybil e then e.flow else 0) +
      sybilTotalInfluence isSybil rest

def EdgesRespectCapacity : List TrustEdge → Prop
  | [] => True
  | e :: rest => e.flow ≤ e.capacity ∧ EdgesRespectCapacity rest

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

theorem sybilSeedCutBound_invariant_under_sybil_cloning
    (isSybil : Nat → Bool)
    (e : TrustEdge)
    (edges : List TrustEdge)
    (h_sybil_src : isSybil e.source = true) :
    sybilSeedCutBound isSybil (e :: edges) = sybilSeedCutBound isSybil edges := by
  simp [sybilSeedCutBound, isSeedCutEdge, h_sybil_src]

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

theorem epistemic_sybil_bounded_by_seed_cut
    (isSybil : Nat → Bool)
    (edges : List TrustEdge)
    (sybilRegionInfluence : Nat)
    (h_cap : EdgesRespectCapacity edges)
    (h_conservation : sybilRegionInfluence ≤ sybilTotalInfluence isSybil edges) :
    sybilRegionInfluence ≤ sybilSeedCutBound isSybil edges :=
  Nat.le_trans h_conservation (sybilTotalInfluence_le_seedCutBound isSybil edges h_cap)

end Obend.Consensus.Epistemic
end
