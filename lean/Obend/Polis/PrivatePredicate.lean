module
/-
# Obend.Polis.PrivatePredicate — first-order distributed predicates, cSHAKE256-bound conservation, AEAD discharge

1. `DistPred`: injective byte-coded first-order distributed predicates (`DistPred.encode_injective`) + closure impossibility (`opaque_closure_collapses_finite_encoding`, `opaque_closure_escapes_descriptor_table`).
2. `DistPred.evalWith`: strong Kleene evaluation (`negated_witnessed_refused_firstParty`, `evalFirstParty_sound_for_evalWith`, `discharge_monotone`) and slot-hiding vat partial evaluation (`pevalVat_hides_known_slots`, `eval_subst_eq_eval_pevalVat`).
3. `Opening.bind` + `auditTransfer`: domain-separated 256-bit `cSHAKE256` commitment + pad-bijection hiding + audited blinding conservation (`privPred_conservation_extract`, `privPred_conservation_sound`), alongside explicit equivocation/forgery counterexamples (`demoKey_equivocates`, `homCheck_accepts_unblinded_forgery`) on raw `ℤ/2²⁵⁶` affine sums.
4. `aeadSeal` / `SealLedger` / `verifyDischarge`: full-coverage `cSHAKE256` counter-mode sealing (`keystreamFor_covers`), nonce-reuse leak proof + fresh-nonce ledger (`SealLedger`), and Macaroon third-party caveat discharge.
-/
public import Obend.Crypto.Transcript
public import Obend.Polis.EvidencedOcap
public import Obend.Polis.VerkleUmem

public section
namespace Obend.Polis.PrivatePredicate

open Obend.Polis
open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Slots, steps and the syntax -/

abbrev SlotId := Nat
structure VkId where
  id : ByteArray
  deriving DecidableEq

structure SlotStep where
  old : Option Int
  new : Option Int
  deriving DecidableEq

abbrev Step := SlotId → SlotStep

inductive SlotTest where
  | eq (value : Int) | le (value : Int) | memberOf (set : List Int)
  | writeOnce | monotone | hashEq (digest : ByteArray)
  deriving DecidableEq

mutual
inductive DistPred where
  | atom (slot : SlotId) (test : SlotTest) | witnessed (vk : VkId)
  | not (p : DistPred) | all (ps : DistPredList) | any (ps : DistPredList)
inductive DistPredList where
  | nil | cons (p : DistPred) (ps : DistPredList)
end
deriving instance DecidableEq for DistPred, DistPredList

namespace DistPred
abbrev eq (slot : SlotId) (value : Int) : DistPred := .atom slot (.eq value)
abbrev le (slot : SlotId) (value : Int) : DistPred := .atom slot (.le value)
abbrev memberOf (slot : SlotId) (set : List Int) : DistPred := .atom slot (.memberOf set)
abbrev writeOnce (slot : SlotId) : DistPred := .atom slot .writeOnce
abbrev monotone (slot : SlotId) : DistPred := .atom slot .monotone
abbrev hashEq (slot : SlotId) (digest : ByteArray) : DistPred := .atom slot (.hashEq digest)
abbrev tt : DistPred := .all .nil
abbrev ff : DistPred := .any .nil
end DistPred

def DistPredList.ofList : List DistPred → DistPredList
  | [] => .nil | p :: ps => .cons p (DistPredList.ofList ps)

/-! ## 2. The byte code -/

def encodeInt : Int → List UInt8 | .ofNat n => 0 :: leb128 n | .negSucc n => 1 :: leb128 n

theorem encodeInt_prefix_inj {a b : Int} {r₁ r₂ : List UInt8}
    (h : encodeInt a ++ r₁ = encodeInt b ++ r₂) : a = b ∧ r₁ = r₂ := by
  cases a <;> cases b <;> simp only [encodeInt, List.cons_append] at h <;>
    have hc := List.cons.inj h
  · obtain ⟨hn, hr⟩ := leb128_prefix_inj hc.2; exact ⟨by rw [hn], hr⟩
  · exact absurd hc.1 (by decide)
  · exact absurd hc.1 (by decide)
  · obtain ⟨hn, hr⟩ := leb128_prefix_inj hc.2; exact ⟨by rw [hn], hr⟩

def encodeInts : List Int → List UInt8
  | [] => [0] | x :: xs => 1 :: (encodeInt x ++ encodeInts xs)

theorem encodeInts_prefix_inj : ∀ (a b : List Int) (r₁ r₂ : List UInt8),
    encodeInts a ++ r₁ = encodeInts b ++ r₂ → a = b ∧ r₁ = r₂
  | [], [], _, _, h => by
    simp only [encodeInts, List.cons_append, List.nil_append] at h; exact ⟨rfl, (List.cons.inj h).2⟩
  | [], _ :: _, _, _, h => by
    simp only [encodeInts, List.cons_append, List.nil_append] at h; exact absurd (List.cons.inj h).1 (by decide)
  | _ :: _, [], _, _, h => by
    simp only [encodeInts, List.cons_append, List.nil_append] at h; exact absurd (List.cons.inj h).1 (by decide)
  | x :: xs, y :: ys, r₁, r₂, h => by
    simp only [encodeInts, List.cons_append, List.append_assoc] at h
    obtain ⟨hxy, hrest⟩ := encodeInt_prefix_inj (List.cons.inj h).2
    obtain ⟨hl, hr⟩ := encodeInts_prefix_inj xs ys r₁ r₂ hrest
    exact ⟨by rw [hxy, hl], hr⟩

def SlotTest.encode : SlotTest → List UInt8
  | .eq v => 0 :: encodeInt v | .le v => 1 :: encodeInt v | .memberOf set => 2 :: encodeInts set
  | .writeOnce => [3] | .monotone => [4] | .hashEq d => 5 :: encodeListField d.data.toList

theorem SlotTest.encode_prefix_inj (a b : SlotTest) (r₁ r₂ : List UInt8)
    (h : a.encode ++ r₁ = b.encode ++ r₂) : a = b ∧ r₁ = r₂ := by
  cases a <;> cases b <;>
    simp only [SlotTest.encode, List.cons_append, List.nil_append] at h <;>
    have hc := List.cons.inj h <;>
    first
      | exact absurd hc.1 (by decide)
      | exact ⟨rfl, hc.2⟩
      | (obtain ⟨hv, hr⟩ := encodeInt_prefix_inj hc.2; exact ⟨by rw [hv], hr⟩)
      | (obtain ⟨hv, hr⟩ := encodeInts_prefix_inj _ _ _ _ hc.2; exact ⟨by rw [hv], hr⟩)
      | (obtain ⟨hv, hr⟩ := encodeListField_prefix_inj hc.2; exact ⟨by rw [byteArray_eq_of_toList_eq hv], hr⟩)

mutual
def DistPred.encode : DistPred → List UInt8
  | .atom s t => 0 :: (leb128 s ++ t.encode) | .witnessed vk => 1 :: encodeListField vk.id.data.toList
  | .not p => 2 :: p.encode | .all ps => 3 :: ps.encode | .any ps => 4 :: ps.encode
termination_by structural p => p
def DistPredList.encode : DistPredList → List UInt8
  | .nil => [0] | .cons p ps => 1 :: (p.encode ++ ps.encode)
termination_by structural ps => ps
end

mutual
theorem DistPred.encode_prefix_inj : ∀ (a b : DistPred) (r₁ r₂ : List UInt8),
    a.encode ++ r₁ = b.encode ++ r₂ → a = b ∧ r₁ = r₂
  | .atom s t, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hs, hrest⟩ := leb128_prefix_inj hc.2
        obtain ⟨ht, hr⟩ := SlotTest.encode_prefix_inj _ _ _ _ hrest; exact ⟨by rw [hs, ht], hr⟩)
  | .witnessed vk, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hv, hr⟩ := encodeListField_prefix_inj hc.2
        obtain ⟨i⟩ := vk; rename_i vk'; obtain ⟨j⟩ := vk'
        exact ⟨by rw [byteArray_eq_of_toList_eq (a := i) (b := j) hv], hr⟩)
  | .not p, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hp, hr⟩ := DistPred.encode_prefix_inj p _ r₁ r₂ hc.2; exact ⟨by rw [hp], hr⟩)
  | .all ps, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hp, hr⟩ := DistPredList.encode_prefix_inj ps _ r₁ r₂ hc.2; exact ⟨by rw [hp], hr⟩)
  | .any ps, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first | exact absurd hc.1 (by decide) | (
        obtain ⟨hp, hr⟩ := DistPredList.encode_prefix_inj ps _ r₁ r₂ hc.2; exact ⟨by rw [hp], hr⟩)
theorem DistPredList.encode_prefix_inj : ∀ (a b : DistPredList) (r₁ r₂ : List UInt8),
    a.encode ++ r₁ = b.encode ++ r₂ → a = b ∧ r₁ = r₂
  | .nil, b, r₁, r₂, h => by
    cases b <;> simp only [DistPredList.encode, List.cons_append, List.nil_append] at h <;>
      have hc := List.cons.inj h
    · exact ⟨rfl, hc.2⟩
    · exact absurd hc.1 (by decide)
  | .cons p ps, b, r₁, r₂, h => by
    cases b <;>
      simp only [DistPredList.encode, List.cons_append, List.nil_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h
    · exact absurd hc.1 (by decide)
    · obtain ⟨hp, hrest⟩ := DistPred.encode_prefix_inj p _ _ _ hc.2
      obtain ⟨hps, hr⟩ := DistPredList.encode_prefix_inj ps _ r₁ r₂ hrest
      exact ⟨by rw [hp, hps], hr⟩
end

/-- **The syntax has a faithful byte code.** Two predicates with one code are one predicate. -/
theorem DistPred.encode_injective {a b : DistPred} (h : a.encode = b.encode) : a = b :=
  (DistPred.encode_prefix_inj a b [] [] (by rw [List.append_nil, List.append_nil, h])).1

/-- Customization string of the predicate digest. -/
def predCustomization : List UInt8 := "OBEND.POLIS.DISTPRED/v1".toUTF8.data.toList

/-- The content address of a predicate. -/
def DistPred.digest (p : DistPred) : ByteArray := cshake32ByteArray predCustomization p.encode

/-- Equal content addresses name equal predicates, or the two codes collide. -/
theorem DistPred.digest_binds {a b : DistPred} (h : a.digest = b.digest) :
    a = b ∨ CollisionAmong (cshake256Bytes predCustomization)
      (fun x => x = a.encode ∨ x = b.encode) := by
  rcases cshake32_binds predCustomization h with hp | hc
  · exact .inl (DistPred.encode_injective hp)
  · exact .inr hc

/-! ## 3. Why the syntax may not hold closures -/

theorem pigeonhole : ∀ (n : Nat) (f : Nat → Nat), (∀ i, i ≤ n → f i < n) →
    ∃ i j, i < j ∧ j ≤ n ∧ f i = f j
  | 0, f, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | n + 1, f, h =>
    if hex : ∃ i, i ≤ n ∧ f i = f (n + 1) then by
      obtain ⟨i, hi, he⟩ := hex
      exact ⟨i, n + 1, by omega, Nat.le_refl _, he⟩
    else by
      have hne : ∀ i, i ≤ n → f i ≠ f (n + 1) := fun i hi he => hex ⟨i, hi, he⟩
      have hg : ∀ i, i ≤ n → (if f i < f (n + 1) then f i else f i - 1) < n := by
        intro i hi
        have h1 := h i (by omega); have h2 := h (n + 1) (Nat.le_refl _); have h3 := hne i hi
        split <;> omega
      obtain ⟨i, j, hij, hj, he⟩ :=
        pigeonhole n (fun i => if f i < f (n + 1) then f i else f i - 1) hg
      refine ⟨i, j, hij, by omega, ?_⟩
      have hi3 := hne i (by omega); have hj3 := hne j hj
      have he' : (if f i < f (n + 1) then f i else f i - 1) =
          (if f j < f (n + 1) then f j else f j - 1) := he
      split at he' <;> split at he' <;> omega

theorem opaque_closure_collapses_finite_encoding {State : Type} (n : Nat)
    (family : Nat → State → Bool)
    (hfamily : ∀ i j, i < j → j ≤ n → ∃ s, family i s ≠ family j s)
    (encode : (State → Bool) → Fin n) :
    ∃ f g : State → Bool, (∃ s, f s ≠ g s) ∧ encode f = encode g := by
  obtain ⟨i, j, hij, hj, he⟩ :=
    pigeonhole n (fun i => (encode (family i)).val) (fun i _ => (encode (family i)).isLt)
  exact ⟨family i, family j, hfamily i j hij hj, Fin.ext he⟩

theorem guard_closure_collapses_finite_encoding (n : Nat) (encode : (Step → Bool) → Fin n) :
    ∃ f g : Step → Bool, (∃ σ, f σ ≠ g σ) ∧ encode f = encode g := by
  refine opaque_closure_collapses_finite_encoding n
    (fun i σ => decide ((σ 0).new = some (Int.ofNat i))) ?_ encode
  intro i j hij _
  exact ⟨fun _ => ⟨none, some (Int.ofNat i)⟩, by simp; omega⟩

theorem opaque_closure_escapes_descriptor_table {Code : Type} (decode : Code → Code → Bool) :
    ∃ f : Code → Bool, ∀ c, ∃ s, decode c s ≠ f s :=
  ⟨fun s => !decode s s, fun c => ⟨c, by
    show decode c c ≠ !decode c c; generalize decode c c = b; cases b <;> decide⟩⟩

/-! ## 4. Evaluation -/

def slotCustomization : List UInt8 := "OBEND.POLIS.DISTPRED.SLOT/v1".toUTF8.data.toList
def slotDigest (value : Int) : ByteArray := cshake32ByteArray slotCustomization (encodeInt value)

theorem slotDigest_binds {a b : Int} (h : slotDigest a = slotDigest b) :
    a = b ∨ CollisionAmong (cshake256Bytes slotCustomization)
      (fun x => x = encodeInt a ∨ x = encodeInt b) := by
  rcases cshake32_binds slotCustomization h with hp | hc
  · exact .inl (encodeInt_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hp])).1
  · exact .inr hc

def SlotTest.holds : SlotTest → SlotStep → Bool
  | .eq v, st => decide (st.new = some v)
  | .le v, st => match st.new with | some x => decide (x ≤ v) | none => false
  | .memberOf set, st => match st.new with | some x => set.contains x | none => false
  | .writeOnce, st =>
    match st.old with | none => true | some o => decide (o = 0) || decide (st.new = some o)
  | .monotone, st => match st.old, st.new with | some o, some n => decide (o ≤ n) | _, _ => false
  | .hashEq d, st => match st.new with | some x => decide (slotDigest x = d) | none => false

abbrev Oracle := VkId → KleenePred3
def noOracle : Oracle := fun _ => .unbound3
def dischargeOracle (ds : List VkId) : Oracle := fun vk => if vk ∈ ds then .true3 else .unbound3
def ofBool : Bool → KleenePred3 | true => .true3 | false => .false3
def combine3 : Bool → KleenePred3 → KleenePred3 → KleenePred3
  | true, x, y => x.and3 y | false, x, y => x.or3 y

mutual
def DistPred.evalWith (o : Oracle) (σ : Step) : DistPred → KleenePred3
  | .atom s t => ofBool (t.holds (σ s))
  | .witnessed vk => o vk
  | .not p => (p.evalWith o σ).not3
  | .all ps => ps.evalList o σ true
  | .any ps => ps.evalList o σ false
termination_by structural p => p
def DistPredList.evalList (o : Oracle) (σ : Step) (conj : Bool) : DistPredList → KleenePred3
  | .nil => ofBool conj
  | .cons p ps => combine3 conj (p.evalWith o σ) (ps.evalList o σ conj)
termination_by structural ps => ps
end

def evalFirstParty (σ : Step) (p : DistPred) : KleenePred3 := p.evalWith noOracle σ
def admits (o : Oracle) (σ : Step) (p : DistPred) : Bool := (p.evalWith o σ).accepts

theorem accepts_iff_true3 (x : KleenePred3) : x.accepts = true ↔ x = .true3 := by
  cases x <;> simp [KleenePred3.accepts]
theorem admits_iff (o : Oracle) (σ : Step) (p : DistPred) :
    admits o σ p = true ↔ p.evalWith o σ = .true3 := accepts_iff_true3 _
theorem admits_tt (o : Oracle) (σ : Step) : admits o σ .tt = true := by rfl
theorem combine3_true (x y : KleenePred3) : combine3 true x y = x.and3 y := by rfl
theorem combine3_refines (conj : Bool) {p p' q q' : KleenePred3} (hp : KleenePred3.Refines p p')
    (hq : KleenePred3.Refines q q') :
    KleenePred3.Refines (combine3 conj p q) (combine3 conj p' q') := by
  cases conj
  · exact KleenePred3.or3_refines hp hq
  · exact KleenePred3.and3_refines hp hq
theorem combine3_unit (conj : Bool) (x : KleenePred3) : combine3 conj (ofBool conj) x = x := by
  cases conj <;> cases x <;> rfl
theorem combine3_zero_left (conj : Bool) (x : KleenePred3) :
    combine3 conj (ofBool (!conj)) x = ofBool (!conj) := by cases conj <;> cases x <;> rfl
theorem combine3_zero_right (conj : Bool) (x : KleenePred3) :
    combine3 conj x (ofBool (!conj)) = ofBool (!conj) := by cases conj <;> cases x <;> rfl
theorem combine3_ofBool (conj a b : Bool) :
    combine3 conj (ofBool a) (ofBool b) = ofBool (if conj then a && b else a || b) := by
  cases conj <;> cases a <;> cases b <;> rfl

mutual
theorem DistPred.evalWith_refines {o o' : Oracle}
    (h : ∀ vk, KleenePred3.Refines (o vk) (o' vk)) (σ : Step) :
    ∀ p : DistPred, KleenePred3.Refines (p.evalWith o σ) (p.evalWith o' σ)
  | .atom _ _ => by simp only [DistPred.evalWith]; exact .inr rfl
  | .witnessed vk => by simp only [DistPred.evalWith]; exact h vk
  | .not p => by simp only [DistPred.evalWith]; exact KleenePred3.not3_refines (DistPred.evalWith_refines h σ p)
  | .all ps => by simp only [DistPred.evalWith]; exact DistPredList.evalList_refines h σ true ps
  | .any ps => by simp only [DistPred.evalWith]; exact DistPredList.evalList_refines h σ false ps
theorem DistPredList.evalList_refines {o o' : Oracle}
    (h : ∀ vk, KleenePred3.Refines (o vk) (o' vk)) (σ : Step) (conj : Bool) :
    ∀ ps : DistPredList, KleenePred3.Refines (ps.evalList o σ conj) (ps.evalList o' σ conj)
  | .nil => by simp only [DistPredList.evalList]; exact .inr rfl
  | .cons p ps => by
    simp only [DistPredList.evalList]
    exact combine3_refines conj (DistPred.evalWith_refines h σ p)
      (DistPredList.evalList_refines h σ conj ps)
end

theorem evalFirstParty_sound_for_evalWith (o : Oracle) (σ : Step) (p : DistPred)
    (h : evalFirstParty σ p ≠ .unbound3) : p.evalWith o σ = evalFirstParty σ p := by
  rcases DistPred.evalWith_refines (o := noOracle) (o' := o) (fun _ => .inl rfl) σ p with hu | he
  · exact absurd hu h
  · exact he.symm

theorem negated_witnessed_refused_firstParty (σ : Step) (vk : VkId) :
    (evalFirstParty σ (.not (.witnessed vk))).accepts = false ∧
      (evalFirstParty σ (.witnessed vk)).accepts = false := by
  simp [evalFirstParty, DistPred.evalWith, noOracle, KleenePred3.not3, KleenePred3.accepts]

theorem negated_witnessed_refused_under_discharges (ds : List VkId) (σ : Step) (vk : VkId) :
    admits (dischargeOracle ds) σ (.not (.witnessed vk)) = false := by
  simp only [admits, DistPred.evalWith, dischargeOracle]; split <;> rfl

theorem discharge_monotone {ds ds' : List VkId} (hsub : ∀ vk, vk ∈ ds → vk ∈ ds') (σ : Step)
    (p : DistPred) (h : admits (dischargeOracle ds) σ p = true) :
    admits (dischargeOracle ds') σ p = true := by
  have hr : ∀ vk, KleenePred3.Refines (dischargeOracle ds vk) (dischargeOracle ds' vk) := by
    intro vk; by_cases hm : vk ∈ ds
    · exact .inr (by simp [dischargeOracle, hm, hsub vk hm])
    · exact .inl (by simp [dischargeOracle, hm])
  have ht := (accepts_iff_true3 _).1 h
  rcases DistPred.evalWith_refines hr σ p with hu | he
  · rw [ht] at hu; cases hu
  · exact (accepts_iff_true3 _).2 (he ▸ ht)

mutual
def DistPred.witnessedFree : DistPred → Bool
  | .atom _ _ => true | .witnessed _ => false | .not p => p.witnessedFree
  | .all ps => ps.witnessedFree | .any ps => ps.witnessedFree
termination_by structural p => p
def DistPredList.witnessedFree : DistPredList → Bool
  | .nil => true | .cons p ps => p.witnessedFree && ps.witnessedFree
termination_by structural ps => ps
end

mutual
theorem DistPred.evalWith_of_witnessedFree (σ : Step) :
    ∀ p : DistPred, p.witnessedFree = true → ∃ b : Bool, ∀ o : Oracle, p.evalWith o σ = ofBool b
  | .atom s t, _ => ⟨t.holds (σ s), fun _ => by simp only [DistPred.evalWith]⟩
  | .witnessed _, h => by simp [DistPred.witnessedFree] at h
  | .not p, h => by
    obtain ⟨b, hb⟩ := DistPred.evalWith_of_witnessedFree σ p (by simpa only [DistPred.witnessedFree] using h)
    exact ⟨!b, fun o => by simp only [DistPred.evalWith, hb o]; cases b <;> rfl⟩
  | .all ps, h => by
    obtain ⟨b, hb⟩ := DistPredList.evalList_of_witnessedFree σ true ps (by simpa only [DistPred.witnessedFree] using h)
    exact ⟨b, fun o => by simp only [DistPred.evalWith, hb o]⟩
  | .any ps, h => by
    obtain ⟨b, hb⟩ := DistPredList.evalList_of_witnessedFree σ false ps (by simpa only [DistPred.witnessedFree] using h)
    exact ⟨b, fun o => by simp only [DistPred.evalWith, hb o]⟩
theorem DistPredList.evalList_of_witnessedFree (σ : Step) (conj : Bool) :
    ∀ ps : DistPredList, ps.witnessedFree = true →
      ∃ b : Bool, ∀ o : Oracle, ps.evalList o σ conj = ofBool b
  | .nil, _ => ⟨conj, fun _ => by simp only [DistPredList.evalList]⟩
  | .cons p ps, h => by
    simp only [DistPredList.witnessedFree, Bool.and_eq_true] at h
    obtain ⟨b₁, h₁⟩ := DistPred.evalWith_of_witnessedFree σ p h.1
    obtain ⟨b₂, h₂⟩ := DistPredList.evalList_of_witnessedFree σ conj ps h.2
    exact ⟨if conj then b₁ && b₂ else b₁ || b₂, fun o => by
      simp only [DistPredList.evalList, h₁ o, h₂ o, combine3_ofBool]⟩
end

theorem evalFirstParty_decides_witnessedFree (o : Oracle) (σ : Step) (p : DistPred)
    (h : p.witnessedFree = true) :
    evalFirstParty σ p ≠ .unbound3 ∧ p.evalWith o σ = evalFirstParty σ p := by
  obtain ⟨b, hb⟩ := DistPred.evalWith_of_witnessedFree σ p h
  exact ⟨by rw [evalFirstParty, hb noOracle]; cases b <;> simp [ofBool],
    by rw [evalFirstParty, hb o, hb noOracle]⟩

/-! ## 5. Residuals: what one vat computes and what it hands on -/

abbrev View := SlotId → Option SlotStep
def Agrees (v : View) (σ : Step) : Prop := ∀ s st, v s = some st → σ s = st
def overlay (v : View) (rest : Step) : Step := fun s => (v s).getD (rest s)
theorem agrees_overlay (v : View) (rest : Step) : Agrees v (overlay v rest) := by
  intro s st h; simp [overlay, h]

def constP : Bool → DistPred | true => .all .nil | false => .any .nil
def listP : Bool → DistPredList → DistPred | true, ps => .all ps | false, ps => .any ps
def DistPred.constOf : DistPred → Option Bool
  | .all .nil => some true | .any .nil => some false | _ => none

theorem constOf_eq_some {p : DistPred} {b : Bool} (h : p.constOf = some b) : p = constP b := by
  unfold DistPred.constOf at h; split at h <;> cases h <;> rfl
theorem evalWith_constP (o : Oracle) (σ : Step) (b : Bool) :
    (constP b).evalWith o σ = ofBool b := by cases b <;> rfl
theorem evalWith_listP (o : Oracle) (σ : Step) (conj : Bool) (ps : DistPredList) :
    (listP conj ps).evalWith o σ = ps.evalList o σ conj := by
  cases conj <;> simp only [listP, DistPred.evalWith]

def pevalAtom (v : View) (s : SlotId) (t : SlotTest) : DistPred :=
  match v s with | some st => constP (t.holds st) | none => .atom s t
def notR (p : DistPred) : DistPred :=
  match p.constOf with | some b => constP (!b) | none => .not p
def DistPredList.hasConst (b : Bool) : DistPredList → Bool
  | .nil => false | .cons p ps => p.constOf == some b || ps.hasConst b
def DistPredList.dropConst (b : Bool) : DistPredList → DistPredList
  | .nil => .nil
  | .cons p ps => if p.constOf = some b then ps.dropConst b else .cons p (ps.dropConst b)
def foldR (conj : Bool) (ps : DistPredList) : DistPred :=
  if ps.hasConst (!conj) then constP (!conj) else listP conj (ps.dropConst conj)

mutual
def DistPred.pevalVat (v : View) : DistPred → DistPred
  | .atom s t => pevalAtom v s t | .witnessed vk => .witnessed vk
  | .not p => notR (p.pevalVat v) | .all ps => foldR true (ps.pevalVat v)
  | .any ps => foldR false (ps.pevalVat v)
termination_by structural p => p
def DistPredList.pevalVat (v : View) : DistPredList → DistPredList
  | .nil => .nil | .cons p ps => .cons (p.pevalVat v) (ps.pevalVat v)
termination_by structural ps => ps
end

mutual
def DistPred.mentions (s : SlotId) : DistPred → Bool
  | .atom s' _ => s' == s | .witnessed _ => false | .not p => p.mentions s
  | .all ps => ps.mentions s | .any ps => ps.mentions s
termination_by structural p => p
def DistPredList.mentions (s : SlotId) : DistPredList → Bool
  | .nil => false | .cons p ps => p.mentions s || ps.mentions s
termination_by structural ps => ps
end

theorem evalWith_notR (o : Oracle) (σ : Step) (p : DistPred) :
    (notR p).evalWith o σ = (p.evalWith o σ).not3 := by
  unfold notR; split
  · rename_i b hb; rw [constOf_eq_some hb, evalWith_constP, evalWith_constP]; cases b <;> rfl
  · simp only [DistPred.evalWith]

theorem DistPredList.evalList_dropConst (o : Oracle) (σ : Step) (conj : Bool) :
    ∀ ps : DistPredList, (ps.dropConst conj).evalList o σ conj = ps.evalList o σ conj
  | .nil => by rfl
  | .cons p ps => by
    simp only [DistPredList.dropConst]; split
    · rename_i hc
      simp only [DistPredList.evalList, DistPredList.evalList_dropConst o σ conj ps,
        constOf_eq_some hc, evalWith_constP, combine3_unit]
    · simp only [DistPredList.evalList, DistPredList.evalList_dropConst o σ conj ps]

theorem DistPredList.evalList_hasConst (o : Oracle) (σ : Step) (conj : Bool) :
    ∀ ps : DistPredList, ps.hasConst (!conj) = true → ps.evalList o σ conj = ofBool (!conj)
  | .nil, h => by simp [DistPredList.hasConst] at h
  | .cons p ps, h => by
    simp only [DistPredList.hasConst, Bool.or_eq_true, beq_iff_eq] at h
    simp only [DistPredList.evalList]
    rcases h with h | h
    · rw [constOf_eq_some h, evalWith_constP, combine3_zero_left]
    · rw [DistPredList.evalList_hasConst o σ conj ps h, combine3_zero_right]

theorem evalWith_foldR (o : Oracle) (σ : Step) (conj : Bool) (ps : DistPredList) :
    (foldR conj ps).evalWith o σ = ps.evalList o σ conj := by
  unfold foldR; split
  · rename_i h; rw [DistPredList.evalList_hasConst o σ conj ps h, evalWith_constP]
  · rw [evalWith_listP, DistPredList.evalList_dropConst]

theorem evalWith_pevalAtom {v : View} {σ : Step} (hv : Agrees v σ) (o : Oracle) (s : SlotId)
    (t : SlotTest) : (pevalAtom v s t).evalWith o σ = ofBool (t.holds (σ s)) := by
  unfold pevalAtom; split
  · rename_i st h; rw [evalWith_constP, hv s st h]
  · simp only [DistPred.evalWith]

mutual
theorem DistPred.evalWith_pevalVat {v : View} {σ : Step} (hv : Agrees v σ) (o : Oracle) :
    ∀ p : DistPred, (p.pevalVat v).evalWith o σ = p.evalWith o σ
  | .atom s t => by simp only [DistPred.pevalVat, evalWith_pevalAtom hv, DistPred.evalWith]
  | .witnessed _ => by simp only [DistPred.pevalVat]
  | .not p => by simp only [DistPred.pevalVat, evalWith_notR, DistPred.evalWith, DistPred.evalWith_pevalVat hv o p]
  | .all ps => by simp only [DistPred.pevalVat, evalWith_foldR, DistPred.evalWith, DistPredList.evalList_pevalVat hv o true ps]
  | .any ps => by simp only [DistPred.pevalVat, evalWith_foldR, DistPred.evalWith, DistPredList.evalList_pevalVat hv o false ps]
theorem DistPredList.evalList_pevalVat {v : View} {σ : Step} (hv : Agrees v σ) (o : Oracle)
    (conj : Bool) : ∀ ps : DistPredList, (ps.pevalVat v).evalList o σ conj = ps.evalList o σ conj
  | .nil => by simp only [DistPredList.pevalVat]
  | .cons p ps => by
    simp only [DistPredList.pevalVat, DistPredList.evalList, DistPred.evalWith_pevalVat hv o p,
      DistPredList.evalList_pevalVat hv o conj ps]
end

theorem mentions_constP (s : SlotId) (b : Bool) : (constP b).mentions s = false := by cases b <;> rfl
theorem mentions_pevalAtom {v : View} {s : SlotId} (hs : (v s).isSome = true) (s' : SlotId)
    (t : SlotTest) : (pevalAtom v s' t).mentions s = false := by
  unfold pevalAtom; split
  · exact mentions_constP s _
  · rename_i h; simp only [DistPred.mentions, beq_eq_false_iff_ne, ne_eq]
    intro he; subst he; simp [h] at hs

theorem mentions_notR (s : SlotId) (p : DistPred) (h : p.mentions s = false) :
    (notR p).mentions s = false := by
  unfold notR; split
  · exact mentions_constP s _
  · simpa only [DistPred.mentions] using h

theorem DistPredList.mentions_dropConst (s : SlotId) (b : Bool) :
    ∀ ps : DistPredList, ps.mentions s = false → (ps.dropConst b).mentions s = false
  | .nil, _ => by rfl
  | .cons p ps, h => by
    simp only [DistPredList.mentions, Bool.or_eq_false_iff] at h
    simp only [DistPredList.dropConst]; split
    · exact DistPredList.mentions_dropConst s b ps h.2
    · simp only [DistPredList.mentions, h.1, DistPredList.mentions_dropConst s b ps h.2, Bool.or_self]

theorem mentions_foldR (s : SlotId) (conj : Bool) (ps : DistPredList)
    (h : ps.mentions s = false) : (foldR conj ps).mentions s = false := by
  unfold foldR; split
  · exact mentions_constP s _
  · cases conj <;> simpa only [listP, DistPred.mentions] using DistPredList.mentions_dropConst s _ ps h

mutual
theorem DistPred.pevalVat_hides_known_slots {v : View} {s : SlotId} (hs : (v s).isSome = true) :
    ∀ p : DistPred, (p.pevalVat v).mentions s = false
  | .atom s' t => by simp only [DistPred.pevalVat]; exact mentions_pevalAtom hs s' t
  | .witnessed _ => by simp only [DistPred.pevalVat, DistPred.mentions]
  | .not p => by simp only [DistPred.pevalVat]; exact mentions_notR s _ (DistPred.pevalVat_hides_known_slots hs p)
  | .all ps => by simp only [DistPred.pevalVat]; exact mentions_foldR s true _ (DistPredList.pevalVat_hides_known_slots hs ps)
  | .any ps => by simp only [DistPred.pevalVat]; exact mentions_foldR s false _ (DistPredList.pevalVat_hides_known_slots hs ps)
theorem DistPredList.pevalVat_hides_known_slots {v : View} {s : SlotId}
    (hs : (v s).isSome = true) :
    ∀ ps : DistPredList, (ps.pevalVat v).mentions s = false
  | .nil => by simp only [DistPredList.pevalVat, DistPredList.mentions]
  | .cons p ps => by
    simp only [DistPredList.pevalVat, DistPredList.mentions,
      DistPred.pevalVat_hides_known_slots hs p, DistPredList.pevalVat_hides_known_slots hs ps, Bool.or_self]
end

mutual
theorem DistPred.evalWith_congr (o : Oracle) {σ σ' : Step} :
    ∀ p : DistPred, (∀ s, p.mentions s = true → σ s = σ' s) → p.evalWith o σ = p.evalWith o σ'
  | .atom s t, h => by simp only [DistPred.evalWith, h s (by simp [DistPred.mentions])]
  | .witnessed _, _ => by simp only [DistPred.evalWith]
  | .not p, h => by
    simp only [DistPred.evalWith, DistPred.evalWith_congr o p (fun s hs => h s (by simpa only [DistPred.mentions] using hs))]
  | .all ps, h => by
    simp only [DistPred.evalWith, DistPredList.evalList_congr o true ps (fun s hs => h s (by simpa only [DistPred.mentions] using hs))]
  | .any ps, h => by
    simp only [DistPred.evalWith, DistPredList.evalList_congr o false ps (fun s hs => h s (by simpa only [DistPred.mentions] using hs))]
theorem DistPredList.evalList_congr (o : Oracle) {σ σ' : Step} (conj : Bool) :
    ∀ ps : DistPredList, (∀ s, ps.mentions s = true → σ s = σ' s) →
      ps.evalList o σ conj = ps.evalList o σ' conj
  | .nil, _ => by simp only [DistPredList.evalList]
  | .cons p ps, h => by
    simp only [DistPredList.evalList,
      DistPred.evalWith_congr o p (fun s hs => h s (by simp [DistPredList.mentions, hs])),
      DistPredList.evalList_congr o conj ps (fun s hs => h s (by simp [DistPredList.mentions, hs]))]
end

theorem eval_subst_eq_eval_pevalVat (o : Oracle) (v : View) (rest : Step) (p : DistPred) :
    p.evalWith o (overlay v rest) = (p.pevalVat v).evalWith o rest := by
  rw [← DistPred.evalWith_pevalVat (agrees_overlay v rest) o p]
  apply DistPred.evalWith_congr
  intro s hs
  cases hv : v s with
  | none => simp [overlay, hv]
  | some st => rw [DistPred.pevalVat_hides_known_slots (by simp [hv]) p] at hs; cases hs

/-! ## 6. Additively homomorphic ring tags and cSHAKE256-bound openings -/

/-- Two generators of `ℤ/2²⁵⁶`, with `g` a unit (`gInv * g = 1`). -/
structure CommitKey where
  g : BitVec 256
  h : BitVec 256
  gInv : BitVec 256
  unit : gInv * g = 1#256

/-- A `CommitKey` where the blinding generator `h` is also an odd unit (`hInv * h = 1`),
giving a 1-to-1 hiding pad bijection for every value `v`. -/
structure HidingCommitKey extends CommitKey where
  hInv : BitVec 256
  hUnit : hInv * h = 1#256

def commitVal (key : CommitKey) (value blind : BitVec 256) : BitVec 256 :=
  key.g * value + key.h * blind

structure Opening where
  value : BitVec 256
  blind : BitVec 256
  deriving DecidableEq

def Opening.commit (key : CommitKey) (o : Opening) : BitVec 256 := commitVal key o.value o.blind

def bvSum : List (BitVec 256) → BitVec 256
  | [] => 0#256
  | x :: xs => x + bvSum xs

def natSum : List (BitVec 256) → Nat
  | [] => 0
  | x :: xs => x.toNat + natSum xs

def valueSum (os : List Opening) : BitVec 256 := bvSum (os.map (·.value))
def blindSum (os : List Opening) : BitVec 256 := bvSum (os.map (·.blind))

theorem commitVal_add (key : CommitKey) (v₁ b₁ v₂ b₂ : BitVec 256) :
    commitVal key (v₁ + v₂) (b₁ + b₂) = commitVal key v₁ b₁ + commitVal key v₂ b₂ := by
  simp only [commitVal, BitVec.mul_add]
  ac_rfl

theorem commitSum_collapse (key : CommitKey) (os : List Opening) :
    bvSum (os.map (Opening.commit key)) = commitVal key (valueSum os) (blindSum os) := by
  induction os with
  | nil => simp [bvSum, commitVal, valueSum, blindSum]
  | cons o os ih =>
    simp only [valueSum, blindSum] at ih
    simp only [List.map_cons, bvSum, ih, Opening.commit, commitVal_add, valueSum, blindSum]

theorem commitVal_value_inj (key : CommitKey) {a a' b : BitVec 256}
    (h : commitVal key a b = commitVal key a' b) : a = a' := by
  have h1 : key.g * a = key.g * a' := by
    have h0 := congrArg (· - key.h * b) h
    simpa only [commitVal, BitVec.add_sub_cancel] using h0
  have h2 := congrArg (key.gInv * ·) h1
  simpa only [← BitVec.mul_assoc, key.unit, BitVec.one_mul] using h2

private theorem bv256_sub_add_cancel (x y : BitVec 256) : x - y + y = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- Unique blinding pad `b` mapping candidate value `v` to target ring tag `c`. -/
def HidingCommitKey.blindFor (key : HidingCommitKey) (c v : BitVec 256) : BitVec 256 :=
  key.hInv * (c - key.g * v)

/-- **Uniform Hiding Pad Bijection**: when `h` is a unit mod `2²⁵⁶`, for every ring tag `c` and
every candidate value `v` there is a unique blinding `b = key.blindFor c v` with `commitVal = c`.
Hence `commitVal` alone is information-theoretically hiding under uniform `b`, and therefore CANNOT
bind `(v, b)` on its own — binding comes from `Opening.bind` (`cSHAKE256`). -/
theorem commitVal_hiding_bijection (key : HidingCommitKey) (c v b : BitVec 256) :
    commitVal key.toCommitKey v b = c ↔ b = key.blindFor c v := by
  constructor
  · intro hc
    have h1 : key.h * b = c - key.g * v := by
      rw [← hc, commitVal, BitVec.add_comm, BitVec.add_sub_cancel]
    have h2 := congrArg (key.hInv * ·) h1
    simpa only [HidingCommitKey.blindFor, ← BitVec.mul_assoc, key.hUnit, BitVec.one_mul] using h2
  · intro hb
    subst hb
    have hmul : key.h * (key.hInv * (c - key.g * v)) = c - key.g * v := by
      calc key.h * (key.hInv * (c - key.g * v))
        _ = (key.hInv * key.h) * (c - key.g * v) := by ac_rfl
        _ = 1#256 * (c - key.g * v) := by rw [key.hUnit]
        _ = c - key.g * v := BitVec.one_mul _
    calc commitVal key.toCommitKey v (key.blindFor c v)
      _ = key.g * v + key.h * (key.hInv * (c - key.g * v)) := rfl
      _ = (c - key.g * v) + key.g * v := by rw [hmul, BitVec.add_comm]
      _ = c := bv256_sub_add_cancel c (key.g * v)

def homCheck (ins outs : List (BitVec 256)) : Bool := decide (bvSum ins = bvSum outs)

theorem homCheck_iff (ins outs : List (BitVec 256)) :
    homCheck ins outs = true ↔ bvSum ins = bvSum outs := by
  simp only [homCheck, decide_eq_true_eq]

theorem private_conservation_checks_homomorphically (key : CommitKey) (ins outs : List Opening) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = true ↔
      commitVal key (valueSum ins) (blindSum ins) = commitVal key (valueSum outs) (blindSum outs) := by
  simp only [homCheck, decide_eq_true_eq, commitSum_collapse]

theorem private_conservation_iff_value_sum (key : CommitKey) (ins outs : List Opening)
    (hblind : blindSum ins = blindSum outs) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = true ↔
      valueSum ins = valueSum outs := by
  rw [private_conservation_checks_homomorphically]
  constructor
  · intro h; rw [hblind] at h; exact commitVal_value_inj key h
  · intro h; rw [h, hblind]

theorem bvSum_toNat : ∀ xs : List (BitVec 256), (bvSum xs).toNat = natSum xs % 2 ^ 256
  | [] => by simp [bvSum, natSum]
  | x :: xs => by simp only [bvSum, natSum, BitVec.toNat_add, bvSum_toNat xs, Nat.add_mod_mod]

theorem natSum_le_of_bits (bits : Nat) : ∀ xs : List (BitVec 256),
    (∀ x, x ∈ xs → x.toNat < 2 ^ bits) → natSum xs ≤ xs.length * 2 ^ bits
  | [], _ => by simp [natSum]
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := natSum_le_of_bits bits xs (fun y hy => h y (by simp [hy]))
    simp only [natSum, List.length_cons, Nat.add_one_mul]; omega

theorem private_conservation_nat_sum (key : CommitKey) (ins outs : List Opening)
    (hblind : blindSum ins = blindSum outs)
    (hin : natSum (ins.map (·.value)) < 2 ^ 256) (hout : natSum (outs.map (·.value)) < 2 ^ 256) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = true ↔
      natSum (ins.map (·.value)) = natSum (outs.map (·.value)) := by
  rw [private_conservation_iff_value_sum key ins outs hblind]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [valueSum, bvSum_toNat] at h'
    rwa [Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hout] at h'
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [valueSum, bvSum_toNat, h]

theorem inflation_refused (key : CommitKey) (ins outs : List Opening)
    (hblind : blindSum ins = blindSum outs) (hne : valueSum ins ≠ valueSum outs) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = false := by
  cases hc : homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) with
  | false => rfl
  | true => exact absurd ((private_conservation_iff_value_sum key ins outs hblind).1 hc) hne

def demoKey : CommitKey :=
  ⟨3#256, 5#256, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB#256, by decide⟩

def demoHidingKey : HidingCommitKey :=
  { demoKey with
    hInv := 0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCD#256
    hUnit := by decide }

/-- **Equivocation on Raw `ℤ/2²⁵⁶` Ring Tags**: `3·0 + 5·5 = 25 = 3·5 + 5·2`, so `Opening.commit`
alone is NOT binding without a domain-separated `cSHAKE256` opening commitment (`Opening.bind`). -/
theorem demoKey_equivocates :
    Opening.commit demoKey ⟨0#256, 5#256⟩ = Opening.commit demoKey ⟨5#256, 2#256⟩ := by decide

/-- **Forgery Without Blinding Conservation**: if `blindSum ins = blindSum outs` is NOT verified,
`[⟨0, 0⟩] → [⟨200, -120⟩]` passes `homCheck` with 8-bit values while inflating `0 < 200`! -/
theorem homCheck_accepts_unblinded_forgery :
    let ins : List Opening := [⟨0#256, 0#256⟩]
    let outs : List Opening := [⟨200#256, 0#256 - 120#256⟩]
    homCheck (ins.map (Opening.commit demoKey)) (outs.map (Opening.commit demoKey)) = true ∧
      (∀ op ∈ ins ++ outs, op.value.toNat < 2 ^ 8) ∧
      natSum (ins.map (·.value)) < natSum (outs.map (·.value)) := by decide

/-- Type-valued constructive collision witness over an explicit finite preimage list `msgs`. -/
structure PinnedListCollision (domain : List UInt8) (msgs : List (List UInt8)) where
  msgA : List UInt8
  msgB : List UInt8
  memA : msgA ∈ msgs
  memB : msgB ∈ msgs
  distinct : msgA ≠ msgB
  sameDigest : cshake256Bytes domain msgA = cshake256Bytes domain msgB

def PinnedListCollision.weaken {domain : List UInt8} {m₁ m₂ : List (List UInt8)}
    (hSub : ∀ m ∈ m₁, m ∈ m₂) (w : PinnedListCollision domain m₁) : PinnedListCollision domain m₂ :=
  ⟨w.msgA, w.msgB, hSub _ w.memA, hSub _ w.memB, w.distinct, w.sameDigest⟩

theorem PinnedListCollision.toCollisionAmong {domain : List UInt8} {msgs : List (List UInt8)}
    (w : PinnedListCollision domain msgs) :
    CollisionAmong (cshake256Bytes domain) (fun x => x ∈ msgs) :=
  ⟨w.msgA, w.msgB, w.memA, w.memB, w.distinct, congrArg ofBE w.sameDigest⟩

/-- Constructive `0 Classical` extractor for `cshake32ByteArray`. -/
def cshake32Extract (domain m₁ m₂ : List UInt8)
    (h : cshake32ByteArray domain m₁ = cshake32ByteArray domain m₂) :
    PSum (PLift (m₁ = m₂)) (PinnedListCollision domain [m₁, m₂]) :=
  if hm : m₁ = m₂ then .inl ⟨hm⟩
  else .inr ⟨m₁, m₂, .head _, .tail _ (.head _), hm, by
    have hl := congrArg (fun b : ByteArray => b.data.toList) h
    simpa only [cshake32ByteArray, Native.bytesOfList_toList] using hl⟩

def openingCustomization : List UInt8 := "OBEND.POLIS.OPENING.BIND/v1".toUTF8.data.toList

def Opening.encode (o : Opening) : List UInt8 :=
  encodeFields [be 32 o.value.toNat, be 32 o.blind.toNat]

theorem Opening.encode_injective {a b : Opening} (h : a.encode = b.encode) : a = b := by
  obtain ⟨va, ba⟩ := a; obtain ⟨vb, bb⟩ := b
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hv := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ va.isLt) (h256 ▸ vb.isLt) hf.1)
  have hb := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ ba.isLt) (h256 ▸ bb.isLt) hf.2)
  rw [hv, hb]

/-- Domain-separated 256-bit `cSHAKE256` binding commitment to `(value, blind)`. -/
def Opening.bind (o : Opening) : ByteArray := cshake32ByteArray openingCustomization o.encode

/-- Constructive `0 Classical` binding extractor for `Opening.bind`. -/
def Opening.bindExtract (a b : Opening) (h : a.bind = b.bind) :
    PSum (PLift (a = b)) (PinnedListCollision openingCustomization [a.encode, b.encode]) :=
  match cshake32Extract openingCustomization a.encode b.encode h with
  | .inl hp => .inl ⟨Opening.encode_injective hp.down⟩
  | .inr hc => .inr hc

attribute [local irreducible] Opening.bind Opening.encode openingCustomization

def bindListExtract : ∀ (xs ys : List Opening),
    xs.map Opening.bind = ys.map Opening.bind →
    PSum (PLift (xs = ys))
      (PinnedListCollision openingCustomization (xs.map Opening.encode ++ ys.map Opening.encode))
  | [], [], _ => .inl ⟨rfl⟩
  | [], _ :: _, h => False.elim (by cases h)
  | _ :: _, [], h => False.elim (by cases h)
  | x :: xs, y :: ys, h =>
    have hHead : Opening.bind x = Opening.bind y := by injection h
    have hTail : xs.map Opening.bind = ys.map Opening.bind := by injection h
    match Opening.bindExtract x y hHead with
    | .inr hc =>
      .inr (hc.weaken (fun _ hm => by
        cases hm with
        | head => exact List.mem_append_left _ (.head _)
        | tail _ hm' =>
          cases hm' with
          | head => exact List.mem_append_right _ (.head _)
          | tail _ hm'' => cases hm''))
    | .inl hxy =>
      match bindListExtract xs ys hTail with
      | .inl hrest => .inl ⟨by rw [hxy.down, hrest.down]⟩
      | .inr hc =>
        .inr (hc.weaken (by
          intro m hm
          rcases List.mem_append.1 hm with hL | hR
          · exact List.mem_append_left _ (.tail _ hL)
          · exact List.mem_append_right _ (.tail _ hR)))

/-! ## 7. The graded ladder: bound openings, audited blinding conservation, witnessed ranges -/

structure RangeClaim where
  commitment : BitVec 256
  bits : Nat
  deriving DecidableEq

def RangeClaim.encode (c : RangeClaim) : List UInt8 :=
  encodeFields [be 32 c.commitment.toNat, leb128 c.bits]

theorem RangeClaim.encode_injective {a b : RangeClaim} (h : a.encode = b.encode) : a = b := by
  obtain ⟨ca, na⟩ := a; obtain ⟨cb, nb⟩ := b
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hc := BitVec.eq_of_toNat_eq (be_injective (h256 ▸ ca.isLt) (h256 ▸ cb.isLt) hf.1)
  have hn := (leb128_prefix_inj (n₁ := na) (n₂ := nb) (r₁ := []) (r₂ := []) (by simpa using hf.2)).1
  rw [hc, hn]

def rangeCustomization : List UInt8 := "OBEND.POLIS.RANGE/v1".toUTF8.data.toList
def rangeVk (c : RangeClaim) : VkId := ⟨cshake32ByteArray rangeCustomization c.encode⟩

theorem rangeVk_binds {a b : RangeClaim} (h : rangeVk a = rangeVk b) :
    a = b ∨ CollisionAmong (cshake256Bytes rangeCustomization)
      (fun x => x = a.encode ∨ x = b.encode) := by
  rcases cshake32_binds rangeCustomization (congrArg VkId.id h) with hp | hc
  · exact .inl (RangeClaim.encode_injective hp)
  · exact .inr hc

/-- Full statement of an audited private transfer: binds `key.g`, `key.h`, ring tags,
256-bit `Opening.bind` digests, and bit-width `bits`. -/
structure AuditClaim where
  g : BitVec 256
  h : BitVec 256
  inCommits : List (BitVec 256)
  outCommits : List (BitVec 256)
  inBinds : List ByteArray
  outBinds : List ByteArray
  bits : Nat
  deriving DecidableEq

def encodeBv256List (vs : List (BitVec 256)) : List UInt8 :=
  encodeFields (vs.map fun v => be 32 v.toNat)

private theorem map_be32_injective : ∀ (a b : List (BitVec 256)),
    a.map (fun v => be 32 v.toNat) = b.map (fun v => be 32 v.toNat) → a = b
  | [], [], _ => rfl
  | [], _ :: _, hc => by cases hc
  | _ :: _, [], hc => by cases hc
  | x :: xs', y :: ys', hc => by
    simp only [List.map_cons, List.cons.injEq] at hc
    have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
    rw [BitVec.eq_of_toNat_eq (be_injective (h256 ▸ x.isLt) (h256 ▸ y.isLt) hc.1),
        map_be32_injective xs' ys' hc.2]

theorem encodeBv256List_injective {xs ys : List (BitVec 256)}
    (h : encodeBv256List xs = encodeBv256List ys) : xs = ys :=
  map_be32_injective xs ys (encodeFields_injective _ _ h)

def AuditClaim.encode (c : AuditClaim) : List UInt8 :=
  encodeFields [be 32 c.g.toNat, be 32 c.h.toNat, encodeBv256List c.inCommits,
    encodeBv256List c.outCommits, encodeFields (c.inBinds.map (·.data.toList)),
    encodeFields (c.outBinds.map (·.data.toList)), leb128 c.bits]

theorem AuditClaim.encode_injective {a b : AuditClaim} (h : a.encode = b.encode) : a = b := by
  obtain ⟨ga, ha, ica, oca, iba, oba, ba⟩ := a
  obtain ⟨gb, hb, icb, ocb, ibb, obb, bb⟩ := b
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨hg, hh, hic, hoc, hib, hob, hbits⟩
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  rw [BitVec.eq_of_toNat_eq (be_injective (h256 ▸ ga.isLt) (h256 ▸ gb.isLt) hg),
      BitVec.eq_of_toNat_eq (be_injective (h256 ▸ ha.isLt) (h256 ▸ hb.isLt) hh),
      encodeBv256List_injective hic, encodeBv256List_injective hoc,
      map_toList_injective iba ibb (encodeFields_injective _ _ hib),
      map_toList_injective oba obb (encodeFields_injective _ _ hob),
      (leb128_prefix_inj (n₁ := ba) (n₂ := bb) (r₁ := []) (r₂ := []) (by simpa using hbits)).1]

def auditCustomization : List UInt8 := "OBEND.POLIS.TRANSFER.AUDIT/v1".toUTF8.data.toList

/-- 33-byte tagged `VkId` (`1 :: cshake256Bytes ...`) disjoint by width from 32-byte `rangeVk`. -/
def auditVk (c : AuditClaim) : VkId :=
  ⟨⟨(1 :: cshake256Bytes auditCustomization c.encode).toArray⟩⟩

theorem auditVk_ne_rangeVk (c : AuditClaim) (r : RangeClaim) : auditVk c ≠ rangeVk r := by
  intro hEq
  have hLen := congrArg (fun v : VkId => v.id.data.toList.length) hEq
  simp only [auditVk, rangeVk, cshake32ByteArray, Native.bytesOfList_toList,
    List.length_cons, cshake256Bytes_length] at hLen
  omega

def auditVkExtract (a b : AuditClaim) (h : auditVk a = auditVk b) :
    PSum (PLift (a = b)) (PinnedListCollision auditCustomization [a.encode, b.encode]) :=
  if hm : a.encode = b.encode then .inl ⟨AuditClaim.encode_injective hm⟩
  else .inr ⟨a.encode, b.encode, .head _, .tail _ (.head _), hm, by
    have hl := congrArg (fun v : VkId => v.id.data.toList) h
    simpa only [auditVk, List.cons.injEq, true_and] using hl⟩

def AuditClaim.ofTransfer (key : CommitKey) (ins outs : List Opening) (bits : Nat) : AuditClaim :=
  ⟨key.g, key.h, ins.map (Opening.commit key), outs.map (Opening.commit key),
   ins.map Opening.bind, outs.map Opening.bind, bits⟩

/-- Executable transfer auditor: load-bearingly checks `key`, ring tags, `Opening.bind` digests,
**blinding conservation `blindSum ins = blindSum outs`**, and bit-width `< 2 ^ claim.bits`. -/
def auditTransfer (key : CommitKey) (ins outs : List Opening) (claim : AuditClaim) : Bool :=
  decide (claim.g = key.g) && decide (claim.h = key.h) &&
  decide (claim.inCommits = ins.map (Opening.commit key)) &&
  decide (claim.outCommits = outs.map (Opening.commit key)) &&
  decide (claim.inBinds = ins.map Opening.bind) &&
  decide (claim.outBinds = outs.map Opening.bind) &&
  decide (blindSum ins = blindSum outs) &&
  (ins ++ outs).all (fun op => decide (op.value.toNat < 2 ^ claim.bits))

structure PrivPred where
  ins : List (BitVec 256)
  outs : List (BitVec 256)
  ranges : List RangeClaim
  clear : DistPred

def rangeLeaves : List RangeClaim → DistPredList
  | [] => .nil
  | c :: cs => .cons (.witnessed (rangeVk c)) (rangeLeaves cs)

def PrivPred.guard (p : PrivPred) : DistPred := .all (.cons p.clear (rangeLeaves p.ranges))

def PrivPred.check (o : Oracle) (σ : Step) (p : PrivPred) : Bool :=
  homCheck p.ins p.outs && (p.guard.evalWith o σ).accepts

theorem accepts_evalList_rangeLeaves (o : Oracle) (σ : Step) : ∀ cs : List RangeClaim,
    ((rangeLeaves cs).evalList o σ true).accepts = true ↔ ∀ c, c ∈ cs → o (rangeVk c) = .true3
  | [] => by simp [rangeLeaves, DistPredList.evalList, ofBool, KleenePred3.accepts]
  | c :: cs => by
    simp only [rangeLeaves, DistPredList.evalList, combine3_true, DistPred.evalWith,
      KleenePred3.accepts_and3, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [accepts_evalList_rangeLeaves o σ cs, accepts_iff_true3]

theorem PrivPred.check_iff (o : Oracle) (σ : Step) (p : PrivPred) :
    p.check o σ = true ↔
      bvSum p.ins = bvSum p.outs ∧ (∀ c, c ∈ p.ranges → o (rangeVk c) = .true3) ∧
        (p.clear.evalWith o σ).accepts = true := by
  simp only [PrivPred.check, PrivPred.guard, homCheck, Bool.and_eq_true, decide_eq_true_eq,
    DistPred.evalWith, DistPredList.evalList, combine3_true, KleenePred3.accepts_and3,
    accepts_evalList_rangeLeaves]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩

theorem privPred_ranges_refused_firstParty (σ : Step) (p : PrivPred) (c : RangeClaim)
    (hc : c ∈ p.ranges) : p.check noOracle σ = false := by
  cases h : p.check noOracle σ with
  | false => rfl
  | true =>
    have h3 := ((PrivPred.check_iff noOracle σ p).1 h).2.1 c hc
    simp [noOracle] at h3

def RangeSound (key : CommitKey) (o : Oracle) (os : List Opening) (bits : Nat) : Prop :=
  ∀ op, op ∈ os → o (rangeVk ⟨op.commit key, bits⟩) = .true3 → op.value.toNat < 2 ^ bits

/-- Soundness contract for an auditor oracle backing certified openings `(insCert, outsCert)`. -/
def AuditSound (key : CommitKey) (o : Oracle) (insCert outsCert : List Opening)
    (claimCert : AuditClaim) : Prop :=
  auditTransfer key insCert outsCert claimCert = true ∧
    ∀ c, o (auditVk c) = .true3 → auditVk c = auditVk claimCert

/-- Concrete executable oracle running `auditTransfer` for `auditVk` and `< 2 ^ bits` for `rangeVk`. -/
def auditedOracle (key : CommitKey) (insCert outsCert : List Opening) (bits : Nat) : Oracle :=
  let claimCert := AuditClaim.ofTransfer key insCert outsCert bits
  fun vk =>
    if auditTransfer key insCert outsCert claimCert && decide (vk = auditVk claimCert) then .true3
    else if (insCert ++ outsCert).any (fun op =>
        decide (op.value.toNat < 2 ^ bits) && decide (vk = rangeVk ⟨op.commit key, bits⟩)) then .true3
    else .unbound3

theorem auditedOracle_auditSound (key : CommitKey) (insCert outsCert : List Opening) (bits : Nat)
    (hAud : auditTransfer key insCert outsCert (AuditClaim.ofTransfer key insCert outsCert bits) = true) :
    AuditSound key (auditedOracle key insCert outsCert bits) insCert outsCert
      (AuditClaim.ofTransfer key insCert outsCert bits) := by
  refine ⟨hAud, fun c hc => ?_⟩
  unfold auditedOracle at hc
  split at hc
  · rename_i h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.2
  · split at hc
    · rename_i _ h2
      obtain ⟨op, _, hOp⟩ := List.any_eq_true.1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hOp
      exact False.elim (auditVk_ne_rangeVk c ⟨op.commit key, bits⟩ hOp.2)
    · cases hc

/-- Private transfer predicate: checks homomorphic ring balance, range leaves on every opening,
the audited `auditVk` leaf binding `(ins, outs)` + blinding conservation, and `clear`. -/
def transferPred (key : CommitKey) (ins outs : List Opening) (bits : Nat) (clear : DistPred) :
    PrivPred :=
  ⟨ins.map (Opening.commit key), outs.map (Opening.commit key),
    (ins ++ outs).map (fun op => ⟨op.commit key, bits⟩),
    .all (.cons (.witnessed (auditVk (AuditClaim.ofTransfer key ins outs bits))) (.cons clear .nil))⟩

/-- Constructive `0 Classical` extractor for audited private transfers: either recovers `ins = insCert`,
`outs = outsCert`, verified `blindSum ins = blindSum outs`, exact `Nat` value conservation, and `clear`,
or returns a concrete `PinnedListCollision` on `auditCustomization` or `openingCustomization`. -/
def privPred_conservation_extract (key : CommitKey) (o : Oracle) (σ : Step)
    (ins outs insCert outsCert : List Opening) (claimCert : AuditClaim)
    (bits : Nat) (clear : DistPred)
    (hcheck : (transferPred key ins outs bits clear).check o σ = true)
    (hAudit : AuditSound key o insCert outsCert claimCert)
    (hrange : RangeSound key o (ins ++ outs) bits)
    (hin : ins.length * 2 ^ bits < 2 ^ 256) (hout : outs.length * 2 ^ bits < 2 ^ 256) :
    PSum
      (PLift (ins = insCert ∧ outs = outsCert ∧ blindSum ins = blindSum outs ∧
        natSum (ins.map (·.value)) = natSum (outs.map (·.value)) ∧
        (clear.evalWith o σ).accepts = true))
      (Sum
        (PinnedListCollision auditCustomization
          [(AuditClaim.ofTransfer key ins outs bits).encode, claimCert.encode])
        (PinnedListCollision openingCustomization
          ((ins.map Opening.encode ++ insCert.map Opening.encode) ++
           (outs.map Opening.encode ++ outsCert.map Opening.encode)))) :=
  let claim := AuditClaim.ofTransfer key ins outs bits
  have hChk := (PrivPred.check_iff o σ (transferPred key ins outs bits clear)).1 hcheck
  have hAll : o (auditVk claim) = .true3 ∧ (clear.evalWith o σ).accepts = true := by
    have hClear := hChk.2.2
    simp only [transferPred, DistPred.evalWith, DistPredList.evalList, combine3_true,
      ofBool, KleenePred3.accepts_and3, Bool.and_eq_true, accepts_iff_true3] at hClear
    exact ⟨hClear.1, (accepts_iff_true3 _).2 hClear.2.1⟩
  match auditVkExtract claim claimCert (hAudit.2 claim hAll.1) with
  | .inr hcAud => .inr (.inl hcAud)
  | .inl hClaimEq =>
    have hAudTrue := hAudit.1
    have hInBinds : ins.map Opening.bind = insCert.map Opening.bind := by
      have h1 : claim.inBinds = claimCert.inBinds := congrArg AuditClaim.inBinds hClaimEq.down
      simp only [auditTransfer, Bool.and_eq_true, decide_eq_true_eq] at hAudTrue
      exact h1.trans hAudTrue.1.1.1.2
    have hOutBinds : outs.map Opening.bind = outsCert.map Opening.bind := by
      have h1 : claim.outBinds = claimCert.outBinds := congrArg AuditClaim.outBinds hClaimEq.down
      simp only [auditTransfer, Bool.and_eq_true, decide_eq_true_eq] at hAudTrue
      exact h1.trans hAudTrue.1.1.2
    match bindListExtract ins insCert hInBinds with
    | .inr hcIn =>
      .inr (.inr (hcIn.weaken (fun _ hm => List.mem_append_left _ hm)))
    | .inl hInsEq =>
      match bindListExtract outs outsCert hOutBinds with
      | .inr hcOut =>
        .inr (.inr (hcOut.weaken (fun _ hm => List.mem_append_right _ hm)))
      | .inl hOutsEq =>
        .inl ⟨by
          have hBlindCert : blindSum insCert = blindSum outsCert := by
            simp only [auditTransfer, Bool.and_eq_true, decide_eq_true_eq] at hAudTrue
            exact hAudTrue.1.2
          have hblind : blindSum ins = blindSum outs := by
            rw [hInsEq.down, hOutsEq.down]; exact hBlindCert
          have hbound : ∀ op, op ∈ ins ++ outs → op.value.toNat < 2 ^ bits := fun op hop =>
            hrange op hop (hChk.2.1 ⟨op.commit key, bits⟩ (List.mem_map.2 ⟨op, hop, rfl⟩))
          have hin' : natSum (ins.map (·.value)) < 2 ^ 256 := by
            have := natSum_le_of_bits bits (ins.map (·.value)) (fun x hx => by
              obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hx
              exact hbound op (List.mem_append_left _ hop))
            simp only [List.length_map] at this; omega
          have hout' : natSum (outs.map (·.value)) < 2 ^ 256 := by
            have := natSum_le_of_bits bits (outs.map (·.value)) (fun x hx => by
              obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hx
              exact hbound op (List.mem_append_right _ hop))
            simp only [List.length_map] at this; omega
          have hNat : natSum (ins.map (·.value)) = natSum (outs.map (·.value)) :=
            (private_conservation_nat_sum key ins outs hblind hin' hout').1
              (by simpa only [homCheck, decide_eq_true_eq, transferPred] using hChk.1)
          exact ⟨hInsEq.down, hOutsEq.down, hblind, hNat, hAll.2⟩⟩

/-- **Audited Private Conservation, End to End** (`0` raw `hblind` assumptions!):
     Blinding conservation `blindSum ins = blindSum outs` is verified inside `auditTransfer`
     via the `auditVk` discharge leaf, yielding exact `Nat` value conservation up to a finite
     two-claim or finite opening-list `cSHAKE256` collision! -/
theorem privPred_conservation_sound (key : CommitKey) (o : Oracle) (σ : Step)
    (ins outs insCert outsCert : List Opening) (claimCert : AuditClaim)
    (bits : Nat) (clear : DistPred)
    (hcheck : (transferPred key ins outs bits clear).check o σ = true)
    (hAudit : AuditSound key o insCert outsCert claimCert)
    (hrange : RangeSound key o (ins ++ outs) bits)
    (hin : ins.length * 2 ^ bits < 2 ^ 256) (hout : outs.length * 2 ^ bits < 2 ^ 256) :
    (blindSum ins = blindSum outs ∧
      natSum (ins.map (·.value)) = natSum (outs.map (·.value)) ∧
      (clear.evalWith o σ).accepts = true) ∨
    CollisionAmong (cshake256Bytes auditCustomization)
      (fun x => x ∈ [(AuditClaim.ofTransfer key ins outs bits).encode, claimCert.encode]) ∨
    CollisionAmong (cshake256Bytes openingCustomization)
      (fun x => x ∈ (ins.map Opening.encode ++ insCert.map Opening.encode) ++
        (outs.map Opening.encode ++ outsCert.map Opening.encode)) := by
  cases privPred_conservation_extract key o σ ins outs insCert outsCert claimCert bits clear
      hcheck hAudit hrange hin hout with
  | inl hp => exact .inl ⟨hp.down.2.2.1, hp.down.2.2.2.1, hp.down.2.2.2.2⟩
  | inr hc =>
    cases hc with
    | inl hA => exact .inr (.inl hA.toCollisionAmong)
    | inr hO => exact .inr (.inr hO.toCollisionAmong)

/-- All premises of `privPred_conservation_sound` are jointly inhabited on the real `auditedOracle`
(NOT a credulous `fun _ => .true3` rubber-stamp!). -/
theorem privPred_conservation_inhabited :
    ∃ (key : CommitKey) (o : Oracle) (σ : Step) (ins outs : List Opening) (bits : Nat),
      (transferPred key ins outs bits .tt).check o σ = true ∧
      AuditSound key o ins outs (AuditClaim.ofTransfer key ins outs bits) ∧
      RangeSound key o (ins ++ outs) bits ∧ 0 < ins.length ∧
      ins.length * 2 ^ bits < 2 ^ 256 ∧ outs.length * 2 ^ bits < 2 ^ 256 := by
  let ins : List Opening := [⟨5#256, 7#256⟩]
  let outs : List Opening := [⟨5#256, 7#256⟩]
  let claim := AuditClaim.ofTransfer demoKey ins outs 8
  have hAud : auditTransfer demoKey ins outs claim = true := by
    simp [auditTransfer, claim, AuditClaim.ofTransfer, ins, outs, blindSum, bvSum]
  refine ⟨demoKey, auditedOracle demoKey ins outs 8, fun _ => ⟨none, none⟩, ins, outs, 8,
    ?_, auditedOracle_auditSound demoKey ins outs 8 hAud, ?_, by decide, by decide, by decide⟩
  · rw [PrivPred.check_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro c hc
      simp only [transferPred, ins, outs, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false, or_self] at hc
      subst hc
      unfold auditedOracle
      have hNe : decide (rangeVk ⟨(⟨5#256, 7#256⟩ : Opening).commit demoKey, 8⟩ = auditVk claim) = false :=
        decide_eq_false (fun h => auditVk_ne_rangeVk claim _ h.symm)
      have hHit : ((ins ++ outs).any fun op =>
          decide (op.value.toNat < 2 ^ 8) &&
          decide (rangeVk ⟨(⟨5#256, 7#256⟩ : Opening).commit demoKey, 8⟩ =
            rangeVk ⟨op.commit demoKey, 8⟩)) = true :=
        List.any_eq_true.2 ⟨⟨5#256, 7#256⟩, by simp [ins],
          Bool.and_eq_true_iff.2 ⟨by decide, decide_eq_true rfl⟩⟩
      rw [hNe]
      simp [hHit]
    · have hAudHit : auditedOracle demoKey ins outs 8 (auditVk claim) = .true3 := by
        unfold auditedOracle
        simp [claim, hAud]
      simp [transferPred, claim, hAudHit, DistPred.tt, DistPred.evalWith, DistPredList.evalList,
        combine3_true, ofBool, KleenePred3.and3, KleenePred3.accepts]
  · intro op hop _
    simp only [ins, outs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, or_self] at hop
    subst hop; decide

/-! ## 8. Sealing: cSHAKE256 counter mode with coverage + fresh-nonce ledger -/

def xorWith : List UInt8 → List UInt8 → List UInt8
  | [], _ => []
  | m :: ms, [] => m :: xorWith ms []
  | m :: ms, k :: ks => (m ^^^ k) :: xorWith ms ks

theorem xorWith_length : ∀ (m ks : List UInt8), (xorWith m ks).length = m.length
  | [], _ => by simp [xorWith]
  | _ :: ms, [] => by simp [xorWith, xorWith_length ms []]
  | _ :: ms, _ :: ks => by simp [xorWith, xorWith_length ms ks]

theorem xorWith_xorWith : ∀ (m ks : List UInt8), xorWith (xorWith m ks) ks = m
  | [], _ => by simp [xorWith]
  | m :: ms, [] => by simp [xorWith, xorWith_xorWith ms []]
  | m :: ms, k :: ks => by
    simp only [xorWith, xorWith_xorWith ms ks, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

theorem xorWith_same_pad : ∀ (m₁ m₂ ks : List UInt8),
    m₁.length = m₂.length → m₁.length ≤ ks.length →
    xorWith (xorWith m₁ ks) (xorWith m₂ ks) = xorWith m₁ m₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hL, _ => by cases hL
  | _ :: _, [], _, hL, _ => by cases hL
  | _ :: _, _ :: _, [], _, hCov => by simp at hCov
  | a :: as, b :: bs, k :: ks, hL, hCov => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hL
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hCov
    have hByte : (a ^^^ k) ^^^ (b ^^^ k) = a ^^^ b := by
      have : (a ^^^ k) ^^^ (b ^^^ k) = (a ^^^ b) ^^^ (k ^^^ k) := by ac_rfl
      rw [this, UInt8.xor_self, UInt8.xor_zero]
    simp only [xorWith, hByte, xorWith_same_pad as bs ks hL hCov]

def streamCustomization : List UInt8 := "OBEND.POLIS.SEAL.STREAM/v1".toUTF8.data.toList
def macCustomization : List UInt8 := "OBEND.POLIS.SEAL.MAC/v1".toUTF8.data.toList

def keystream (key nonce : ByteArray) : Nat → Nat → List UInt8
  | 0, _ => []
  | blocks + 1, i =>
    cshake256Bytes streamCustomization
        (encodeFields [key.data.toList, nonce.data.toList, leb128 i]) ++
      keystream key nonce blocks (i + 1)

theorem keystream_length (key nonce : ByteArray) : ∀ (blocks i : Nat),
    (keystream key nonce blocks i).length = 32 * blocks
  | 0, _ => by simp [keystream]
  | blocks + 1, i => by
    simp only [keystream, List.length_append, cshake256Bytes_length,
      keystream_length key nonce blocks (i + 1)]
    omega

def keystreamFor (key nonce : ByteArray) (len : Nat) : List UInt8 :=
  keystream key nonce ((len + 31) / 32) 0

/-- **Full-Pad Coverage (`keystreamFor_covers`)**: `keystreamFor` always produces at least `len`
keystream bytes, so `xorWith`'s unmasked `[]` fallback branch is never entered by `aeadSeal`. -/
theorem keystreamFor_covers (key nonce : ByteArray) (len : Nat) :
    len ≤ (keystreamFor key nonce len).length := by
  rw [keystreamFor, keystream_length]
  omega

def macPreimage (key nonce : ByteArray) (body : List UInt8) : List UInt8 :=
  encodeFields [key.data.toList, nonce.data.toList, body]

def macTag (key nonce : ByteArray) (body : List UInt8) : ByteArray :=
  cshake32ByteArray macCustomization (macPreimage key nonce body)

theorem macTag_binds {k k' n n' : ByteArray} {b b' : List UInt8}
    (h : macTag k n b = macTag k' n' b') :
    (k = k' ∧ n = n' ∧ b = b') ∨ CollisionAmong (cshake256Bytes macCustomization)
      (fun x => x = macPreimage k n b ∨ x = macPreimage k' n' b') := by
  rcases cshake32_binds macCustomization h with hp | hc
  · have hf := encodeFields_injective _ _ hp
    simp only [List.cons.injEq, and_true] at hf
    exact .inl ⟨byteArray_eq_of_toList_eq hf.1, byteArray_eq_of_toList_eq hf.2.1, hf.2.2⟩
  · exact .inr hc

structure Sealed where
  nonce : ByteArray
  body : List UInt8
  tag : ByteArray
  deriving DecidableEq

def aeadSeal (key nonce : ByteArray) (msg : List UInt8) : Sealed :=
  ⟨nonce, xorWith msg (keystreamFor key nonce msg.length),
    macTag key nonce (xorWith msg (keystreamFor key nonce msg.length))⟩

/-- **Two-Time Pad Nonce-Reuse Leak**: sealing two equal-length messages under the same `(key, nonce)`
exposes `xorWith m₁ m₂` directly from the ciphertexts. -/
theorem aeadSeal_nonce_reuse_leaks (key nonce : ByteArray) (m₁ m₂ : List UInt8)
    (hLen : m₁.length = m₂.length) :
    xorWith (aeadSeal key nonce m₁).body (aeadSeal key nonce m₂).body = xorWith m₁ m₂ := by
  simp only [aeadSeal, hLen]
  exact xorWith_same_pad m₁ m₂ _ hLen (hLen ▸ keystreamFor_covers key nonce m₂.length)

def memBytes (x : ByteArray) : List ByteArray → Bool
  | [] => false
  | y :: ys => decide (x = y) || memBytes x ys

theorem memBytes_iff (x : ByteArray) : ∀ (ys : List ByteArray), memBytes x ys = true ↔ x ∈ ys
  | [] => by simp [memBytes]
  | y :: ys => by simp [memBytes, memBytes_iff x ys]

/-- Stateful sealing ledger enforcing strict per-key nonce freshness (`seenNonces.Nodup`). -/
structure SealLedger where
  seenNonces : List ByteArray

def SealLedger.sealFresh (st : SealLedger) (key nonce : ByteArray) (msg : List UInt8) :
    Option (SealLedger × Sealed) :=
  if memBytes nonce st.seenNonces then none
  else some (⟨nonce :: st.seenNonces⟩, aeadSeal key nonce msg)

theorem SealLedger.reused_nonce_refused (st : SealLedger) (key nonce : ByteArray) (msg : List UInt8)
    (hSeen : nonce ∈ st.seenNonces) :
    st.sealFresh key nonce msg = none := by
  simp [SealLedger.sealFresh, (memBytes_iff nonce st.seenNonces).2 hSeen]

theorem SealLedger.sealFresh_preserves_nodup {st st' : SealLedger} {key nonce : ByteArray}
    {msg : List UInt8} {s : Sealed} (hNd : st.seenNonces.Nodup)
    (hOk : st.sealFresh key nonce msg = some (st', s)) :
    st'.seenNonces.Nodup ∧ nonce ∉ st.seenNonces := by
  unfold SealLedger.sealFresh at hOk
  split at hOk
  · cases hOk
  · rename_i hNot
    simp only [Option.some.injEq, Prod.mk.injEq] at hOk
    have hNotMem : nonce ∉ st.seenNonces := fun hm => hNot ((memBytes_iff nonce st.seenNonces).2 hm)
    rw [← hOk.1]
    exact ⟨List.nodup_cons.2 ⟨hNotMem, hNd⟩, hNotMem⟩

def aeadOpen (key : ByteArray) (s : Sealed) : Option (List UInt8) :=
  if s.tag = macTag key s.nonce s.body then
    some (xorWith s.body (keystreamFor key s.nonce s.body.length))
  else none

theorem aeadOpen_aeadSeal (key nonce : ByteArray) (msg : List UInt8) :
    aeadOpen key (aeadSeal key nonce msg) = some msg := by
  simp only [aeadOpen, aeadSeal, ↓reduceIte, xorWith_length, xorWith_xorWith]

theorem aeadOpen_eq_some {key : ByteArray} {s : Sealed} {m : List UInt8}
    (h : aeadOpen key s = some m) :
    s.tag = macTag key s.nonce s.body ∧
      m = xorWith s.body (keystreamFor key s.nonce s.body.length) := by
  unfold aeadOpen at h
  split at h
  · rename_i ht; exact ⟨ht, (Option.some.inj h).symm⟩
  · cases h

theorem aeadOpen_wrong_key {key key' nonce : ByteArray} {msg m : List UInt8}
    (h : aeadOpen key' (aeadSeal key nonce msg) = some m) :
    key' = key ∨ CollisionAmong (cshake256Bytes macCustomization)
      (fun x => x = macPreimage key nonce (aeadSeal key nonce msg).body ∨
        x = macPreimage key' nonce (aeadSeal key nonce msg).body) := by
  have ht := (aeadOpen_eq_some h).1
  rcases macTag_binds (k := key) (k' := key') (n := nonce) (n' := nonce)
      (b := (aeadSeal key nonce msg).body) (b' := (aeadSeal key nonce msg).body) ht with he | hc
  · exact .inl he.1.symm
  · exact .inr hc

theorem aeadOpen_tampered {key nonce nonce' : ByteArray} {msg body' m : List UInt8}
    (h : aeadOpen key ⟨nonce', body', (aeadSeal key nonce msg).tag⟩ = some m) :
    (nonce' = nonce ∧ body' = (aeadSeal key nonce msg).body ∧ m = msg) ∨
      CollisionAmong (cshake256Bytes macCustomization)
        (fun x => x = macPreimage key nonce (aeadSeal key nonce msg).body ∨
          x = macPreimage key nonce' body') := by
  obtain ⟨ht, _⟩ := aeadOpen_eq_some h
  rcases macTag_binds (k := key) (k' := key) (n := nonce) (n' := nonce')
      (b := (aeadSeal key nonce msg).body) (b' := body') ht with he | hc
  · obtain ⟨_, hn, hb⟩ := he; subst hn; subst hb
    refine .inl ⟨rfl, rfl, ?_⟩
    have ho := aeadOpen_aeadSeal key nonce msg
    simp only [aeadSeal] at h ho; rw [ho] at h
    exact (Option.some.inj h).symm
  · exact .inr hc

/-! ## 9. Third-party caveats and their discharge -/

inductive DCaveat where
  | firstParty (pred : DistPred) | bindToParent (binding : ByteArray)
  deriving DecidableEq

def DCaveat.body : DCaveat → List UInt8
  | .firstParty p => 0 :: p.encode | .bindToParent b => 1 :: b.data.toList

structure Discharge where
  createdAt : Nat
  nonce : ByteArray
  caveats : List DCaveat
  tail : ByteArray

def chainCustomization : List UInt8 := "OBEND.POLIS.DISCHARGE.CHAIN/v1".toUTF8.data.toList
def bindCustomization : List UInt8 := "OBEND.POLIS.DISCHARGE.BIND/v1".toUTF8.data.toList
def chainInit (r nonce : ByteArray) (createdAt : Nat) : ByteArray :=
  cshake32ByteArray chainCustomization (encodeFields [[0], r.data.toList, nonce.data.toList, leb128 createdAt])
def chainStep (tail : ByteArray) (c : DCaveat) : ByteArray :=
  cshake32ByteArray chainCustomization (encodeFields [[1], tail.data.toList, c.body])
def replayTail (r nonce : ByteArray) (createdAt : Nat) (cs : List DCaveat) : ByteArray :=
  cs.foldl chainStep (chainInit r nonce createdAt)
def bindingHash (parentTail : ByteArray) : ByteArray :=
  cshake32ByteArray bindCustomization parentTail.data.toList

theorem bindingHash_binds {a b : ByteArray} (h : bindingHash a = bindingHash b) :
    a = b ∨ CollisionAmong (cshake256Bytes bindCustomization)
      (fun x => x = a.data.toList ∨ x = b.data.toList) := by
  rcases cshake32_binds bindCustomization h with hp | hc
  · exact .inl (byteArray_eq_of_toList_eq hp)
  · exact .inr hc

def fresh (createdAt now maxAge : Nat) : Bool :=
  decide (createdAt ≠ 0) && decide (createdAt ≤ now) && decide (now - createdAt ≤ maxAge)
theorem fresh_iff (createdAt now maxAge : Nat) :
    fresh createdAt now maxAge = true ↔ createdAt ≠ 0 ∧ createdAt ≤ now ∧ now - createdAt ≤ maxAge := by
  simp [fresh, and_assoc]
def chainValid (d : Discharge) (r : ByteArray) : Bool :=
  decide (d.tail = replayTail r d.nonce d.createdAt d.caveats)
def boundTo (d : Discharge) (parentTail : ByteArray) : Bool :=
  d.caveats.contains (.bindToParent (bindingHash parentTail))
theorem boundTo_iff (d : Discharge) (parentTail : ByteArray) :
    boundTo d parentTail = true ↔ DCaveat.bindToParent (bindingHash parentTail) ∈ d.caveats := by
  simp [boundTo]
def DCaveat.holds (σ : Step) : DCaveat → Bool
  | .firstParty p => (evalFirstParty σ p).accepts | .bindToParent _ => true
def caveatsHold (σ : Step) (d : Discharge) : Bool := d.caveats.all (DCaveat.holds σ)
theorem caveatsHold_iff (σ : Step) (d : Discharge) :
    caveatsHold σ d = true ↔
      ∀ p, DCaveat.firstParty p ∈ d.caveats → (evalFirstParty σ p).accepts = true := by
  simp only [caveatsHold, List.all_eq_true]
  exact ⟨fun h p hp => h _ hp, fun h c hc => by cases c with | firstParty p => exact h p hc | bindToParent _ => rfl⟩

structure ThirdPartyCaveat where
  location : ByteArray
  ticket : Sealed
  vid : Sealed

def issueCaveat (location k3p ticketNonce vidNonce parentTail r : ByteArray) (pred : VkId) :
    ThirdPartyCaveat :=
  ⟨location, aeadSeal k3p ticketNonce (r.data.toList ++ pred.id.data.toList),
    aeadSeal parentTail vidNonce r.data.toList⟩
def openTicket (k3p : ByteArray) (cav : ThirdPartyCaveat) : Option (ByteArray × VkId) :=
  (aeadOpen k3p cav.ticket).map fun m => (⟨(m.take 32).toArray⟩, ⟨⟨(m.drop 32).toArray⟩⟩)
def createDischarge (r : ByteArray) (createdAt : Nat) (nonce : ByteArray) (preds : List DistPred) :
    Discharge :=
  ⟨createdAt, nonce, preds.map .firstParty, replayTail r nonce createdAt (preds.map .firstParty)⟩
def bindDischarge (d : Discharge) (parentTail : ByteArray) : Discharge :=
  { d with
    caveats := d.caveats ++ [.bindToParent (bindingHash parentTail)]
    tail := chainStep d.tail (.bindToParent (bindingHash parentTail)) }
def serveTicket (k3p : ByteArray) (cav : ThirdPartyCaveat) (vouches : VkId → Bool)
    (createdAt : Nat) (nonce : ByteArray) (preds : List DistPred) : Option Discharge :=
  match openTicket k3p cav with
  | some (r, pred) => if vouches pred then some (createDischarge r createdAt nonce preds) else none
  | none => none
def recoverKey (cav : ThirdPartyCaveat) (parentTail : ByteArray) : Option ByteArray :=
  (aeadOpen parentTail cav.vid).map fun m => ⟨m.toArray⟩
def verifyDischarge (cav : ThirdPartyCaveat) (d : Discharge) (parentTail : ByteArray) (σ : Step)
    (now maxAge : Nat) : Bool :=
  match recoverKey cav parentTail with
  | none => false
  | some r => fresh d.createdAt now maxAge && chainValid d r && boundTo d parentTail && caveatsHold σ d

theorem verifyDischarge_iff (cav : ThirdPartyCaveat) (d : Discharge) (parentTail : ByteArray)
    (σ : Step) (now maxAge : Nat) :
    verifyDischarge cav d parentTail σ now maxAge = true ↔
      ∃ r, recoverKey cav parentTail = some r ∧
        (d.createdAt ≠ 0 ∧ d.createdAt ≤ now ∧ now - d.createdAt ≤ maxAge) ∧
        d.tail = replayTail r d.nonce d.createdAt d.caveats ∧
        DCaveat.bindToParent (bindingHash parentTail) ∈ d.caveats ∧
        ∀ p, DCaveat.firstParty p ∈ d.caveats → (evalFirstParty σ p).accepts = true := by
  unfold verifyDischarge
  cases recoverKey cav parentTail with
  | none => simp
  | some r =>
    simp only [Bool.and_eq_true, fresh_iff, chainValid, decide_eq_true_eq, boundTo_iff,
      caveatsHold_iff, Option.some.injEq]
    constructor
    · rintro ⟨⟨⟨hf, hc⟩, hb⟩, hp⟩; exact ⟨r, rfl, hf, hc, hb, hp⟩
    · rintro ⟨r', hr', hf, hc, hb, hp⟩; subst hr'; exact ⟨⟨⟨hf, hc⟩, hb⟩, hp⟩

theorem byteArray_toList_toArray (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  cases b; simp

theorem openTicket_issueCaveat (location k3p n₁ n₂ parentTail r : ByteArray) (pred : VkId)
    (hr : r.size = 32) :
    openTicket k3p (issueCaveat location k3p n₁ n₂ parentTail r pred) = some (r, pred) := by
  have hlen : r.data.toList.length = 32 := by cases r; simpa [ByteArray.size] using hr
  obtain ⟨pid⟩ := pred
  simp only [openTicket, issueCaveat, aeadOpen_aeadSeal, Option.map_some, List.take_left' hlen,
    List.drop_left' hlen, byteArray_toList_toArray]

theorem honestDischarge_accepts (location k3p n₁ n₂ parentTail r nonce : ByteArray) (pred : VkId)
    (vouches : VkId → Bool) (createdAt now maxAge : Nat) (preds : List DistPred) (σ : Step)
    (hr : r.size = 32) (hvouch : vouches pred = true)
    (hfresh : fresh createdAt now maxAge = true)
    (hpreds : ∀ p, p ∈ preds → (evalFirstParty σ p).accepts = true) :
    ∃ d, serveTicket k3p (issueCaveat location k3p n₁ n₂ parentTail r pred) vouches createdAt
          nonce preds = some d ∧
      verifyDischarge (issueCaveat location k3p n₁ n₂ parentTail r pred)
        (bindDischarge d parentTail) parentTail σ now maxAge = true := by
  refine ⟨createDischarge r createdAt nonce preds, ?_, ?_⟩
  · simp only [serveTicket, openTicket_issueCaveat location k3p n₁ n₂ parentTail r pred hr, hvouch,
      ↓reduceIte]
  · rw [verifyDischarge_iff]
    refine ⟨r, ?_, (fresh_iff _ _ _).1 hfresh, ?_, ?_, ?_⟩
    · simp only [recoverKey, issueCaveat, aeadOpen_aeadSeal, Option.map_some,
        byteArray_toList_toArray]
    · simp only [bindDischarge, createDischarge, replayTail, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    · simp [bindDischarge]
    · intro p hp
      simp only [bindDischarge, createDischarge, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, DCaveat.firstParty.injEq, exists_eq_right] at hp
      exact hpreds p hp

theorem staleDischarge_refused (cav : ThirdPartyCaveat) (d : Discharge) (parentTail : ByteArray)
    (σ : Step) (now maxAge : Nat)
    (hstale : d.createdAt = 0 ∨ now < d.createdAt ∨ maxAge < now - d.createdAt) :
    verifyDischarge cav d parentTail σ now maxAge = false := by
  cases hv : verifyDischarge cav d parentTail σ now maxAge with
  | false => rfl
  | true =>
    obtain ⟨_, _, hf, _⟩ := (verifyDischarge_iff cav d parentTail σ now maxAge).1 hv
    omega

theorem unbound_or_wrong_parent_refused (cav : ThirdPartyCaveat) (d : Discharge)
    (tailA tailB : ByteArray) (σ : Step) (now maxAge : Nat)
    (hbind : ∀ b, DCaveat.bindToParent b ∈ d.caveats → b = bindingHash tailA)
    (hv : verifyDischarge cav d tailB σ now maxAge = true) :
    (∃ b, DCaveat.bindToParent b ∈ d.caveats) ∧
      (tailA = tailB ∨ CollisionAmong (cshake256Bytes bindCustomization)
        (fun x => x = tailA.data.toList ∨ x = tailB.data.toList)) := by
  obtain ⟨_, _, _, _, hb, _⟩ := (verifyDischarge_iff cav d tailB σ now maxAge).1 hv
  refine ⟨⟨_, hb⟩, (bindingHash_binds (hbind _ hb)).imp Eq.symm (CollisionAmong.mono fun _ hx => ?_)⟩
  exact hx.symm

end Obend.Polis.PrivatePredicate
end
