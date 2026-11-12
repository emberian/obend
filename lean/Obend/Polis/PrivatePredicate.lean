module
/-
# Obend.Polis.PrivatePredicate — first-order distributed predicates, graded disclosure, third-party discharge

A guard that several vats must agree on is data: it is hashed, compared, shipped, partially evaluated
by a vat that holds some of its slots and finished by one that holds the rest.

1. `DistPred`: a first-order predicate over a step of numbered slots. Every leaf is a slot number, an
   integer, a finite integer list, a 32-byte cSHAKE256 digest or a verification-key identifier; there
   is no function in the tree. `DistPred.encode` is an injective byte code. The converse is
   `opaque_closure_collapses_finite_encoding`: a code table for `State → Bool` closures smaller than
   a separating family identifies two closures that differ on a state, and
   `opaque_closure_escapes_descriptor_table` is the diagonal argument for a table of any size.
2. `DistPred.evalWith`: strong Kleene evaluation (Kleene, *Introduction to Metamathematics*, 1952,
   §64) under an oracle `VkId → KleenePred3`; a `witnessed vk` leaf is `unbound3` when no discharge
   was presented. `negated_witnessed_refused_firstParty`, `evalFirstParty_sound_for_evalWith`,
   `discharge_monotone`.
3. `commitVal`: the affine commitment `g·v + h·b` over the ring `ℤ/2²⁵⁶`, in the shape of Pedersen,
   *Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing* (CRYPTO 1991). The
   algebra a verifier relies on is proved: additivity (`commitSum_collapse`) and, at equal blinding
   totals, that the check on commitments holds exactly when the hidden value totals agree
   (`private_conservation_iff_value_sum`; `g` is a unit, so there is no hypothesis). Totals are modulo
   `2²⁵⁶`; `private_conservation_nat_sum` removes the modulus under the bound the range tier supplies.
   Hiding is a property of the group the generators live in and is not claimed for this ring, where
   the discrete logarithm is division.
4. `PrivPred`: the three tiers. Each range claim is a `witnessed` leaf named by the digest of the
   claim, so it fails closed without a discharge. `privPred_conservation_sound` is over the naturals.
5. `pevalVat`: partial evaluation (Jones, Gomard and Sestoft, *Partial Evaluation and Automatic
   Program Generation*, 1993) by a vat over the slots it holds. The residual names none of them
   (`pevalVat_hides_known_slots`) and has the verdict of the whole predicate on the joined state
   (`eval_subst_eq_eval_pevalVat`). It does reveal which of the vat's atoms were decided.
6. Third-party discharge after Birgisson, Politz, Erlingsson, Taly, Vrable and Lentczner, *Macaroons:
   Cookies with Contextual Caveats for Decentralized Authorization in the Cloud* (NDSS 2014): a ticket
   sealed to the third party and a verifier id sealed under the parent's tail both carry the
   discharge key; the discharge is a keyed chain that must be fresh and bound to that parent. Sealing
   is cSHAKE256 in counter mode with a cSHAKE256 tag. `verifyDischarge_iff`,
   `honestDischarge_accepts`, `staleDischarge_refused`, `unbound_or_wrong_parent_refused`.
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

/-- A slot of a vat's state. -/
abbrev SlotId := Nat

/-- The name of a claim proved outside the vat: 32 bytes, never a function. -/
structure VkId where
  id : ByteArray
  deriving DecidableEq

/-- What one turn did to a slot: its value before and after, either of which may be absent. -/
structure SlotStep where
  old : Option Int
  new : Option Int
  deriving DecidableEq

/-- A step of the whole state. -/
abbrev Step := SlotId → SlotStep

/-- The tests an atom can make on one slot of a step. -/
inductive SlotTest where
  /-- The new value is `value`. -/
  | eq (value : Int)
  /-- The new value is at most `value`. -/
  | le (value : Int)
  /-- The new value is in `set`. -/
  | memberOf (set : List Int)
  /-- A slot that held a nonzero value keeps it. -/
  | writeOnce
  /-- The value did not decrease; both sides must be present. -/
  | monotone
  /-- The cSHAKE256 digest of the new value is `digest`. -/
  | hashEq (digest : ByteArray)
  deriving DecidableEq

mutual
/-- A distributed predicate. `all .nil` is truth and `any .nil` is falsehood. -/
inductive DistPred where
  | atom (slot : SlotId) (test : SlotTest)
  /-- A claim discharged by a third party, named by `vk`. -/
  | witnessed (vk : VkId)
  | not (p : DistPred)
  | all (ps : DistPredList)
  | any (ps : DistPredList)
/-- The children of `all` and `any`. -/
inductive DistPredList where
  | nil
  | cons (p : DistPred) (ps : DistPredList)
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

/-- The children as a list. -/
def DistPredList.ofList : List DistPred → DistPredList
  | [] => .nil
  | p :: ps => .cons p (DistPredList.ofList ps)

/-! ## 2. The byte code -/

/-- An integer: a sign byte and the LEB128 magnitude. -/
def encodeInt : Int → List UInt8
  | .ofNat n => 0 :: leb128 n
  | .negSucc n => 1 :: leb128 n

theorem encodeInt_prefix_inj {a b : Int} {r₁ r₂ : List UInt8}
    (h : encodeInt a ++ r₁ = encodeInt b ++ r₂) : a = b ∧ r₁ = r₂ := by
  cases a <;> cases b <;> simp only [encodeInt, List.cons_append] at h <;>
    have hc := List.cons.inj h
  · obtain ⟨hn, hr⟩ := leb128_prefix_inj hc.2
    exact ⟨by rw [hn], hr⟩
  · exact absurd hc.1 (by decide)
  · exact absurd hc.1 (by decide)
  · obtain ⟨hn, hr⟩ := leb128_prefix_inj hc.2
    exact ⟨by rw [hn], hr⟩

/-- A list of integers, each behind a continuation byte. -/
def encodeInts : List Int → List UInt8
  | [] => [0]
  | x :: xs => 1 :: (encodeInt x ++ encodeInts xs)

theorem encodeInts_prefix_inj : ∀ (a b : List Int) (r₁ r₂ : List UInt8),
    encodeInts a ++ r₁ = encodeInts b ++ r₂ → a = b ∧ r₁ = r₂
  | [], [], _, _, h => by
    simp only [encodeInts, List.cons_append, List.nil_append] at h
    exact ⟨rfl, (List.cons.inj h).2⟩
  | [], _ :: _, _, _, h => by
    simp only [encodeInts, List.cons_append, List.nil_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | _ :: _, [], _, _, h => by
    simp only [encodeInts, List.cons_append, List.nil_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | x :: xs, y :: ys, r₁, r₂, h => by
    simp only [encodeInts, List.cons_append, List.append_assoc] at h
    obtain ⟨hxy, hrest⟩ := encodeInt_prefix_inj (List.cons.inj h).2
    obtain ⟨hl, hr⟩ := encodeInts_prefix_inj xs ys r₁ r₂ hrest
    exact ⟨by rw [hxy, hl], hr⟩

/-- A slot test: a tag byte and its operand. -/
def SlotTest.encode : SlotTest → List UInt8
  | .eq v => 0 :: encodeInt v
  | .le v => 1 :: encodeInt v
  | .memberOf set => 2 :: encodeInts set
  | .writeOnce => [3]
  | .monotone => [4]
  | .hashEq d => 5 :: encodeListField d.data.toList

theorem SlotTest.encode_prefix_inj (a b : SlotTest) (r₁ r₂ : List UInt8)
    (h : a.encode ++ r₁ = b.encode ++ r₂) : a = b ∧ r₁ = r₂ := by
  cases a <;> cases b <;>
    simp only [SlotTest.encode, List.cons_append, List.nil_append] at h <;>
    have hc := List.cons.inj h <;>
    first
      | exact absurd hc.1 (by decide)
      | exact ⟨rfl, hc.2⟩
      | (obtain ⟨hv, hr⟩ := encodeInt_prefix_inj hc.2
         exact ⟨by rw [hv], hr⟩)
      | (obtain ⟨hv, hr⟩ := encodeInts_prefix_inj _ _ _ _ hc.2
         exact ⟨by rw [hv], hr⟩)
      | (obtain ⟨hv, hr⟩ := encodeListField_prefix_inj hc.2
         exact ⟨by rw [byteArray_eq_of_toList_eq hv], hr⟩)

mutual
/-- The byte code of a predicate: a tag byte, then the operands, each self-delimiting. -/
def DistPred.encode : DistPred → List UInt8
  | .atom s t => 0 :: (leb128 s ++ t.encode)
  | .witnessed vk => 1 :: encodeListField vk.id.data.toList
  | .not p => 2 :: p.encode
  | .all ps => 3 :: ps.encode
  | .any ps => 4 :: ps.encode
termination_by structural p => p
/-- The byte code of a child list. -/
def DistPredList.encode : DistPredList → List UInt8
  | .nil => [0]
  | .cons p ps => 1 :: (p.encode ++ ps.encode)
termination_by structural ps => ps
end

mutual
theorem DistPred.encode_prefix_inj : ∀ (a b : DistPred) (r₁ r₂ : List UInt8),
    a.encode ++ r₁ = b.encode ++ r₂ → a = b ∧ r₁ = r₂
  | .atom s t, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append, List.append_assoc] at h <;>
      have hc := List.cons.inj h <;>
      first
        | exact absurd hc.1 (by decide)
        | (obtain ⟨hs, hrest⟩ := leb128_prefix_inj hc.2
           obtain ⟨ht, hr⟩ := SlotTest.encode_prefix_inj _ _ _ _ hrest
           exact ⟨by rw [hs, ht], hr⟩)
  | .witnessed vk, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first
        | exact absurd hc.1 (by decide)
        | (obtain ⟨hv, hr⟩ := encodeListField_prefix_inj hc.2
           obtain ⟨i⟩ := vk
           rename_i vk'
           obtain ⟨j⟩ := vk'
           exact ⟨by rw [byteArray_eq_of_toList_eq (a := i) (b := j) hv], hr⟩)
  | .not p, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first
        | exact absurd hc.1 (by decide)
        | (obtain ⟨hp, hr⟩ := DistPred.encode_prefix_inj p _ r₁ r₂ hc.2
           exact ⟨by rw [hp], hr⟩)
  | .all ps, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first
        | exact absurd hc.1 (by decide)
        | (obtain ⟨hp, hr⟩ := DistPredList.encode_prefix_inj ps _ r₁ r₂ hc.2
           exact ⟨by rw [hp], hr⟩)
  | .any ps, b, r₁, r₂, h => by
    cases b <;> simp only [DistPred.encode, List.cons_append] at h <;>
      have hc := List.cons.inj h <;>
      first
        | exact absurd hc.1 (by decide)
        | (obtain ⟨hp, hr⟩ := DistPredList.encode_prefix_inj ps _ r₁ r₂ hc.2
           exact ⟨by rw [hp], hr⟩)
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

/-- Pigeonhole on an initial segment: `n + 1` values below `n` repeat. The search for a repeat is a
bounded decidable one, so the two indices are computed, not chosen. -/
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
        have h1 := h i (by omega)
        have h2 := h (n + 1) (Nat.le_refl _)
        have h3 := hne i hi
        split <;> omega
      obtain ⟨i, j, hij, hj, he⟩ :=
        pigeonhole n (fun i => if f i < f (n + 1) then f i else f i - 1) hg
      refine ⟨i, j, hij, by omega, ?_⟩
      have hi3 := hne i (by omega)
      have hj3 := hne j hj
      have he' : (if f i < f (n + 1) then f i else f i - 1) =
          (if f j < f (n + 1) then f j else f j - 1) := he
      split at he' <;> split at he' <;> omega

/-- **Closures do not fit a finite code table.** Take any family of `n + 1` predicates on `State`
that pairwise differ somewhere. Every encoding of `State → Bool` into `n` codes gives two
extensionally different closures the same code, so whatever reads the code (a circuit, a cost
model, another vat) cannot tell apart two guards the executor distinguishes. -/
theorem opaque_closure_collapses_finite_encoding {State : Type} (n : Nat)
    (family : Nat → State → Bool)
    (hfamily : ∀ i j, i < j → j ≤ n → ∃ s, family i s ≠ family j s)
    (encode : (State → Bool) → Fin n) :
    ∃ f g : State → Bool, (∃ s, f s ≠ g s) ∧ encode f = encode g := by
  obtain ⟨i, j, hij, hj, he⟩ :=
    pigeonhole n (fun i => (encode (family i)).val) (fun i _ => (encode (family i)).isLt)
  exact ⟨family i, family j, hfamily i j hij hj, Fin.ext he⟩

/-- The same over steps: the guards `new[0] = i` already separate. -/
theorem guard_closure_collapses_finite_encoding (n : Nat) (encode : (Step → Bool) → Fin n) :
    ∃ f g : Step → Bool, (∃ σ, f σ ≠ g σ) ∧ encode f = encode g := by
  refine opaque_closure_collapses_finite_encoding n
    (fun i σ => decide ((σ 0).new = some (Int.ofNat i))) ?_ encode
  intro i j hij _
  refine ⟨fun _ => ⟨none, some (Int.ofNat i)⟩, ?_⟩
  simp
  omega

/-- **No descriptor table reaches every closure**, however large: for any `decode` from codes to
predicates on codes, the diagonal predicate differs from every decoded one. -/
theorem opaque_closure_escapes_descriptor_table {Code : Type} (decode : Code → Code → Bool) :
    ∃ f : Code → Bool, ∀ c, ∃ s, decode c s ≠ f s :=
  ⟨fun s => !decode s s, fun c => ⟨c, by
    show decode c c ≠ !decode c c
    generalize decode c c = b
    cases b <;> decide⟩⟩

/-! ## 4. Evaluation -/

/-- Customization string of the slot-value digest. -/
def slotCustomization : List UInt8 := "OBEND.POLIS.DISTPRED.SLOT/v1".toUTF8.data.toList

/-- The 32-byte digest a `hashEq` atom compares against. -/
def slotDigest (value : Int) : ByteArray := cshake32ByteArray slotCustomization (encodeInt value)

/-- Two values with one digest are equal, or their encodings collide. -/
theorem slotDigest_binds {a b : Int} (h : slotDigest a = slotDigest b) :
    a = b ∨ CollisionAmong (cshake256Bytes slotCustomization)
      (fun x => x = encodeInt a ∨ x = encodeInt b) := by
  rcases cshake32_binds slotCustomization h with hp | hc
  · exact .inl (encodeInt_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hp])).1
  · exact .inr hc

/-- Decide a test on one slot of a step. An absent value fails every test except the first write of
a `writeOnce` slot. -/
def SlotTest.holds : SlotTest → SlotStep → Bool
  | .eq v, st => decide (st.new = some v)
  | .le v, st =>
    match st.new with
    | some x => decide (x ≤ v)
    | none => false
  | .memberOf set, st =>
    match st.new with
    | some x => set.contains x
    | none => false
  | .writeOnce, st =>
    match st.old with
    | none => true
    | some o => decide (o = 0) || decide (st.new = some o)
  | .monotone, st =>
    match st.old, st.new with
    | some o, some n => decide (o ≤ n)
    | _, _ => false
  | .hashEq d, st =>
    match st.new with
    | some x => decide (slotDigest x = d)
    | none => false

/-- What is known of the third-party claims: verified, refuted, or not presented. -/
abbrev Oracle := VkId → KleenePred3

/-- No discharge was presented for any claim. -/
def noOracle : Oracle := fun _ => .unbound3

/-- The claims in `ds` were discharged; nothing is known of the others. -/
def dischargeOracle (ds : List VkId) : Oracle := fun vk => if vk ∈ ds then .true3 else .unbound3

/-- A decided verdict. -/
def ofBool : Bool → KleenePred3
  | true => .true3
  | false => .false3

/-- The connective of a child list: conjunction for `all`, disjunction for `any`. -/
def combine3 : Bool → KleenePred3 → KleenePred3 → KleenePred3
  | true, x, y => x.and3 y
  | false, x, y => x.or3 y

mutual
/-- Strong Kleene evaluation of a predicate on a step, under an oracle for its claims. -/
def DistPred.evalWith (o : Oracle) (σ : Step) : DistPred → KleenePred3
  | .atom s t => ofBool (t.holds (σ s))
  | .witnessed vk => o vk
  | .not p => (p.evalWith o σ).not3
  | .all ps => ps.evalList o σ true
  | .any ps => ps.evalList o σ false
termination_by structural p => p
/-- The conjunction (`conj = true`) or disjunction of the children. -/
def DistPredList.evalList (o : Oracle) (σ : Step) (conj : Bool) : DistPredList → KleenePred3
  | .nil => ofBool conj
  | .cons p ps => combine3 conj (p.evalWith o σ) (ps.evalList o σ conj)
termination_by structural ps => ps
end

/-- Evaluation by the vat alone, with no discharge for any claim. -/
def evalFirstParty (σ : Step) (p : DistPred) : KleenePred3 := p.evalWith noOracle σ

/-- A predicate admits a step only when it evaluates to `true3`. -/
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
    combine3 conj (ofBool (!conj)) x = ofBool (!conj) := by
  cases conj <;> cases x <;> rfl

theorem combine3_zero_right (conj : Bool) (x : KleenePred3) :
    combine3 conj x (ofBool (!conj)) = ofBool (!conj) := by
  cases conj <;> cases x <;> rfl

theorem combine3_ofBool (conj a b : Bool) :
    combine3 conj (ofBool a) (ofBool b) = ofBool (if conj then a && b else a || b) := by
  cases conj <;> cases a <;> cases b <;> rfl

mutual
/-- Evaluation is monotone in what the oracle knows. -/
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

/-- **A first-party verdict stands.** Whatever the vat decides with no oracle, true or false, is the
verdict under every oracle: discharges only ever settle what was left open. -/
theorem evalFirstParty_sound_for_evalWith (o : Oracle) (σ : Step) (p : DistPred)
    (h : evalFirstParty σ p ≠ .unbound3) : p.evalWith o σ = evalFirstParty σ p := by
  rcases DistPred.evalWith_refines (o := noOracle) (o' := o) (fun _ => .inl rfl) σ p with hu | he
  · exact absurd hu h
  · exact he.symm

/-- **Fail closed at both polarities.** With no discharge a `witnessed` leaf is refused, and so is
its negation: a law "deny when credential `vk` is shown" cannot be turned into "admit everything" by
showing nothing. -/
theorem negated_witnessed_refused_firstParty (σ : Step) (vk : VkId) :
    (evalFirstParty σ (.not (.witnessed vk))).accepts = false ∧
      (evalFirstParty σ (.witnessed vk)).accepts = false := by
  simp [evalFirstParty, DistPred.evalWith, noOracle, KleenePred3.not3, KleenePred3.accepts]

/-- Presenting discharges never makes a negated claim true: only a refutation could. -/
theorem negated_witnessed_refused_under_discharges (ds : List VkId) (σ : Step) (vk : VkId) :
    admits (dischargeOracle ds) σ (.not (.witnessed vk)) = false := by
  simp only [admits, DistPred.evalWith, dischargeOracle]
  split <;> rfl

/-- **Discharges are monotone.** A step admitted with the discharges `ds` is admitted with any
larger set. -/
theorem discharge_monotone {ds ds' : List VkId} (hsub : ∀ vk, vk ∈ ds → vk ∈ ds') (σ : Step)
    (p : DistPred) (h : admits (dischargeOracle ds) σ p = true) :
    admits (dischargeOracle ds') σ p = true := by
  have hr : ∀ vk, KleenePred3.Refines (dischargeOracle ds vk) (dischargeOracle ds' vk) := by
    intro vk
    by_cases hm : vk ∈ ds
    · exact .inr (by simp [dischargeOracle, hm, hsub vk hm])
    · exact .inl (by simp [dischargeOracle, hm])
  have ht := (accepts_iff_true3 _).1 h
  rcases DistPred.evalWith_refines hr σ p with hu | he
  · rw [ht] at hu
    cases hu
  · exact (accepts_iff_true3 _).2 (he ▸ ht)

mutual
/-- No `witnessed` leaf occurs. -/
def DistPred.witnessedFree : DistPred → Bool
  | .atom _ _ => true
  | .witnessed _ => false
  | .not p => p.witnessedFree
  | .all ps => ps.witnessedFree
  | .any ps => ps.witnessedFree
termination_by structural p => p
def DistPredList.witnessedFree : DistPredList → Bool
  | .nil => true
  | .cons p ps => p.witnessedFree && ps.witnessedFree
termination_by structural ps => ps
end

mutual
theorem DistPred.evalWith_of_witnessedFree (σ : Step) :
    ∀ p : DistPred, p.witnessedFree = true → ∃ b : Bool, ∀ o : Oracle, p.evalWith o σ = ofBool b
  | .atom s t, _ => ⟨t.holds (σ s), fun _ => by simp only [DistPred.evalWith]⟩
  | .witnessed _, h => by simp [DistPred.witnessedFree] at h
  | .not p, h => by
    obtain ⟨b, hb⟩ := DistPred.evalWith_of_witnessedFree σ p
      (by simpa only [DistPred.witnessedFree] using h)
    refine ⟨!b, fun o => ?_⟩
    simp only [DistPred.evalWith, hb o]
    cases b <;> rfl
  | .all ps, h => by
    obtain ⟨b, hb⟩ := DistPredList.evalList_of_witnessedFree σ true ps
      (by simpa only [DistPred.witnessedFree] using h)
    exact ⟨b, fun o => by simp only [DistPred.evalWith, hb o]⟩
  | .any ps, h => by
    obtain ⟨b, hb⟩ := DistPredList.evalList_of_witnessedFree σ false ps
      (by simpa only [DistPred.witnessedFree] using h)
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

/-- **On a predicate with no third-party claim the vat needs no oracle**: it decides the predicate,
and every oracle gives the same verdict. -/
theorem evalFirstParty_decides_witnessedFree (o : Oracle) (σ : Step) (p : DistPred)
    (h : p.witnessedFree = true) :
    evalFirstParty σ p ≠ .unbound3 ∧ p.evalWith o σ = evalFirstParty σ p := by
  obtain ⟨b, hb⟩ := DistPred.evalWith_of_witnessedFree σ p h
  refine ⟨?_, ?_⟩
  · rw [evalFirstParty, hb noOracle]
    cases b <;> simp [ofBool]
  · rw [evalFirstParty, hb o, hb noOracle]

/-! ## 5. Residuals: what one vat computes and what it hands on -/

/-- A vat's slice of a step: the slots it holds, each with its whole before and after. -/
abbrev View := SlotId → Option SlotStep

/-- The step agrees with the vat's slice wherever the vat holds a slot. -/
def Agrees (v : View) (σ : Step) : Prop := ∀ s st, v s = some st → σ s = st

/-- The vat's slice laid over the rest of the step. -/
def overlay (v : View) (rest : Step) : Step := fun s => (v s).getD (rest s)

theorem agrees_overlay (v : View) (rest : Step) : Agrees v (overlay v rest) := by
  intro s st h
  simp [overlay, h]

/-- A decided verdict as a predicate. -/
def constP : Bool → DistPred
  | true => .all .nil
  | false => .any .nil

/-- A child list under its connective. -/
def listP : Bool → DistPredList → DistPred
  | true, ps => .all ps
  | false, ps => .any ps

/-- The verdict a predicate is, when it is a constant. -/
def DistPred.constOf : DistPred → Option Bool
  | .all .nil => some true
  | .any .nil => some false
  | _ => none

theorem constOf_eq_some {p : DistPred} {b : Bool} (h : p.constOf = some b) : p = constP b := by
  unfold DistPred.constOf at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem evalWith_constP (o : Oracle) (σ : Step) (b : Bool) :
    (constP b).evalWith o σ = ofBool b := by
  cases b <;> rfl

theorem evalWith_listP (o : Oracle) (σ : Step) (conj : Bool) (ps : DistPredList) :
    (listP conj ps).evalWith o σ = ps.evalList o σ conj := by
  cases conj <;> simp only [listP, DistPred.evalWith]

/-- An atom on a slot the vat holds is its verdict; any other atom stays. -/
def pevalAtom (v : View) (s : SlotId) (t : SlotTest) : DistPred :=
  match v s with
  | some st => constP (t.holds st)
  | none => .atom s t

/-- Negation, folded on a constant. -/
def notR (p : DistPred) : DistPred :=
  match p.constOf with
  | some b => constP (!b)
  | none => .not p

/-- Some child is the constant `b`. -/
def DistPredList.hasConst (b : Bool) : DistPredList → Bool
  | .nil => false
  | .cons p ps => p.constOf == some b || ps.hasConst b

/-- The children that are not the constant `b`. -/
def DistPredList.dropConst (b : Bool) : DistPredList → DistPredList
  | .nil => .nil
  | .cons p ps => if p.constOf = some b then ps.dropConst b else .cons p (ps.dropConst b)

/-- A connective, folded: a child that decides it is its verdict, neutral children vanish. -/
def foldR (conj : Bool) (ps : DistPredList) : DistPred :=
  if ps.hasConst (!conj) then constP (!conj) else listP conj (ps.dropConst conj)

mutual
/-- **The residual** of a predicate for a vat: every atom on a slot the vat holds is evaluated, and
every connective whose verdict that settles is folded. -/
def DistPred.pevalVat (v : View) : DistPred → DistPred
  | .atom s t => pevalAtom v s t
  | .witnessed vk => .witnessed vk
  | .not p => notR (p.pevalVat v)
  | .all ps => foldR true (ps.pevalVat v)
  | .any ps => foldR false (ps.pevalVat v)
termination_by structural p => p
def DistPredList.pevalVat (v : View) : DistPredList → DistPredList
  | .nil => .nil
  | .cons p ps => .cons (p.pevalVat v) (ps.pevalVat v)
termination_by structural ps => ps
end

mutual
/-- The slots a predicate reads. -/
def DistPred.mentions (s : SlotId) : DistPred → Bool
  | .atom s' _ => s' == s
  | .witnessed _ => false
  | .not p => p.mentions s
  | .all ps => ps.mentions s
  | .any ps => ps.mentions s
termination_by structural p => p
def DistPredList.mentions (s : SlotId) : DistPredList → Bool
  | .nil => false
  | .cons p ps => p.mentions s || ps.mentions s
termination_by structural ps => ps
end

theorem evalWith_notR (o : Oracle) (σ : Step) (p : DistPred) :
    (notR p).evalWith o σ = (p.evalWith o σ).not3 := by
  unfold notR
  split
  · rename_i b hb
    rw [constOf_eq_some hb, evalWith_constP, evalWith_constP]
    cases b <;> rfl
  · simp only [DistPred.evalWith]

theorem DistPredList.evalList_dropConst (o : Oracle) (σ : Step) (conj : Bool) :
    ∀ ps : DistPredList, (ps.dropConst conj).evalList o σ conj = ps.evalList o σ conj
  | .nil => by rfl
  | .cons p ps => by
    simp only [DistPredList.dropConst]
    split
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
  unfold foldR
  split
  · rename_i h
    rw [DistPredList.evalList_hasConst o σ conj ps h, evalWith_constP]
  · rw [evalWith_listP, DistPredList.evalList_dropConst]

theorem evalWith_pevalAtom {v : View} {σ : Step} (hv : Agrees v σ) (o : Oracle) (s : SlotId)
    (t : SlotTest) : (pevalAtom v s t).evalWith o σ = ofBool (t.holds (σ s)) := by
  unfold pevalAtom
  split
  · rename_i st h
    rw [evalWith_constP, hv s st h]
  · simp only [DistPred.evalWith]

mutual
/-- **The residual is never wrong.** On any step that agrees with the vat's slice, the residual has
the verdict of the predicate, under every oracle. -/
theorem DistPred.evalWith_pevalVat {v : View} {σ : Step} (hv : Agrees v σ) (o : Oracle) :
    ∀ p : DistPred, (p.pevalVat v).evalWith o σ = p.evalWith o σ
  | .atom s t => by
    simp only [DistPred.pevalVat, evalWith_pevalAtom hv, DistPred.evalWith]
  | .witnessed _ => by simp only [DistPred.pevalVat]
  | .not p => by
    simp only [DistPred.pevalVat, evalWith_notR, DistPred.evalWith,
      DistPred.evalWith_pevalVat hv o p]
  | .all ps => by
    simp only [DistPred.pevalVat, evalWith_foldR, DistPred.evalWith,
      DistPredList.evalList_pevalVat hv o true ps]
  | .any ps => by
    simp only [DistPred.pevalVat, evalWith_foldR, DistPred.evalWith,
      DistPredList.evalList_pevalVat hv o false ps]
theorem DistPredList.evalList_pevalVat {v : View} {σ : Step} (hv : Agrees v σ) (o : Oracle)
    (conj : Bool) : ∀ ps : DistPredList, (ps.pevalVat v).evalList o σ conj = ps.evalList o σ conj
  | .nil => by simp only [DistPredList.pevalVat]
  | .cons p ps => by
    simp only [DistPredList.pevalVat, DistPredList.evalList, DistPred.evalWith_pevalVat hv o p,
      DistPredList.evalList_pevalVat hv o conj ps]
end

theorem mentions_constP (s : SlotId) (b : Bool) : (constP b).mentions s = false := by
  cases b <;> rfl

theorem mentions_pevalAtom {v : View} {s : SlotId} (hs : (v s).isSome = true) (s' : SlotId)
    (t : SlotTest) : (pevalAtom v s' t).mentions s = false := by
  unfold pevalAtom
  split
  · exact mentions_constP s _
  · rename_i h
    simp only [DistPred.mentions, beq_eq_false_iff_ne, ne_eq]
    intro he
    subst he
    simp [h] at hs

theorem mentions_notR (s : SlotId) (p : DistPred) (h : p.mentions s = false) :
    (notR p).mentions s = false := by
  unfold notR
  split
  · exact mentions_constP s _
  · simpa only [DistPred.mentions] using h

theorem DistPredList.mentions_dropConst (s : SlotId) (b : Bool) :
    ∀ ps : DistPredList, ps.mentions s = false → (ps.dropConst b).mentions s = false
  | .nil, _ => by rfl
  | .cons p ps, h => by
    simp only [DistPredList.mentions, Bool.or_eq_false_iff] at h
    simp only [DistPredList.dropConst]
    split
    · exact DistPredList.mentions_dropConst s b ps h.2
    · simp only [DistPredList.mentions, h.1, DistPredList.mentions_dropConst s b ps h.2,
        Bool.or_self]

theorem mentions_foldR (s : SlotId) (conj : Bool) (ps : DistPredList)
    (h : ps.mentions s = false) : (foldR conj ps).mentions s = false := by
  unfold foldR
  split
  · exact mentions_constP s _
  · cases conj <;>
      simpa only [listP, DistPred.mentions] using DistPredList.mentions_dropConst s _ ps h

mutual
/-- **The residual names no slot the vat holds.** Whoever receives it learns no slot number of the
vat's slice, and cannot be made to read one. -/
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
      DistPred.pevalVat_hides_known_slots hs p, DistPredList.pevalVat_hides_known_slots hs ps,
      Bool.or_self]
end

mutual
/-- A predicate's verdict depends on the step only through the slots it reads. -/
theorem DistPred.evalWith_congr (o : Oracle) {σ σ' : Step} :
    ∀ p : DistPred, (∀ s, p.mentions s = true → σ s = σ' s) → p.evalWith o σ = p.evalWith o σ'
  | .atom s t, h => by
    simp only [DistPred.evalWith, h s (by simp [DistPred.mentions])]
  | .witnessed _, _ => by simp only [DistPred.evalWith]
  | .not p, h => by
    simp only [DistPred.evalWith,
      DistPred.evalWith_congr o p (fun s hs => h s (by simpa only [DistPred.mentions] using hs))]
  | .all ps, h => by
    simp only [DistPred.evalWith, DistPredList.evalList_congr o true ps
      (fun s hs => h s (by simpa only [DistPred.mentions] using hs))]
  | .any ps, h => by
    simp only [DistPred.evalWith, DistPredList.evalList_congr o false ps
      (fun s hs => h s (by simpa only [DistPred.mentions] using hs))]
theorem DistPredList.evalList_congr (o : Oracle) {σ σ' : Step} (conj : Bool) :
    ∀ ps : DistPredList, (∀ s, ps.mentions s = true → σ s = σ' s) →
      ps.evalList o σ conj = ps.evalList o σ' conj
  | .nil, _ => by simp only [DistPredList.evalList]
  | .cons p ps, h => by
    simp only [DistPredList.evalList,
      DistPred.evalWith_congr o p (fun s hs => h s (by simp [DistPredList.mentions, hs])),
      DistPredList.evalList_congr o conj ps (fun s hs => h s (by simp [DistPredList.mentions, hs]))]
end

/-- **Cross-vat evaluation.** The verdict of `p` on the vat's slice joined with the rest of the
step is the verdict of the residual on the rest alone. The second party evaluates what it was sent
on what it holds; whatever its state says at the first vat's slots is never read. -/
theorem eval_subst_eq_eval_pevalVat (o : Oracle) (v : View) (rest : Step) (p : DistPred) :
    p.evalWith o (overlay v rest) = (p.pevalVat v).evalWith o rest := by
  rw [← DistPred.evalWith_pevalVat (agrees_overlay v rest) o p]
  apply DistPred.evalWith_congr
  intro s hs
  cases hv : v s with
  | none => simp [overlay, hv]
  | some st =>
    rw [DistPred.pevalVat_hides_known_slots (by simp [hv]) p] at hs
    cases hs

/-! ## 6. Additively homomorphic commitments over `ℤ/2²⁵⁶` -/

/-- Two generators of the ring `ℤ/2²⁵⁶`, the first a unit with its inverse. -/
structure CommitKey where
  g : BitVec 256
  h : BitVec 256
  gInv : BitVec 256
  unit : gInv * g = 1#256

/-- The commitment to `value` under `blind`. -/
def commitVal (key : CommitKey) (value blind : BitVec 256) : BitVec 256 :=
  key.g * value + key.h * blind

/-- What the committer keeps: the value and its blinding. -/
structure Opening where
  value : BitVec 256
  blind : BitVec 256

/-- What the verifier sees. -/
def Opening.commit (key : CommitKey) (o : Opening) : BitVec 256 := commitVal key o.value o.blind

/-- The sum of a list in the ring. -/
def bvSum : List (BitVec 256) → BitVec 256
  | [] => 0#256
  | x :: xs => x + bvSum xs

/-- The sum of a list over the naturals. -/
def natSum : List (BitVec 256) → Nat
  | [] => 0
  | x :: xs => x.toNat + natSum xs

/-- The hidden value total of a list of openings. -/
def valueSum (os : List Opening) : BitVec 256 := bvSum (os.map (·.value))

/-- The blinding total. -/
def blindSum (os : List Opening) : BitVec 256 := bvSum (os.map (·.blind))

theorem commitVal_add (key : CommitKey) (v₁ b₁ v₂ b₂ : BitVec 256) :
    commitVal key (v₁ + v₂) (b₁ + b₂) = commitVal key v₁ b₁ + commitVal key v₂ b₂ := by
  simp only [commitVal, BitVec.mul_add]
  ac_rfl

/-- **The commitment is additive**: the sum of the commitments is the commitment of the sums. -/
theorem commitSum_collapse (key : CommitKey) (os : List Opening) :
    bvSum (os.map (Opening.commit key)) = commitVal key (valueSum os) (blindSum os) := by
  induction os with
  | nil => simp [bvSum, commitVal, valueSum, blindSum]
  | cons o os ih =>
    simp only [valueSum, blindSum] at ih
    simp only [List.map_cons, bvSum, ih, Opening.commit, commitVal_add, valueSum, blindSum]

/-- At one blinding, the commitment determines the value: `g` is a unit. -/
theorem commitVal_value_inj (key : CommitKey) {a a' b : BitVec 256}
    (h : commitVal key a b = commitVal key a' b) : a = a' := by
  have h1 : key.g * a = key.g * a' := by
    have h0 := congrArg (· - key.h * b) h
    simpa only [commitVal, BitVec.add_sub_cancel] using h0
  have h2 := congrArg (key.gInv * ·) h1
  simpa only [← BitVec.mul_assoc, key.unit, BitVec.one_mul] using h2

/-- The verifier's check: the two commitment totals are equal. It reads nothing else. -/
def homCheck (ins outs : List (BitVec 256)) : Bool := decide (bvSum ins = bvSum outs)

theorem homCheck_iff (ins outs : List (BitVec 256)) :
    homCheck ins outs = true ↔ bvSum ins = bvSum outs := by
  simp only [homCheck, decide_eq_true_eq]

/-- **Conservation is checked on commitments alone.** The check on the commitments of `ins` and
`outs` holds exactly when the commitment of the input totals is the commitment of the output
totals. -/
theorem private_conservation_checks_homomorphically (key : CommitKey) (ins outs : List Opening) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = true ↔
      commitVal key (valueSum ins) (blindSum ins) = commitVal key (valueSum outs) (blindSum outs) := by
  simp only [homCheck, decide_eq_true_eq, commitSum_collapse]

/-- **The check is value conservation.** When the blinding totals agree, the commitments balance
exactly when the hidden value totals do. No value and no blinding is read by the check. -/
theorem private_conservation_iff_value_sum (key : CommitKey) (ins outs : List Opening)
    (hblind : blindSum ins = blindSum outs) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = true ↔
      valueSum ins = valueSum outs := by
  rw [private_conservation_checks_homomorphically]
  constructor
  · intro h
    rw [hblind] at h
    exact commitVal_value_inj key h
  · intro h
    rw [h, hblind]

theorem bvSum_toNat : ∀ xs : List (BitVec 256), (bvSum xs).toNat = natSum xs % 2 ^ 256
  | [] => by simp [bvSum, natSum]
  | x :: xs => by
    simp only [bvSum, natSum, BitVec.toNat_add, bvSum_toNat xs, Nat.add_mod_mod]

/-- `n` values of `bits` bits sum to at most `n · 2^bits`. -/
theorem natSum_le_of_bits (bits : Nat) : ∀ xs : List (BitVec 256),
    (∀ x, x ∈ xs → x.toNat < 2 ^ bits) → natSum xs ≤ xs.length * 2 ^ bits
  | [], _ => by simp [natSum]
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := natSum_le_of_bits bits xs (fun y hy => h y (by simp [hy]))
    simp only [natSum, List.length_cons, Nat.add_one_mul]
    omega

/-- **Conservation over the naturals.** When neither total wraps, the check is equality of the
value totals as numbers. Without the bound it is equality modulo `2²⁵⁶`, and an output of
`2²⁵⁶ - 1` passes for a debt of one: the bound is what a range proof is for. -/
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

/-- An inflating transfer is refused without opening anything. -/
theorem inflation_refused (key : CommitKey) (ins outs : List Opening)
    (hblind : blindSum ins = blindSum outs) (hne : valueSum ins ≠ valueSum outs) :
    homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) = false := by
  cases hc : homCheck (ins.map (Opening.commit key)) (outs.map (Opening.commit key)) with
  | false => rfl
  | true => exact absurd ((private_conservation_iff_value_sum key ins outs hblind).1 hc) hne

/-! ## 7. The graded ladder: commitments, witnessed ranges, a residual predicate -/

/-- The claim that the value committed in `commitment` is below `2^bits`. -/
structure RangeClaim where
  commitment : BitVec 256
  bits : Nat

/-- The bytes of a range claim: the commitment in 32 bytes and the width, each length-prefixed. -/
def RangeClaim.encode (c : RangeClaim) : List UInt8 :=
  encodeFields [be 32 c.commitment.toNat, leb128 c.bits]

theorem RangeClaim.encode_injective {a b : RangeClaim} (h : a.encode = b.encode) : a = b := by
  obtain ⟨ca, na⟩ := a
  obtain ⟨cb, nb⟩ := b
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hc : ca = cb :=
    BitVec.eq_of_toNat_eq (be_injective (h256 ▸ ca.isLt) (h256 ▸ cb.isLt) hf.1)
  have hn : na = nb :=
    (leb128_prefix_inj (r₁ := []) (r₂ := []) (by rw [List.append_nil, List.append_nil, hf.2])).1
  rw [hc, hn]

/-- Customization string of the range-claim identifier. -/
def rangeCustomization : List UInt8 := "OBEND.POLIS.RANGE/v1".toUTF8.data.toList

/-- The identifier a range claim is discharged under: the digest of the claim. -/
def rangeVk (c : RangeClaim) : VkId := ⟨cshake32ByteArray rangeCustomization c.encode⟩

/-- One identifier names one claim, or the two claims collide. -/
theorem rangeVk_binds {a b : RangeClaim} (h : rangeVk a = rangeVk b) :
    a = b ∨ CollisionAmong (cshake256Bytes rangeCustomization)
      (fun x => x = a.encode ∨ x = b.encode) := by
  rcases cshake32_binds rangeCustomization (congrArg VkId.id h) with hp | hc
  · exact .inl (RangeClaim.encode_injective hp)
  · exact .inr hc

/-- A private predicate: commitments that must balance, range claims on committed values, and a
predicate over the disclosed slots. -/
structure PrivPred where
  ins : List (BitVec 256)
  outs : List (BitVec 256)
  ranges : List RangeClaim
  clear : DistPred

/-- The range claims as `witnessed` leaves. -/
def rangeLeaves : List RangeClaim → DistPredList
  | [] => .nil
  | c :: cs => .cons (.witnessed (rangeVk c)) (rangeLeaves cs)

/-- The predicate part: the disclosed predicate and every range leaf. -/
def PrivPred.guard (p : PrivPred) : DistPred := .all (.cons p.clear (rangeLeaves p.ranges))

/-- The verifier's whole check. -/
def PrivPred.check (o : Oracle) (σ : Step) (p : PrivPred) : Bool :=
  homCheck p.ins p.outs && (p.guard.evalWith o σ).accepts

theorem accepts_evalList_rangeLeaves (o : Oracle) (σ : Step) : ∀ cs : List RangeClaim,
    ((rangeLeaves cs).evalList o σ true).accepts = true ↔ ∀ c, c ∈ cs → o (rangeVk c) = .true3
  | [] => by simp [rangeLeaves, DistPredList.evalList, ofBool, KleenePred3.accepts]
  | c :: cs => by
    simp only [rangeLeaves, DistPredList.evalList, combine3_true, DistPred.evalWith,
      KleenePred3.accepts_and3, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [accepts_evalList_rangeLeaves o σ cs, accepts_iff_true3]

/-- **The check is the three tiers and nothing else.** -/
theorem PrivPred.check_iff (o : Oracle) (σ : Step) (p : PrivPred) :
    p.check o σ = true ↔
      bvSum p.ins = bvSum p.outs ∧ (∀ c, c ∈ p.ranges → o (rangeVk c) = .true3) ∧
        (p.clear.evalWith o σ).accepts = true := by
  simp only [PrivPred.check, PrivPred.guard, homCheck, Bool.and_eq_true, decide_eq_true_eq,
    DistPred.evalWith, DistPredList.evalList, combine3_true, KleenePred3.accepts_and3,
    accepts_evalList_rangeLeaves]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h3, h2⟩
    exact ⟨h1, h2, h3⟩

/-- A range claim is never satisfied by the vat alone. -/
theorem privPred_ranges_refused_firstParty (σ : Step) (p : PrivPred) (c : RangeClaim)
    (hc : c ∈ p.ranges) : p.check noOracle σ = false := by
  cases h : p.check noOracle σ with
  | false => rfl
  | true =>
    have h3 := ((PrivPred.check_iff noOracle σ p).1 h).2.1 c hc
    simp [noOracle] at h3

/-- The range verifier behind the oracle is sound for these openings: a discharged claim on the
commitment of an opening bounds that opening's value. -/
def RangeSound (key : CommitKey) (o : Oracle) (os : List Opening) (bits : Nat) : Prop :=
  ∀ op, op ∈ os → o (rangeVk ⟨op.commit key, bits⟩) = .true3 → op.value.toNat < 2 ^ bits

/-- The private predicate over the openings `ins` and `outs`: their commitments, a `bits`-bit range
claim on each, and `clear`. -/
def transferPred (key : CommitKey) (ins outs : List Opening) (bits : Nat) (clear : DistPred) :
    PrivPred :=
  ⟨ins.map (Opening.commit key), outs.map (Opening.commit key),
    (ins ++ outs).map (fun op => ⟨op.commit key, bits⟩), clear⟩

/-- **Private conservation, end to end.** If the verifier's check on a transfer passes, the
blinding totals agree, the range verifier is sound, and the widths leave no room to wrap, then the
hidden inputs and outputs have the same total as natural numbers and the disclosed predicate holds.
The verifier read commitments, discharge verdicts and disclosed slots. -/
theorem privPred_conservation_sound (key : CommitKey) (o : Oracle) (σ : Step)
    (ins outs : List Opening) (bits : Nat) (clear : DistPred)
    (hcheck : (transferPred key ins outs bits clear).check o σ = true)
    (hblind : blindSum ins = blindSum outs)
    (hrange : RangeSound key o (ins ++ outs) bits)
    (hin : ins.length * 2 ^ bits < 2 ^ 256) (hout : outs.length * 2 ^ bits < 2 ^ 256) :
    natSum (ins.map (·.value)) = natSum (outs.map (·.value)) ∧
      (clear.evalWith o σ).accepts = true := by
  obtain ⟨hsum, hranges, hclear⟩ := (PrivPred.check_iff o σ _).1 hcheck
  have hbound : ∀ op, op ∈ ins ++ outs → op.value.toNat < 2 ^ bits := fun op hop =>
    hrange op hop (hranges ⟨op.commit key, bits⟩ (List.mem_map.2 ⟨op, hop, rfl⟩))
  have hin' : natSum (ins.map (·.value)) < 2 ^ 256 := by
    have := natSum_le_of_bits bits (ins.map (·.value)) (by
      intro x hx
      obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hx
      exact hbound op (List.mem_append_left _ hop))
    simp only [List.length_map] at this
    omega
  have hout' : natSum (outs.map (·.value)) < 2 ^ 256 := by
    have := natSum_le_of_bits bits (outs.map (·.value)) (by
      intro x hx
      obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hx
      exact hbound op (List.mem_append_right _ hop))
    simp only [List.length_map] at this
    omega
  refine ⟨(private_conservation_nat_sum key ins outs hblind hin' hout').1 ?_, hclear⟩
  simpa only [homCheck, decide_eq_true_eq, transferPred] using hsum

/-- A key: `3` and its inverse modulo `2²⁵⁶`, with `5` for the blinding generator. -/
def demoKey : CommitKey :=
  ⟨3#256, 5#256, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB#256, by decide⟩

/-- The premises of `privPred_conservation_sound` are met together: a transfer of `5` under
blinding `7`, with eight-bit ranges, passes under an oracle whose verdicts are sound. -/
theorem privPred_conservation_inhabited :
    ∃ (key : CommitKey) (o : Oracle) (σ : Step) (ins outs : List Opening) (bits : Nat),
      (transferPred key ins outs bits .tt).check o σ = true ∧ blindSum ins = blindSum outs ∧
        RangeSound key o (ins ++ outs) bits ∧ 0 < ins.length ∧
        ins.length * 2 ^ bits < 2 ^ 256 ∧ outs.length * 2 ^ bits < 2 ^ 256 := by
  refine ⟨demoKey, fun _ => .true3, fun _ => ⟨none, none⟩, [⟨5#256, 7#256⟩], [⟨5#256, 7#256⟩], 8,
    ?_, rfl, ?_, by decide, by decide, by decide⟩
  · rw [PrivPred.check_iff]
    refine ⟨rfl, fun _ _ => rfl, ?_⟩
    simp [transferPred, DistPred.tt, DistPred.evalWith, DistPredList.evalList, ofBool,
      KleenePred3.accepts]
  · intro op hop _
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      or_self] at hop
    subst hop
    decide

/-! ## 8. Sealing: cSHAKE256 in counter mode with a cSHAKE256 tag -/

/-- Byte-wise exclusive or of a message with a pad; past the end of the pad the message is kept. -/
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

/-- Customization string of the keystream. -/
def streamCustomization : List UInt8 := "OBEND.POLIS.SEAL.STREAM/v1".toUTF8.data.toList

/-- Customization string of the authentication tag. -/
def macCustomization : List UInt8 := "OBEND.POLIS.SEAL.MAC/v1".toUTF8.data.toList

/-- `blocks` 32-byte keystream blocks from counter `i`. -/
def keystream (key nonce : ByteArray) : Nat → Nat → List UInt8
  | 0, _ => []
  | blocks + 1, i =>
    cshake256Bytes streamCustomization
        (encodeFields [key.data.toList, nonce.data.toList, leb128 i]) ++
      keystream key nonce blocks (i + 1)

/-- The pad for a message of `len` bytes: `⌈len / 32⌉` blocks of 32 bytes, so it covers the message. -/
def keystreamFor (key nonce : ByteArray) (len : Nat) : List UInt8 :=
  keystream key nonce ((len + 31) / 32) 0

/-- What the tag is the digest of. -/
def macPreimage (key nonce : ByteArray) (body : List UInt8) : List UInt8 :=
  encodeFields [key.data.toList, nonce.data.toList, body]

/-- The 32-byte tag over the key, the nonce and the ciphertext. -/
def macTag (key nonce : ByteArray) (body : List UInt8) : ByteArray :=
  cshake32ByteArray macCustomization (macPreimage key nonce body)

/-- **The tag binds key, nonce and ciphertext**, or two named preimages collide. -/
theorem macTag_binds {k k' n n' : ByteArray} {b b' : List UInt8}
    (h : macTag k n b = macTag k' n' b') :
    (k = k' ∧ n = n' ∧ b = b') ∨ CollisionAmong (cshake256Bytes macCustomization)
      (fun x => x = macPreimage k n b ∨ x = macPreimage k' n' b') := by
  rcases cshake32_binds macCustomization h with hp | hc
  · have hf := encodeFields_injective _ _ hp
    simp only [List.cons.injEq, and_true] at hf
    exact .inl ⟨byteArray_eq_of_toList_eq hf.1, byteArray_eq_of_toList_eq hf.2.1, hf.2.2⟩
  · exact .inr hc

/-- A sealed message. -/
structure Sealed where
  nonce : ByteArray
  body : List UInt8
  tag : ByteArray
  deriving DecidableEq

/-- Seal `msg` under `key` and `nonce`: encrypt, then tag the ciphertext. -/
def aeadSeal (key nonce : ByteArray) (msg : List UInt8) : Sealed :=
  ⟨nonce, xorWith msg (keystreamFor key nonce msg.length),
    macTag key nonce (xorWith msg (keystreamFor key nonce msg.length))⟩

/-- Open a sealed message: check the tag, then decrypt. A wrong tag yields nothing. -/
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
  · rename_i ht
    exact ⟨ht, (Option.some.inj h).symm⟩
  · cases h

/-- **Another key does not open it**: opening a sealed message under `key'` succeeds only for
`key' = key`, or exhibits a collision of the tag hash. -/
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

/-- **A changed ciphertext does not open**: under the genuine tag, a different nonce or body opens
only at a collision of the tag hash. -/
theorem aeadOpen_tampered {key nonce nonce' : ByteArray} {msg body' m : List UInt8}
    (h : aeadOpen key ⟨nonce', body', (aeadSeal key nonce msg).tag⟩ = some m) :
    (nonce' = nonce ∧ body' = (aeadSeal key nonce msg).body ∧ m = msg) ∨
      CollisionAmong (cshake256Bytes macCustomization)
        (fun x => x = macPreimage key nonce (aeadSeal key nonce msg).body ∨
          x = macPreimage key nonce' body') := by
  obtain ⟨ht, hm⟩ := aeadOpen_eq_some h
  rcases macTag_binds (k := key) (k' := key) (n := nonce) (n' := nonce')
      (b := (aeadSeal key nonce msg).body) (b' := body') ht with he | hc
  · obtain ⟨_, hn, hb⟩ := he
    subst hn
    subst hb
    refine .inl ⟨rfl, rfl, ?_⟩
    have ho := aeadOpen_aeadSeal key nonce msg
    simp only [aeadSeal] at h ho
    rw [ho] at h
    exact (Option.some.inj h).symm
  · exact .inr hc

/-! ## 9. Third-party caveats and their discharge -/

/-- A caveat of a discharge: a predicate the third party imposes, or the binding to a parent. -/
inductive DCaveat where
  | firstParty (pred : DistPred)
  | bindToParent (binding : ByteArray)
  deriving DecidableEq

/-- The bytes a caveat contributes to the chain. -/
def DCaveat.body : DCaveat → List UInt8
  | .firstParty p => 0 :: p.encode
  | .bindToParent b => 1 :: b.data.toList

/-- A discharge: when it was made, its nonce, its caveats, and the chain tail over all of them. -/
structure Discharge where
  createdAt : Nat
  nonce : ByteArray
  caveats : List DCaveat
  tail : ByteArray

/-- Customization string of the discharge chain. -/
def chainCustomization : List UInt8 := "OBEND.POLIS.DISCHARGE.CHAIN/v1".toUTF8.data.toList

/-- Customization string of the binding hash. -/
def bindCustomization : List UInt8 := "OBEND.POLIS.DISCHARGE.BIND/v1".toUTF8.data.toList

/-- The chain's first tail: keyed by the discharge key over the nonce and the timestamp. -/
def chainInit (r nonce : ByteArray) (createdAt : Nat) : ByteArray :=
  cshake32ByteArray chainCustomization
    (encodeFields [[0], r.data.toList, nonce.data.toList, leb128 createdAt])

/-- One more caveat: the next tail is keyed by the last. -/
def chainStep (tail : ByteArray) (c : DCaveat) : ByteArray :=
  cshake32ByteArray chainCustomization (encodeFields [[1], tail.data.toList, c.body])

/-- The tail an honest chain over these caveats ends in. -/
def replayTail (r nonce : ByteArray) (createdAt : Nat) (cs : List DCaveat) : ByteArray :=
  cs.foldl chainStep (chainInit r nonce createdAt)

/-- The 32-byte digest of a parent's tail that a bound discharge carries. -/
def bindingHash (parentTail : ByteArray) : ByteArray :=
  cshake32ByteArray bindCustomization parentTail.data.toList

/-- One binding digest names one parent tail, or the two tails collide. -/
theorem bindingHash_binds {a b : ByteArray} (h : bindingHash a = bindingHash b) :
    a = b ∨ CollisionAmong (cshake256Bytes bindCustomization)
      (fun x => x = a.data.toList ∨ x = b.data.toList) := by
  rcases cshake32_binds bindCustomization h with hp | hc
  · exact .inl (byteArray_eq_of_toList_eq hp)
  · exact .inr hc

/-- A discharge is fresh: it carries a timestamp, not from the future, at most `maxAge` old. -/
def fresh (createdAt now maxAge : Nat) : Bool :=
  decide (createdAt ≠ 0) && decide (createdAt ≤ now) && decide (now - createdAt ≤ maxAge)

theorem fresh_iff (createdAt now maxAge : Nat) :
    fresh createdAt now maxAge = true ↔
      createdAt ≠ 0 ∧ createdAt ≤ now ∧ now - createdAt ≤ maxAge := by
  simp [fresh, and_assoc]

/-- The stored tail is the honest chain under `r`. -/
def chainValid (d : Discharge) (r : ByteArray) : Bool :=
  decide (d.tail = replayTail r d.nonce d.createdAt d.caveats)

/-- The discharge carries the binding to this parent. -/
def boundTo (d : Discharge) (parentTail : ByteArray) : Bool :=
  d.caveats.contains (.bindToParent (bindingHash parentTail))

theorem boundTo_iff (d : Discharge) (parentTail : ByteArray) :
    boundTo d parentTail = true ↔ DCaveat.bindToParent (bindingHash parentTail) ∈ d.caveats := by
  simp [boundTo]

/-- A caveat of a discharge holds on a step. The third party's predicates are decided by the
verifier alone, with no oracle. -/
def DCaveat.holds (σ : Step) : DCaveat → Bool
  | .firstParty p => (evalFirstParty σ p).accepts
  | .bindToParent _ => true

/-- Every caveat of the discharge holds. -/
def caveatsHold (σ : Step) (d : Discharge) : Bool := d.caveats.all (DCaveat.holds σ)

theorem caveatsHold_iff (σ : Step) (d : Discharge) :
    caveatsHold σ d = true ↔
      ∀ p, DCaveat.firstParty p ∈ d.caveats → (evalFirstParty σ p).accepts = true := by
  simp only [caveatsHold, List.all_eq_true]
  constructor
  · intro h p hp
    exact h _ hp
  · intro h c hc
    cases c with
    | firstParty p => exact h p hc
    | bindToParent _ => rfl

/-- A third-party caveat on a parent credential: where the third party is, the ticket only it can
open, and the verifier id only the holder of the parent's tail can open. Both carry the discharge
key. -/
structure ThirdPartyCaveat where
  location : ByteArray
  ticket : Sealed
  vid : Sealed

/-- Add a third-party caveat to a credential whose tail is `parentTail`: seal the discharge key `r`
with the identifier of the predicate to the third party's key, and `r` alone under the tail. -/
def issueCaveat (location k3p ticketNonce vidNonce parentTail r : ByteArray) (pred : VkId) :
    ThirdPartyCaveat :=
  ⟨location, aeadSeal k3p ticketNonce (r.data.toList ++ pred.id.data.toList),
    aeadSeal parentTail vidNonce r.data.toList⟩

/-- The third party opens its ticket: the discharge key and the predicate it is asked to vouch for. -/
def openTicket (k3p : ByteArray) (cav : ThirdPartyCaveat) : Option (ByteArray × VkId) :=
  (aeadOpen k3p cav.ticket).map fun m => (⟨(m.take 32).toArray⟩, ⟨⟨(m.drop 32).toArray⟩⟩)

/-- The third party makes a discharge under `r`, with its own caveats. -/
def createDischarge (r : ByteArray) (createdAt : Nat) (nonce : ByteArray) (preds : List DistPred) :
    Discharge :=
  ⟨createdAt, nonce, preds.map .firstParty,
    replayTail r nonce createdAt (preds.map .firstParty)⟩

/-- The holder binds a discharge to the parent it will be shown with, extending the chain. -/
def bindDischarge (d : Discharge) (parentTail : ByteArray) : Discharge :=
  { d with
    caveats := d.caveats ++ [.bindToParent (bindingHash parentTail)]
    tail := chainStep d.tail (.bindToParent (bindingHash parentTail)) }

/-- The third party's service: open the ticket, decide the predicate it names, and discharge. -/
def serveTicket (k3p : ByteArray) (cav : ThirdPartyCaveat) (vouches : VkId → Bool)
    (createdAt : Nat) (nonce : ByteArray) (preds : List DistPred) : Option Discharge :=
  match openTicket k3p cav with
  | some (r, pred) => if vouches pred then some (createDischarge r createdAt nonce preds) else none
  | none => none

/-- The verifier recovers the discharge key from the verifier id, under the parent's tail. -/
def recoverKey (cav : ThirdPartyCaveat) (parentTail : ByteArray) : Option ByteArray :=
  (aeadOpen parentTail cav.vid).map fun m => ⟨m.toArray⟩

/-- **The verifier's gate.** Recover the key under the parent's tail; then the discharge must be
fresh, its chain must replay under that key, it must be bound to this parent, and its caveats must
hold. -/
def verifyDischarge (cav : ThirdPartyCaveat) (d : Discharge) (parentTail : ByteArray) (σ : Step)
    (now maxAge : Nat) : Bool :=
  match recoverKey cav parentTail with
  | none => false
  | some r =>
    fresh d.createdAt now maxAge && chainValid d r && boundTo d parentTail && caveatsHold σ d

/-- **Exactly the accepted discharges.** -/
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
    · rintro ⟨⟨⟨hf, hc⟩, hb⟩, hp⟩
      exact ⟨r, rfl, hf, hc, hb, hp⟩
    · rintro ⟨r', hr', hf, hc, hb, hp⟩
      subst hr'
      exact ⟨⟨⟨hf, hc⟩, hb⟩, hp⟩

theorem byteArray_toList_toArray (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  cases b
  simp

/-- The third party recovers exactly what was sealed to it. -/
theorem openTicket_issueCaveat (location k3p n₁ n₂ parentTail r : ByteArray) (pred : VkId)
    (hr : r.size = 32) :
    openTicket k3p (issueCaveat location k3p n₁ n₂ parentTail r pred) = some (r, pred) := by
  have hlen : r.data.toList.length = 32 := by
    cases r
    simpa [ByteArray.size] using hr
  obtain ⟨pid⟩ := pred
  simp only [openTicket, issueCaveat, aeadOpen_aeadSeal, Option.map_some, List.take_left' hlen,
    List.drop_left' hlen, byteArray_toList_toArray]

/-- **The honest round trip.** A caveat issued against a parent, served by a third party that
vouches for the named predicate, bound by the holder to that parent and shown while fresh, is
accepted whenever the third party's own caveats hold. -/
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

/-- **A stale discharge is refused**: no timestamp, a timestamp from the future, or one older than
`maxAge`. A captured discharge cannot be replayed after its window. -/
theorem staleDischarge_refused (cav : ThirdPartyCaveat) (d : Discharge) (parentTail : ByteArray)
    (σ : Step) (now maxAge : Nat)
    (hstale : d.createdAt = 0 ∨ now < d.createdAt ∨ maxAge < now - d.createdAt) :
    verifyDischarge cav d parentTail σ now maxAge = false := by
  cases hv : verifyDischarge cav d parentTail σ now maxAge with
  | false => rfl
  | true =>
    obtain ⟨_, _, hf, _⟩ := (verifyDischarge_iff cav d parentTail σ now maxAge).1 hv
    omega

/-- **A discharge is good for one parent.** If every binding a discharge carries is to the parent
tail `tailA` and it is accepted against `tailB`, then it carries a binding and the two tails are
the same, or the binding hash collides on them. A discharge with no binding is never accepted, and
one moved to another credential is refused unless the hash is broken at those two tails. -/
theorem unbound_or_wrong_parent_refused (cav : ThirdPartyCaveat) (d : Discharge)
    (tailA tailB : ByteArray) (σ : Step) (now maxAge : Nat)
    (hbind : ∀ b, DCaveat.bindToParent b ∈ d.caveats → b = bindingHash tailA)
    (hv : verifyDischarge cav d tailB σ now maxAge = true) :
    (∃ b, DCaveat.bindToParent b ∈ d.caveats) ∧
      (tailA = tailB ∨ CollisionAmong (cshake256Bytes bindCustomization)
        (fun x => x = tailA.data.toList ∨ x = tailB.data.toList)) := by
  obtain ⟨_, _, _, _, hb, _⟩ := (verifyDischarge_iff cav d tailB σ now maxAge).1 hv
  refine ⟨⟨_, hb⟩, ?_⟩
  rcases bindingHash_binds (hbind _ hb) with he | hc
  · exact .inl he.symm
  · refine .inr (CollisionAmong.mono (fun x hx => ?_) hc)
    rcases hx with hx | hx
    · exact .inr hx
    · exact .inl hx

end Obend.Polis.PrivatePredicate
end
