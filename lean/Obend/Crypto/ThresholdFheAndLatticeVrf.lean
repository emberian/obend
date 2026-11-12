module
/-
# Obend.Crypto.ThresholdFheAndLatticeVrf — tagged threshold decryption, packed-bit openings, lattice VRF

Three organs over the `DarkBazaar` RLWE carriers, and one multi-turn machine that runs them together.

1. **Tagged threshold decryption** (after Tulva, ePrint 2026/2485, Fig. 3). Shamir shares over a
   Vandermonde matrix; a partial decryption is `s_k · c₁ + e_k mod q` carrying the tag
   `H(domain ‖ context ‖ ciphertext)` (the paper's Remark 6: pseudorandom, context-dependent tag); the
   public combiner takes integral interpolation coefficients `λ_k` with `Σ λ_k x_k^j ≡ ξ·[j = 0]`
   (the `ξ`-cleared row of `V_T⁻¹`) and decodes `ξ·c₀ + Σ λ_k pd_k`.
   `tulvaCombine_recovers_plaintext` is correctness under the worst-case bound
   `ξ·‖e_ct‖ + Σ|λ_k|·‖e_k‖ < ⌊q/(2t)⌋`. What is not modelled: the gadget key switch
   `c₀ := A·G⁻¹(ĉ₀ ‖ t)`, bit dropping, and the paper's `ξ`-coprime linear decryption (here the
   plaintext carries the slack: `ξ·m` must fit the signed range, and the combiner divides by `ξ`).
   The leakage side is stated by counting, for uniform flooding on `[-S, S]`: an unsmudged decryption
   is a threshold oracle on the key-dependent noise (`tulva_unsmudged_boundary_oracle_leaks`), while
   all but `|shift|` of the `2S+1` masks couple two hypotheses whose phases differ by `shift`
   (`smudgeUncoupled_length_le`, `tulvaShare_explained_by_other_key`), which under `SmudgeSafe` is a
   `2^-secBits` fraction (`tulva_smudge_floods_noise`). This is the interval form of the flooding
   lemma, one query, one coefficient; the paper's Gaussian `√Q` composition is not proved, and the
   machine below charges every released share against a query budget instead.
2. **Packed-bit openings** (after BitZ, ePrint 2026/2141). A witness matrix of cells committed once;
   booleanity `c(1-c) = 0` over `ℤ` plus the binary recomposition `ψ` opened in `ℤ`, in `ℤ_q` and in
   Goldilocks gives the `B`-bit range with no table and the equality of the two ring images
   (`bitz_sameOpening_and_free_range_sound`).
3. **Lattice VRF** (after LaV, Esgin et al. Crypto'23, in the ring-bound form of ePrint 2026/772).
   Verification is over the opened witness: a short `z` with `A·z = t mod q`, the rounded
   `y = ⌊B_x·z⌉_p` for the hash-derived `B_x`, and `v = H(key ‖ input ‖ y)`. Zero knowledge of the
   real proof is out of scope; what is proved is completeness and the uniqueness reduction
   (`lav_unique_output_or_msisBreak`, `lav_T_uniqueness`).
4. **The auction machine**: `auctionRun` over a list of turns, with tag non-replay, the query budget
   and the leader log as accumulated state.
-/
public import Obend.Crypto.FastRing
public import Obend.Crypto.Transcript
public import Obend.Crypto.SameOpening
public import Obend.Crypto.DarkBazaar
import all Obend.Crypto.FastRing
import all Obend.Crypto.Transcript
import all Obend.Crypto.SameOpening
import all Obend.Crypto.DarkBazaar

public section
namespace Obend.Crypto
open Obend.Apps.ZkNtt Obend.Crypto.Fast Obend.Digest.HashBytes Obend.Ledger
set_option autoImplicit false

/-! ## 0. Congruence witnesses, framed integer rows, negacyclic left-linearity -/

private theorem emod_eq_of_sub_eq_mul {a b q c : Int} (h : a - b = q * c) : a % q = b % q := by
  have ha : a = b + q * c := by omega
  rw [ha, Int.add_mul_emod_self_left]

private theorem sub_eq_mul_of_emod_eq {a b q : Int} (h : a % q = b % q) : ∃ c, a - b = q * c := by
  refine ⟨a / q - b / q, ?_⟩
  have ha := Int.emod_def a q
  have hb := Int.emod_def b q
  rw [Int.mul_sub]
  omega

private theorem map_inj_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ l l' : List α, l.map f = l'.map f → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih =>
    intro l' h
    cases l' with
    | nil => simp at h
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf a b h.1, ih l' h.2]

private theorem map_eq_at {α β : Type} {f g : α → β} :
    ∀ {l : List α}, l.map f = l.map g → ∀ a ∈ l, f a = g a := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp ha with hx | hl
    · rw [hx]; exact h.1
    · exact ih h.2 a hl

/-- A counted list of length-prefixed byte fields. -/
def encodeFields (fs : List (List UInt8)) : List UInt8 :=
  leb128 fs.length ++ fs.flatMap encodeListField

private theorem flatMap_fields_inj (xs : List (List UInt8)) :
    ∀ ys : List (List UInt8), xs.length = ys.length →
      xs.flatMap encodeListField = ys.flatMap encodeListField → xs = ys := by
  induction xs with
  | nil => intro ys hlen _; cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    intro ys hlen h
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, htail⟩ := encodeListField_prefix_inj h
      rw [hxy, ih ys hlen' htail]

theorem encodeFields_injective {xs ys : List (List UInt8)}
    (h : encodeFields xs = encodeFields ys) : xs = ys := by
  unfold encodeFields at h
  obtain ⟨hlen, hbody⟩ := leb128_prefix_inj h
  exact flatMap_fields_inj xs ys hlen hbody

theorem encodeSignedIntList_injective {xs ys : List Int}
    (h : encodeSignedIntList xs = encodeSignedIntList ys) : xs = ys :=
  encodeSignedIntBytes_injective (by unfold encodeSignedIntBytes; rw [h])

/-- Rows of signed integers, each row framed, the row count in front. -/
def encodeIntRows (rows : List (List Int)) : List UInt8 :=
  encodeFields (rows.map encodeSignedIntList)

theorem encodeIntRows_injective {xs ys : List (List Int)}
    (h : encodeIntRows xs = encodeIntRows ys) : xs = ys :=
  map_inj_of_inj (fun _ _ => encodeSignedIntList_injective) xs ys (encodeFields_injective h)

/-- The coefficient list of a ring element, as hashed. -/
def polyCoeffs {d : Nat} (a : FastIntPoly d) : List Int := a.coeffs.toList

theorem polyCoeffs_injective {d : Nat} {a b : FastIntPoly d}
    (h : polyCoeffs a = polyCoeffs b) : a = b := by
  cases a with
  | mk ca ha =>
    cases b with
    | mk cb hb =>
      have hc : ca = cb := Array.toList_inj.mp h
      subst hc
      rfl

theorem polyRows_injective {d : Nat} {u v : List (FastIntPoly d)}
    (h : u.map polyCoeffs = v.map polyCoeffs) : u = v :=
  map_inj_of_inj (fun _ _ => polyCoeffs_injective) u v h

/-- Equal digests of two three-field frames: equal fields, or a collision of `H`. -/
theorem hash_frame_binding (H : Hash) {a₁ b₁ c₁ a₂ b₂ c₂ : List UInt8}
    (h : H (encodeFrameList a₁ b₁ c₁) = H (encodeFrameList a₂ b₂ c₂)) :
    (a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂) ∨ Collision H := by
  by_cases hPre : encodeFrameList a₁ b₁ c₁ = encodeFrameList a₂ b₂ c₂
  · exact Or.inl (encodeFrameList_injective hPre)
  · exact Or.inr ⟨_, _, hPre, congrArg ofBE h⟩

private theorem negacyclicSpec_addLeft {d : Nat} (s1 s2 a : IntCycloSpec d) (k : Fin d) :
    negacyclicSpec (fun i => s1 i + s2 i) a k = negacyclicSpec s1 a k + negacyclicSpec s2 a k := by
  unfold negacyclicSpec
  rw [← sumInt_add]
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, Int.add_mul, wrapSign]
  split <;> omega

private theorem negacyclicSpec_scaleLeft {d : Nat} (c : Int) (s a : IntCycloSpec d) (k : Fin d) :
    negacyclicSpec (fun i => c * s i) a k = c * negacyclicSpec s a k := by
  unfold negacyclicSpec
  rw [← sumInt_mul]
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, wrapSign]
  split
  · exact Int.mul_assoc _ _ _
  · rw [Int.mul_assoc, Int.mul_neg]

theorem negacyclicMulFast_add_left {d : Nat} (a b c : FastIntPoly d) (k : Fin d) :
    (negacyclicMulFast (intAdd a b) c).spec k =
      (negacyclicMulFast a c).spec k + (negacyclicMulFast b c).spec k := by
  rw [negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec,
    addFast_eq_spec]
  exact negacyclicSpec_addLeft a.spec b.spec c.spec k

theorem negacyclicMulFast_scale_left {d : Nat} (x : Int) (a c : FastIntPoly d) (k : Fin d) :
    (negacyclicMulFast (intScale x a) c).spec k = x * (negacyclicMulFast a c).spec k := by
  rw [negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec, scaleFast_eq_spec]
  exact negacyclicSpec_scaleLeft x a.spec c.spec k

theorem negacyclicMulFast_zero_left {d : Nat} (c : FastIntPoly d) (k : Fin d) :
    (negacyclicMulFast (zeroVec d) c).spec k = 0 := by
  have hz : (zeroVec d).spec = fun _ => (0 : Int) := Sized.spec_ofFn _
  have h := negacyclicSpec_scaleLeft 0 (fun _ => (0 : Int)) c.spec k
  simp only [Int.zero_mul] at h
  rw [negacyclicMulFast_eq_spec, hz]
  exact h

theorem zeroVec_spec {d : Nat} (k : Fin d) : (zeroVec d).spec k = 0 := by
  have h : (zeroVec d).spec = fun _ => (0 : Int) := Sized.spec_ofFn _
  rw [h]

theorem negacyclicMulFast_sub_left {d : Nat} (a b c : FastIntPoly d) (k : Fin d) :
    (negacyclicMulFast (intSub a b) c).spec k =
      (negacyclicMulFast a c).spec k - (negacyclicMulFast b c).spec k := by
  have h : negacyclicSpec (fun i => a.spec i - b.spec i + b.spec i) c.spec k =
      negacyclicSpec (fun i => a.spec i - b.spec i) c.spec k + negacyclicSpec b.spec c.spec k :=
    negacyclicSpec_addLeft _ _ _ k
  have hb : (fun i => a.spec i - b.spec i + b.spec i) = a.spec := by funext i; omega
  rw [hb] at h
  rw [negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec,
    subFast_eq_spec]
  omega

/-! ## 1. Tagged threshold decryption

### 1a. Shamir shares and the Vandermonde-dual combiner -/

/-- Horner evaluation, constant coefficient first. -/
def hornerInt : List Int → Int → Int
  | [], _ => 0
  | a :: as, x => a + x * hornerInt as x

/-- The share at point `x` of a sharing polynomial with ring coefficients, the secret first. -/
def shamirShare {d : Nat} : List (FastIntPoly d) → Int → FastIntPoly d
  | [], _ => zeroVec d
  | a :: as, x => intAdd a (intScale x (shamirShare as x))

/-- `Σ λ_k · g(x_k)` over a quorum of `(point, coefficient)` pairs. -/
def quorumSum : List (Int × Int) → (Int → Int) → Int
  | [], _ => 0
  | (x, l) :: rest, g => l * g x + quorumSum rest g

/-- The Vandermonde-dual condition `Σ λ_k x_k^j ≡ ξ·[j = 0] (mod q)` for every `j < t`: the
coefficients are the `ξ`-scaled first row of the inverse Vandermonde matrix of the quorum. -/
def checkQuorumCoeffs (q t : Nat) (slack : Int) (quorum : List (Int × Int)) : Bool :=
  (List.range t).all fun j =>
    decide ((quorumSum quorum (fun x => x ^ j) - (if j = 0 then slack else 0)) % (q : Int) = 0)

theorem quorumSum_zero (quorum : List (Int × Int)) : quorumSum quorum (fun _ => 0) = 0 := by
  induction quorum with
  | nil => rfl
  | cons p rest ih => obtain ⟨x, l⟩ := p; simp [quorumSum, ih]

theorem quorumSum_linear (quorum : List (Int × Int)) (a : Int) (f g : Int → Int) :
    quorumSum quorum (fun x => a * f x + g x) = a * quorumSum quorum f + quorumSum quorum g := by
  induction quorum with
  | nil => simp [quorumSum]
  | cons p rest ih =>
    obtain ⟨x, l⟩ := p
    simp only [quorumSum, ih]
    grind

/-- **Vandermonde-dual reconstruction.** Coefficients that pass `checkQuorumCoeffs` send the
evaluations of any polynomial of degree below `t` to `ξ` times its constant term, modulo `q`
(stated for every power shift `j`, which is what the induction needs). -/
theorem quorumSum_horner_dvd (q t : Nat) (slack : Int) (quorum : List (Int × Int))
    (hCheck : checkQuorumCoeffs q t slack quorum = true) :
    ∀ (as : List Int) (j : Nat), j + as.length ≤ t →
      (q : Int) ∣ quorumSum quorum (fun x => x ^ j * hornerInt as x) -
        (if j = 0 then slack * as.headD 0 else 0) := by
  have hPow : ∀ j, j < t →
      (q : Int) ∣ quorumSum quorum (fun x => x ^ j) - (if j = 0 then slack else 0) := by
    intro j hj
    have h := (List.all_eq_true.mp hCheck) j (List.mem_range.mpr hj)
    exact Int.dvd_of_emod_eq_zero (of_decide_eq_true h)
  intro as
  induction as with
  | nil =>
    intro j _
    have hf : (fun x : Int => x ^ j * hornerInt [] x) = fun _ => 0 := by
      funext x; simp [hornerInt]
    rw [hf, quorumSum_zero]
    split <;> simp
  | cons a as ih =>
    intro j hj
    simp only [List.length_cons] at hj
    have hf : (fun x : Int => x ^ j * hornerInt (a :: as) x) =
        fun x => a * x ^ j + x ^ (j + 1) * hornerInt as x := by
      funext x
      simp only [hornerInt]
      rw [Int.pow_succ]
      grind
    obtain ⟨c1, h1⟩ := hPow j (by omega)
    obtain ⟨c2, h2⟩ := ih (j + 1) (by omega)
    have hne : ¬ (j + 1 = 0) := by omega
    simp only [hne, ↓reduceIte, Int.sub_zero] at h2
    rw [hf, quorumSum_linear quorum a (fun x => x ^ j) (fun x => x ^ (j + 1) * hornerInt as x), h2]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [↓reduceIte, List.headD_cons] at h1 ⊢
      have e1 : quorumSum quorum (fun x => x ^ 0) = slack + (q : Int) * c1 := by omega
      rw [e1]
      exact ⟨a * c1 + c2, by grind⟩
    · simp only [hj0, ↓reduceIte, Int.sub_zero] at h1 ⊢
      rw [h1]
      exact ⟨a * c1 + c2, by grind⟩

theorem quorum_reconstructs (q t : Nat) (slack : Int) (quorum : List (Int × Int))
    (hCheck : checkQuorumCoeffs q t slack quorum = true) (as : List Int) (hLen : as.length ≤ t) :
    ∃ c, quorumSum quorum (hornerInt as) - slack * as.headD 0 = (q : Int) * c := by
  obtain ⟨c, hc⟩ := quorumSum_horner_dvd q t slack quorum hCheck as 0 (by omega)
  have hf : (fun x : Int => x ^ 0 * hornerInt as x) = hornerInt as := by funext x; simp
  rw [hf] at hc
  exact ⟨c, by simpa using hc⟩

theorem shamirShare_mul_spec {d : Nat} (c : FastIntPoly d) (x : Int) (k : Fin d)
    (as : List (FastIntPoly d)) :
    (negacyclicMulFast (shamirShare as x) c).spec k =
      hornerInt (as.map fun a => (negacyclicMulFast a c).spec k) x := by
  induction as with
  | nil => simp only [shamirShare, List.map_nil, hornerInt]; exact negacyclicMulFast_zero_left c k
  | cons a as ih =>
    simp only [shamirShare, List.map_cons, hornerInt]
    rw [negacyclicMulFast_add_left, negacyclicMulFast_scale_left, ih]

/-! ### 1b. The tag, partial decryption, the combiner -/

def tulvaTagDomain : List UInt8 := [84, 85, 76, 86, 65, 45, 84, 65, 71]

/-- Wire bytes of a ciphertext: both components, framed. -/
def ciphertextBytes {d : Nat} (ct : RlweCiphertext d) : List UInt8 :=
  encodeIntRows [polyCoeffs ct.c0, polyCoeffs ct.c1]

theorem ciphertextBytes_injective {d : Nat} {ct₁ ct₂ : RlweCiphertext d}
    (h : ciphertextBytes ct₁ = ciphertextBytes ct₂) : ct₁ = ct₂ := by
  have hr := encodeIntRows_injective h
  simp only [List.cons.injEq, and_true] at hr
  cases ct₁; cases ct₂
  simp only [RlweCiphertext.mk.injEq]
  exact ⟨polyCoeffs_injective hr.1, polyCoeffs_injective hr.2⟩

/-- The tag of a decryption query: `H(domain ‖ context ‖ ciphertext)`, every field framed. -/
def tulvaTag (H : Hash) (context : List UInt8) {d : Nat} (ct : RlweCiphertext d) : List UInt8 :=
  H (encodeFrameList tulvaTagDomain context (ciphertextBytes ct))

/-- A tag names one `(context, ciphertext)`: a share cannot be moved to another query. -/
theorem tulvaTag_binds_query (H : Hash) (ctx₁ ctx₂ : List UInt8) {d : Nat}
    (ct₁ ct₂ : RlweCiphertext d) (h : tulvaTag H ctx₁ ct₁ = tulvaTag H ctx₂ ct₂) :
    (ctx₁ = ctx₂ ∧ ct₁ = ct₂) ∨ Collision H := by
  rcases hash_frame_binding H h with ⟨_, hctx, hct⟩ | hcol
  · exact Or.inl ⟨hctx, ciphertextBytes_injective hct⟩
  · exact Or.inr hcol

/-- A tagged partial decryption from the party at evaluation point `point`. -/
structure TulvaShare (d : Nat) where
  point : Int
  tag : List UInt8
  sharePoly : FastIntPoly d

/-- Non-interactive partial decryption: `s_k · c₁ + e_k mod q` under the query's tag. The party
needs only its key share, the ciphertext and fresh flooding noise. -/
def tulvaPartialDecrypt (H : Hash) (pp : RlweParams) (context : List UInt8)
    (ct : RlweCiphertext pp.d) (point : Int) (skShare eSmudge : FastIntPoly pp.d) :
    TulvaShare pp.d :=
  { point := point
    tag := tulvaTag H context ct
    sharePoly := (computePartialShare pp point.toNat skShare ct.c1 eSmudge).sharePoly }

/-- A threshold profile: ring, threshold `t`, slack `ξ`, and the noise bounds the combiner enforces. -/
structure TulvaProfile where
  params : RlweParams
  threshold : Nat
  slack : Nat
  encNoiseBound : Nat
  smudgeBound : Nat
  secBits : Nat
  deriving DecidableEq, Repr

inductive TulvaRefusal where
  | invalidParams
  | unsmudged
  | tagMismatch
  | badCoefficients
  | noiseBudgetExceeded (total cap : Nat)
  deriving DecidableEq, Repr

/-- The quorum a list of `(λ_k, share_k)` entries names. -/
def tulvaQuorum {d : Nat} : List (Int × TulvaShare d) → List (Int × Int)
  | [] => []
  | e :: es => (e.2.point, e.1) :: tulvaQuorum es

def tulvaWeightedSum {d : Nat} : List (Int × TulvaShare d) → FastIntPoly d
  | [] => zeroVec d
  | e :: es => intAdd (intScale e.1 e.2.sharePoly) (tulvaWeightedSum es)

def lambdaWeight {d : Nat} : List (Int × TulvaShare d) → Nat
  | [] => 0
  | e :: es => e.1.natAbs + lambdaWeight es

/-- The worst-case noise of the combined phase: `ξ·‖e_ct‖ + Σ|λ_k|·‖e_k‖`. -/
def tulvaNoiseTotal (prof : TulvaProfile) {d : Nat} (entries : List (Int × TulvaShare d)) : Nat :=
  prof.slack * prof.encNoiseBound + lambdaWeight entries * prof.smudgeBound

def tulvaCheck (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) : Bool :=
  prof.params.wfB && decide (0 < prof.slack) &&
  checkSmudgeSafe prof.encNoiseBound prof.smudgeBound prof.secBits &&
  entries.all (fun e => decide (e.2.tag = tulvaTag H context ct)) &&
  checkQuorumCoeffs prof.params.q prof.threshold prof.slack (tulvaQuorum entries) &&
  decide (tulvaNoiseTotal prof entries < prof.params.noiseCap)

/-- The first clause of `tulvaCheck` that fails. -/
def tulvaRefusalOf (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) :
    TulvaRefusal :=
  if !(prof.params.wfB && decide (0 < prof.slack)) then .invalidParams
  else if !checkSmudgeSafe prof.encNoiseBound prof.smudgeBound prof.secBits then .unsmudged
  else if !entries.all (fun e => decide (e.2.tag = tulvaTag H context ct)) then .tagMismatch
  else if !checkQuorumCoeffs prof.params.q prof.threshold prof.slack (tulvaQuorum entries) then
    .badCoefficients
  else .noiseBudgetExceeded (tulvaNoiseTotal prof entries) prof.params.noiseCap

/-- Decode `ξ·c₀ + Σ λ_k pd_k` and divide the slack out. -/
def tulvaDecode (prof : TulvaProfile) (ct : RlweCiphertext prof.params.d)
    (entries : List (Int × TulvaShare prof.params.d)) : FastIntPoly prof.params.d :=
  let phase := reducePolyMod prof.params.q
    (intAdd (intScale (prof.slack : Int) ct.c0) (tulvaWeightedSum entries))
  Sized.ofFn fun i => rlweDecodeSignedCoeff prof.params (phase.spec i) / (prof.slack : Int)

/-- The public share combiner. -/
def tulvaCombine (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) :
    Except TulvaRefusal (FastIntPoly prof.params.d) :=
  if tulvaCheck H prof context ct entries then .ok (tulvaDecode prof ct entries)
  else .error (tulvaRefusalOf H prof context ct entries)

theorem tulvaCombine_ok_iff (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d))
    (mOut : FastIntPoly prof.params.d) :
    tulvaCombine H prof context ct entries = .ok mOut ↔
      tulvaCheck H prof context ct entries = true ∧ tulvaDecode prof ct entries = mOut := by
  unfold tulvaCombine
  constructor
  · intro h
    split at h
    · rename_i hc; exact ⟨hc, Except.ok.inj h⟩
    · cases h
  · rintro ⟨hc, hd⟩
    simp only [hc, ↓reduceIte, hd]

/-- Honest shares: each is `s_k · c₁ + e_k mod q` for the Shamir share `s_k` of the sharing
polynomial `poly` at the entry's point, with `‖e_k‖∞ ≤ smudgeBound`. -/
def TulvaSharesValid (pp : RlweParams) (c1 : FastIntPoly pp.d) (smudgeBound : Nat)
    (poly : List (FastIntPoly pp.d)) :
    List (Int × TulvaShare pp.d) → List (FastIntPoly pp.d) → Prop
  | [], [] => True
  | e :: es, n :: ns =>
    (∀ i : Fin pp.d, e.2.sharePoly.spec i % (pp.q : Int) =
        ((negacyclicMulFast (shamirShare poly e.2.point) c1).spec i + n.spec i) % (pp.q : Int)) ∧
    normInfFast n.coeffs ≤ smudgeBound ∧
    TulvaSharesValid pp c1 smudgeBound poly es ns
  | _, _ => False

theorem tulvaPartialDecrypt_valid (H : Hash) (pp : RlweParams) (context : List UInt8)
    (ct : RlweCiphertext pp.d) (point : Int) (poly : List (FastIntPoly pp.d))
    (eSmudge : FastIntPoly pp.d) (i : Fin pp.d) :
    (tulvaPartialDecrypt H pp context ct point (shamirShare poly point) eSmudge).sharePoly.spec i
        % (pp.q : Int) =
      ((negacyclicMulFast (shamirShare poly point) ct.c1).spec i + eSmudge.spec i) % (pp.q : Int) := by
  simp only [tulvaPartialDecrypt, computePartialShare, reducePolyMod_spec, addFast_eq_spec]
  exact Int.emod_emod _ _

/-- The weighted share sum is the quorum sum of the Horner phases plus a noise term bounded by
`Σ|λ_k| · smudgeBound`, modulo `q`. -/
theorem tulvaWeightedSum_phase (pp : RlweParams) (c1 : FastIntPoly pp.d) (S : Nat)
    (poly : List (FastIntPoly pp.d)) (i : Fin pp.d) :
    ∀ (entries : List (Int × TulvaShare pp.d)) (noises : List (FastIntPoly pp.d)),
      TulvaSharesValid pp c1 S poly entries noises →
      ∃ eta c : Int, eta.natAbs ≤ lambdaWeight entries * S ∧
        (tulvaWeightedSum entries).spec i -
          (quorumSum (tulvaQuorum entries)
            (hornerInt (poly.map fun a => (negacyclicMulFast a c1).spec i)) + eta) =
          (pp.q : Int) * c := by
  intro entries
  induction entries with
  | nil =>
    intro noises _
    refine ⟨0, 0, by simp [lambdaWeight], ?_⟩
    simp [tulvaWeightedSum, tulvaQuorum, quorumSum, zeroVec]
  | cons e es ih =>
    intro noises h
    cases noises with
    | nil => exact False.elim h
    | cons n ns =>
      obtain ⟨hShare, hNorm, hRest⟩ := h
      obtain ⟨eta', c', hb', hc'⟩ := ih ns hRest
      obtain ⟨u, hu⟩ := sub_eq_mul_of_emod_eq (hShare i)
      rw [shamirShare_mul_spec] at hu
      refine ⟨e.1 * n.spec i + eta', e.1 * u + c', ?_, ?_⟩
      · have hn : (n.spec i).natAbs ≤ S := Nat.le_trans (coeff_le_norm n i) hNorm
        have hmul : (e.1 * n.spec i).natAbs ≤ e.1.natAbs * S := by
          rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ hn
        have hadd := Int.natAbs_add_le (e.1 * n.spec i) eta'
        simp only [lambdaWeight, Nat.add_mul]
        omega
      · simp only [tulvaWeightedSum, tulvaQuorum, quorumSum, addFast_eq_spec, scaleFast_eq_spec]
        have key := congrArg (fun z => e.1 * z) hu
        simp only [Int.mul_sub, Int.mul_add] at key
        have hcomm := Int.mul_left_comm e.1 (pp.q : Int) u
        rw [Int.mul_add]
        omega

/-- **Decryption correctness.** When the combiner accepts, the shares are honest Shamir shares of
a sharing polynomial of degree below the threshold whose constant term is the key, each flooded
within `smudgeBound`, and the ciphertext encrypts `m` with error within `encNoiseBound`, the output
is `m`. The accepted configuration is `SmudgeSafe` and its worst-case combined noise
`ξ·‖e_ct‖ + Σ|λ_k|·‖e_k‖` is below `⌊q/(2t)⌋`. -/
theorem tulvaCombine_recovers_plaintext (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d))
    (sk : FastIntPoly prof.params.d) (higher noises : List (FastIntPoly prof.params.d))
    (m eEnc mOut : FastIntPoly prof.params.d)
    (hDec : tulvaCombine H prof context ct entries = .ok mOut)
    (hDeg : higher.length + 1 ≤ prof.threshold)
    (hEnc : RlweEncryptsWithError prof.params sk ct m eEnc)
    (hEncNorm : normInfFast eEnc.coeffs ≤ prof.encNoiseBound)
    (hShares : TulvaSharesValid prof.params ct.c1 prof.smudgeBound (sk :: higher) entries noises)
    (hRoom : ∀ i : Fin prof.params.d, -prof.params.halfT ≤ (prof.slack : Int) * m.spec i ∧
      (prof.slack : Int) * m.spec i < prof.params.halfT) :
    mOut = m ∧ SmudgeSafe prof.encNoiseBound prof.smudgeBound prof.secBits ∧
      tulvaNoiseTotal prof entries < prof.params.noiseCap := by
  obtain ⟨hChk, hOut⟩ := (tulvaCombine_ok_iff H prof context ct entries mOut).mp hDec
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  obtain ⟨⟨⟨⟨⟨hwf, hSlack⟩, hSm⟩, _⟩, hQ⟩, hTot⟩ := hChk
  refine ⟨?_, (checkSmudgeSafe_iff _ _ _).mp hSm, hTot⟩
  subst hOut
  apply Sized.ext
  funext i
  simp only [tulvaDecode, Sized.spec_ofFn, reducePolyMod_spec, addFast_eq_spec, scaleFast_eq_spec]
  obtain ⟨eta, c, hEta, hW⟩ := tulvaWeightedSum_phase prof.params ct.c1 prof.smudgeBound
    (sk :: higher) i entries noises hShares
  obtain ⟨u2, hV⟩ := quorum_reconstructs prof.params.q prof.threshold prof.slack
    (tulvaQuorum entries) hQ ((sk :: higher).map fun a => (negacyclicMulFast a ct.c1).spec i)
    (by simpa using hDeg)
  simp only [List.map_cons, List.headD_cons] at hV hW
  obtain ⟨u3, hE⟩ := sub_eq_mul_of_emod_eq (hEnc i)
  have hCong : ((prof.slack : Int) * ct.c0.spec i + (tulvaWeightedSum entries).spec i)
        % (prof.params.q : Int) % (prof.params.q : Int) =
      (prof.params.delta * ((prof.slack : Int) * m.spec i) +
        ((prof.slack : Int) * eEnc.spec i + eta)) % (prof.params.q : Int) := by
    rw [Int.emod_emod]
    apply emod_eq_of_sub_eq_mul (c := c + u2 + (prof.slack : Int) * u3)
    have k3 := congrArg (fun z => (prof.slack : Int) * z) hE
    simp only [Int.mul_sub, Int.mul_add] at k3
    have c1' := Int.mul_left_comm (prof.slack : Int) prof.params.delta (m.spec i)
    have c2' := Int.mul_left_comm (prof.slack : Int) (prof.params.q : Int) u3
    rw [Int.mul_add, Int.mul_add]
    omega
  have hNoise : ((prof.slack : Int) * eEnc.spec i + eta).natAbs < prof.params.noiseCap := by
    have hs : (prof.slack : Int).natAbs = prof.slack := by omega
    have h1 : ((prof.slack : Int) * eEnc.spec i).natAbs ≤ prof.slack * prof.encNoiseBound := by
      rw [Int.natAbs_mul, hs]
      exact Nat.mul_le_mul_left _ (Nat.le_trans (coeff_le_norm eEnc i) hEncNorm)
    have h2 := Int.natAbs_add_le ((prof.slack : Int) * eEnc.spec i) eta
    unfold tulvaNoiseTotal at hTot
    omega
  rw [rlweDecodeSignedCoeff_exact prof.params _ ((prof.slack : Int) * m.spec i)
    ((prof.slack : Int) * eEnc.spec i + eta) hwf hCong (hRoom i).1 (hRoom i).2 hNoise]
  exact Int.mul_ediv_cancel_left _ (by omega)

/-- A configuration with no flooding noise is refused, whatever the shares. -/
theorem tulvaCombine_refuses_unsmudged (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d))
    (hZero : prof.smudgeBound = 0) (mOut : FastIntPoly prof.params.d) :
    tulvaCombine H prof context ct entries ≠ .ok mOut := by
  intro h
  obtain ⟨hChk, _⟩ := (tulvaCombine_ok_iff H prof context ct entries mOut).mp h
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  have hSm := (checkSmudgeSafe_iff _ _ _).mp hChk.1.1.1.2
  rw [hZero] at hSm
  exact smudgeSafe_refuses_unsmudged _ _ hSm

/-- A quorum whose worst-case combined noise reaches the cap is refused. -/
theorem tulvaCombine_refuses_noise_overflow (H : Hash) (prof : TulvaProfile) (context : List UInt8)
    (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d))
    (hOver : prof.params.noiseCap ≤ tulvaNoiseTotal prof entries)
    (mOut : FastIntPoly prof.params.d) :
    tulvaCombine H prof context ct entries ≠ .ok mOut := by
  intro h
  obtain ⟨hChk, _⟩ := (tulvaCombine_ok_iff H prof context ct entries mOut).mp h
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  omega

/-! ### 1c. What a decryption leaks: the boundary oracle, and flooding by counting -/

/-- **The unsmudged decryption oracle leaks.** With the noise just past the cap the decoder
returns `m + 1`, with the noise inside it returns `m`. The noise of an evaluated ciphertext is an
affine function of the secret key, so one exact decryption answers a threshold question about the
key; this is the mechanism of the IND-CPA-D attacks on exact schemes whose parameters rest on a
heuristic noise estimate. -/
theorem tulva_unsmudged_boundary_oracle_leaks (pp : RlweParams) (hwf : pp.wfB = true)
    (m eIn eOut : Int) (hmLo : -pp.halfT ≤ m) (hmHi : m + 1 < pp.halfT)
    (hIn : eIn.natAbs < pp.noiseCap)
    (hOutLo : (pp.noiseCap : Int) < eOut) (hOutHi : eOut < 3 * (pp.noiseCap : Int)) :
    rlweDecodeSignedCoeff pp (pp.delta * m + eIn) = m ∧
    rlweDecodeSignedCoeff pp (pp.delta * m + eOut) = m + 1 := by
  obtain ⟨_, _, _, _, _, hDelta, _⟩ := rlweParams_identities pp hwf
  refine ⟨rlweDecodeSignedCoeff_exact pp _ m eIn hwf rfl hmLo (by omega) hIn, ?_⟩
  have hEq : pp.delta * m + eOut = pp.delta * (m + 1) + (eOut - 2 * (pp.noiseCap : Int)) := by
    rw [Int.mul_add, hDelta]
    omega
  exact rlweDecodeSignedCoeff_exact pp _ (m + 1) (eOut - 2 * (pp.noiseCap : Int)) hwf
    (by rw [hEq]) (by omega) hmHi (by omega)

/-- The support `[-S, S]` of uniform flooding noise. -/
def smudgeSupport (S : Nat) : List Int :=
  (List.range (2 * S + 1)).map fun (k : Nat) => (k : Int) - (S : Int)

/-- The masks whose view cannot be explained under a hypothesis shifted by `shift`: those `e`
with `e + shift` outside the support. -/
def smudgeUncoupled (S : Nat) (shift : Int) : List Int :=
  (smudgeSupport S).filter fun e => !decide (-(S : Int) ≤ e + shift ∧ e + shift ≤ S)

theorem mem_smudgeSupport (S : Nat) (e : Int) :
    e ∈ smudgeSupport S ↔ -(S : Int) ≤ e ∧ e ≤ S := by
  unfold smudgeSupport
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have := List.mem_range.mp hk
    omega
  · intro h
    exact ⟨(e + S).toNat, List.mem_range.mpr (by omega), by omega⟩

theorem coupled_of_not_uncoupled {S : Nat} {shift e : Int} (hs : e ∈ smudgeSupport S)
    (hn : e ∉ smudgeUncoupled S shift) : -(S : Int) ≤ e + shift ∧ e + shift ≤ S := by
  unfold smudgeUncoupled at hn
  rw [List.mem_filter] at hn
  by_cases hb : -(S : Int) ≤ e + shift ∧ e + shift ≤ S
  · exact hb
  · have hd : decide (-(S : Int) ≤ e + shift ∧ e + shift ≤ S) = false := decide_eq_false hb
    exact absurd ⟨hs, by rw [hd]; rfl⟩ hn

private theorem rangeFilter_length_le (p : Nat → Bool) (lo hi : Nat) :
    ∀ n, (∀ k, k < n → p k = true → k < lo ∨ hi ≤ k) →
      ((List.range n).filter p).length ≤ min n lo + (n - hi) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have ihn := ih (fun k hk hp => h k (by omega) hp)
    rw [List.range_succ, List.filter_append, List.length_append]
    cases hp : p n with
    | false =>
      have hl : (List.filter p [n]).length = 0 := by simp [hp]
      omega
    | true =>
      have hl : (List.filter p [n]).length = 1 := by simp [hp]
      have := h n (by omega) hp
      omega

/-- **Flooding, by counting.** At most `|shift|` of the `2S+1` masks are uncoupled. -/
theorem smudgeUncoupled_length_le (S : Nat) (shift : Int) :
    (smudgeUncoupled S shift).length ≤ shift.natAbs := by
  unfold smudgeUncoupled smudgeSupport
  rw [List.filter_map, List.length_map]
  refine Nat.le_trans
    (rangeFilter_length_le _ (-shift).toNat (2 * S + 1 - shift.toNat) (2 * S + 1) ?_) (by omega)
  intro k _ hp
  simp at hp
  omega

/-- With no flooding, every nonzero shift is detected by the one mask there is. -/
theorem smudgeUncoupled_unsmudged (shift : Int) (h : shift ≠ 0) :
    smudgeUncoupled 0 shift = smudgeSupport 0 := by
  simp [smudgeUncoupled, smudgeSupport]
  omega

/-- **Flooding under `SmudgeSafe`.** Two hypotheses whose phases differ by at most the noise bound
are told apart by at most a `2^-secBits` fraction of the masks: `uncoupled · 2^secBits ≤ S`, of a
support of `2S + 1`. -/
theorem tulva_smudge_floods_noise {noiseBound smudgeBound secBits : Nat}
    (h : SmudgeSafe noiseBound smudgeBound secBits) (shift : Int)
    (hShift : shift.natAbs ≤ noiseBound) :
    (smudgeUncoupled smudgeBound shift).length * 2 ^ secBits ≤ smudgeBound ∧
    (smudgeSupport smudgeBound).length = 2 * smudgeBound + 1 := by
  refine ⟨?_, by simp [smudgeSupport]⟩
  have hLen := Nat.le_trans (smudgeUncoupled_length_le smudgeBound shift) hShift
  exact Nat.le_trans (Nat.mul_le_mul_right _ hLen) h.2.2

/-- **A coupled share says nothing about which key made it.** If every coefficient of the mask is
coupled for the phase difference of two key shares on `c₁`, the same partial decryption is produced
by the other key share with another mask inside the flooding bound. -/
theorem tulvaShare_explained_by_other_key (pp : RlweParams) (g : Nat)
    (sk sk' c1 e : FastIntPoly pp.d) (S : Nat)
    (hCoupled : ∀ i : Fin pp.d, e.spec i ∈ smudgeSupport S ∧
      e.spec i ∉ smudgeUncoupled S
        ((negacyclicMulFast sk c1).spec i - (negacyclicMulFast sk' c1).spec i)) :
    ∃ e' : FastIntPoly pp.d, normInfFast e'.coeffs ≤ S ∧
      computePartialShare pp g sk' c1 e' = computePartialShare pp g sk c1 e := by
  refine ⟨intAdd e (intSub (negacyclicMulFast sk c1) (negacyclicMulFast sk' c1)), ?_, ?_⟩
  · apply norm_le
    intro i
    have h := coupled_of_not_uncoupled (hCoupled i).1 (hCoupled i).2
    simp only [addFast_eq_spec, subFast_eq_spec]
    omega
  · have hpoly : reducePolyMod pp.q (intAdd (negacyclicMulFast sk' c1)
          (intAdd e (intSub (negacyclicMulFast sk c1) (negacyclicMulFast sk' c1)))) =
        reducePolyMod pp.q (intAdd (negacyclicMulFast sk c1) e) := by
      apply Sized.ext
      funext i
      simp only [reducePolyMod_spec, addFast_eq_spec, subFast_eq_spec]
      apply emod_eq_of_sub_eq_mul (c := 0)
      omega
    unfold computePartialShare
    rw [hpoly]

/-! ## 2. Packed-bit openings: one commitment, three rings, a free range check -/

/-- Recomposition in `ℤ`: `ψ(c₀, c₁, …) = Σ c_j 2^j`. -/
def psiZ : List Int → Int
  | [] => 0
  | c :: cs => c + 2 * psiZ cs

/-- Recomposition in Goldilocks. -/
def psiFp : List Int → Goldilocks
  | [] => goldOfInt 0
  | c :: cs => Goldilocks.add (goldOfInt c) (Goldilocks.mul (goldOfInt 2) (psiFp cs))

/-- Recomposition in `ℤ_q`, reduced at every step. -/
def psiRq (q : Nat) : List Int → Int
  | [] => 0
  | c :: cs => (c + 2 * psiRq q cs) % (q : Int)

/-- Booleanity of every cell of a row, as the constraint `c(1 - c) = 0` over `ℤ`. -/
def checkBooleanRow (row : List Int) : Bool :=
  row.all fun c => decide (c * (1 - c) = 0)

theorem boolean_cell_iff (c : Int) : c * (1 - c) = 0 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    rcases Int.mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (h | h) <;> rw [h] <;> rfl

theorem psiFp_eq_goldOfInt (row : List Int) : psiFp row = goldOfInt (psiZ row) := by
  induction row with
  | nil => rfl
  | cons c cs ih => simp only [psiFp, psiZ, ih, goldOfInt_mul, goldOfInt_add]

theorem psiRq_eq_emod (q : Nat) (row : List Int) : psiRq q row = psiZ row % (q : Int) := by
  induction row with
  | nil => simp [psiRq, psiZ]
  | cons c cs ih =>
    simp only [psiRq, psiZ, ih]
    apply emod_eq_of_sub_eq_mul (c := -(2 * (psiZ cs / (q : Int))))
    have hd := Int.emod_def (psiZ cs) (q : Int)
    have hm := Int.mul_left_comm (q : Int) 2 (psiZ cs / (q : Int))
    rw [Int.mul_neg]
    omega

/-- **The free range check.** A boolean row of `B` cells recomposes into `[0, 2^B)`. -/
theorem psiZ_range (row : List Int) (hB : checkBooleanRow row = true) :
    0 ≤ psiZ row ∧ psiZ row < ((2 ^ row.length : Nat) : Int) := by
  induction row with
  | nil => simp [psiZ]
  | cons c cs ih =>
    simp only [checkBooleanRow, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨h0, h1⟩ := ih hB.2
    have hc := (boolean_cell_iff c).mp hB.1
    simp only [psiZ, List.length_cons, Nat.pow_succ]
    omega

/-- The row as the bit list of `SameOpening`: the same number. -/
theorem psiZ_eq_bitsToNat (row : List Int) (hB : checkBooleanRow row = true) :
    psiZ row = ((bitsToNat (row.map fun c => decide (c = 1)) : Nat) : Int) := by
  induction row with
  | nil => simp [psiZ, bitsToNat]
  | cons c cs ih =>
    simp only [checkBooleanRow, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hB
    have hih := ih hB.2
    rcases (boolean_cell_iff c).mp hB.1 with h | h
    · subst h; simp [psiZ, bitsToNat, hih]
    · subst h; simp [psiZ, bitsToNat, hih]

/-- The `SameOpening` order witness opened by two packed rows. -/
def bitzOrderWitness (qtyRow totalRow : List Int) (salt : GoldilocksExt2) : OrderBitWitness :=
  { qtyBits := qtyRow.map fun c => decide (c = 1)
    totalBits := totalRow.map fun c => decide (c = 1)
    salt := salt }

theorem bitzOrderWitness_opens (qtyRow totalRow : List Int) (salt : GoldilocksExt2)
    (hq : checkBooleanRow qtyRow = true) (ht : checkBooleanRow totalRow = true) :
    (((bitzOrderWitness qtyRow totalRow salt).qty : Nat) : Int) = psiZ qtyRow ∧
    (((bitzOrderWitness qtyRow totalRow salt).total : Nat) : Int) = psiZ totalRow :=
  ⟨(psiZ_eq_bitsToNat qtyRow hq).symm, (psiZ_eq_bitsToNat totalRow ht).symm⟩

def bitzDomain : List UInt8 := [66, 73, 84, 90]

/-- The one commitment to the witness matrix: `H(domain ‖ width ‖ rows)`, every row framed. -/
def bitzCommit (H : Hash) (width : Nat) (rows : List (List Int)) : List UInt8 :=
  H (encodeFrameList bitzDomain (leb128 width) (encodeIntRows rows))

theorem bitzCommit_binding (H : Hash) (w₁ w₂ : Nat) (rows₁ rows₂ : List (List Int))
    (h : bitzCommit H w₁ rows₁ = bitzCommit H w₂ rows₂) :
    (w₁ = w₂ ∧ rows₁ = rows₂) ∨ Collision H := by
  rcases hash_frame_binding H h with ⟨_, hw, hrows⟩ | hcol
  · exact Or.inl ⟨(leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hw)).1,
      encodeIntRows_injective hrows⟩
  · exact Or.inr hcol

/-- The two ring images claimed for one row: the `ℤ_q` plaintext coefficient of the encrypted
input, and the Goldilocks value in the clearing witness. -/
structure BitzClaim where
  rq : Int
  fp : Goldilocks
  deriving DecidableEq

def bitzRowsOk (q width : Nat) : List (List Int) → List BitzClaim → Bool
  | [], [] => true
  | row :: rows, cl :: cls =>
    decide (row.length = width) && checkBooleanRow row && decide (psiRq q row = cl.rq) &&
      decide (psiFp row = cl.fp) && bitzRowsOk q width rows cls
  | _, _ => false

/-- The opening check: the rows open the commitment, both rings hold `2^width`, and every row is
`width` boolean cells whose recomposition in each ring is the claimed value. -/
def bitzVerify (H : Hash) (q width : Nat) (commitment : List UInt8) (rows : List (List Int))
    (claims : List BitzClaim) : Bool :=
  decide (bitzCommit H width rows = commitment) && decide (2 ^ width ≤ q) &&
    decide (2 ^ width ≤ goldilocksPrime) && bitzRowsOk q width rows claims

theorem bitzRow_certified (q width : Nat) (row : List Int) (cl : BitzClaim)
    (hq : 2 ^ width ≤ q) (hp : 2 ^ width ≤ goldilocksPrime) (hLen : row.length = width)
    (hBool : checkBooleanRow row = true) (hRq : psiRq q row = cl.rq) (hFp : psiFp row = cl.fp) :
    ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n := by
  obtain ⟨h0, hlt⟩ := psiZ_range row hBool
  rw [hLen] at hlt
  refine ⟨(psiZ row).toNat, by omega, by omega, ?_, ?_⟩
  · rw [← hRq, psiRq_eq_emod, Int.emod_eq_of_lt h0 (by omega)]
    omega
  · rw [← hFp, psiFp_eq_goldOfInt]
    have hv := goldOfInt_val (psiZ row)
    have hlt' : psiZ row < (goldilocksPrime : Int) := by omega
    rw [Int.emod_eq_of_lt h0 hlt'] at hv
    omega

theorem bitzRowsOk_certified (q width : Nat) (hq : 2 ^ width ≤ q)
    (hp : 2 ^ width ≤ goldilocksPrime) :
    ∀ (rows : List (List Int)) (claims : List BitzClaim), bitzRowsOk q width rows claims = true →
      rows.length = claims.length ∧
      ∀ row cl, (row, cl) ∈ rows.zip claims →
        ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n := by
  intro rows
  induction rows with
  | nil =>
    intro claims h
    cases claims with
    | nil => exact ⟨rfl, by intro row cl hm; simp at hm⟩
    | cons _ _ => simp [bitzRowsOk] at h
  | cons r rs ih =>
    intro claims h
    cases claims with
    | nil => simp [bitzRowsOk] at h
    | cons c cs =>
      simp only [bitzRowsOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hLen, hBool⟩, hRq⟩, hFp⟩, hRest⟩ := h
      obtain ⟨hlen, hall⟩ := ih cs hRest
      refine ⟨by simp [hlen], ?_⟩
      intro row cl hm
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨hr, hc⟩ | hm
      · rw [hr, hc]; exact bitzRow_certified q width r c hq hp hLen hBool hRq hFp
      · exact hall row cl hm

/-- **One opening, the range and both rings.** An accepted opening gives, for every row and its
claim, one natural `n < 2^width` that is the row's recomposition in `ℤ`, the claimed `ℤ_q`
plaintext, and the canonical value of the claimed Goldilocks element: the range bound uses no
table, and the encrypted input and the clearing witness hold the same integer. The commitment
admits no other matrix short of a collision of `H`. -/
theorem bitz_sameOpening_and_free_range_sound (H : Hash) (q width : Nat)
    (commitment : List UInt8) (rows : List (List Int)) (claims : List BitzClaim)
    (h : bitzVerify H q width commitment rows claims = true) :
    rows.length = claims.length ∧
    (∀ row cl, (row, cl) ∈ rows.zip claims →
      ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n) ∧
    (∀ rows', bitzCommit H width rows' = commitment → rows' = rows ∨ Collision H) := by
  simp only [bitzVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hCom, hq⟩, hp⟩, hRows⟩ := h
  obtain ⟨hlen, hall⟩ := bitzRowsOk_certified q width hq hp rows claims hRows
  refine ⟨hlen, hall, ?_⟩
  intro rows' h'
  rcases bitzCommit_binding H width width rows' rows (h'.trans hCom.symm) with ⟨_, hr⟩ | hcol
  · exact Or.inl hr
  · exact Or.inr hcol

/-- **Completeness of the opening.** Boolean rows of the committed width, in rings that hold
`2^width`, open their own commitment with their own recompositions as claims. -/
theorem bitzVerify_complete (H : Hash) (q width : Nat) (rows : List (List Int))
    (hq : 2 ^ width ≤ q) (hp : 2 ^ width ≤ goldilocksPrime)
    (hRows : ∀ row ∈ rows, row.length = width ∧ checkBooleanRow row = true) :
    bitzVerify H q width (bitzCommit H width rows) rows
      (rows.map fun r => ⟨psiRq q r, psiFp r⟩) = true := by
  have hOk : bitzRowsOk q width rows (rows.map fun r => ⟨psiRq q r, psiFp r⟩) = true := by
    induction rows with
    | nil => rfl
    | cons r rs ih =>
      have hr := hRows r (by simp)
      have hih := ih (fun row hrow => hRows row (List.mem_cons_of_mem _ hrow))
      simp [bitzRowsOk, hr.1, hr.2, hih]
  simp [bitzVerify, hq, hp, hOk]

/-- The plaintext vector the claims name: lane `i` holds claim `i`'s `ℤ_q` value. -/
def bitzPlainVec (d : Nat) (claims : List BitzClaim) : FastIntPoly d :=
  Sized.ofFn fun i => ((claims[i.val]?).map (·.rq)).getD 0

/-! ## 3. A many-time lattice VRF over the opened witness -/

/-- Public parameters: modulus `q`, rounding modulus `p`, norm bound `β`, the public matrix `A`
(rows of `cols` ring elements) and the number of rows of the input-derived matrix. -/
structure LavParams (d : Nat) where
  q : Nat
  p : Nat
  beta : Nat
  cols : Nat
  outRows : Nat
  A : List (List (FastIntPoly d))

/-- `Σ_j z_j · a_j` in the ring. -/
def rowDot {d : Nat} : List (FastIntPoly d) → List (FastIntPoly d) → FastIntPoly d
  | [], _ => zeroVec d
  | _ :: _, [] => zeroVec d
  | z :: zs, a :: as => intAdd (negacyclicMulFast z a) (rowDot zs as)

def lavVecSub {d : Nat} : List (FastIntPoly d) → List (FastIntPoly d) → List (FastIntPoly d)
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => intSub a b :: lavVecSub as bs

theorem rowDot_sub_spec {d : Nat} (k : Fin d) :
    ∀ (z₁ z₂ row : List (FastIntPoly d)), z₁.length = z₂.length →
      (rowDot (lavVecSub z₁ z₂) row).spec k = (rowDot z₁ row).spec k - (rowDot z₂ row).spec k := by
  intro z₁
  induction z₁ with
  | nil =>
    intro z₂ row hl
    cases z₂ with
    | nil => simp [lavVecSub, rowDot, zeroVec_spec]
    | cons _ _ => simp at hl
  | cons a as ih =>
    intro z₂ row hl
    cases z₂ with
    | nil => simp at hl
    | cons b bs =>
      cases row with
      | nil => simp [lavVecSub, rowDot, zeroVec_spec]
      | cons r rs =>
        have hl' : as.length = bs.length := by simpa using hl
        simp only [lavVecSub, rowDot, addFast_eq_spec]
        rw [negacyclicMulFast_sub_left, ih bs rs hl']
        omega

theorem lavVecSub_short {d : Nat} (beta : Nat) :
    ∀ (z₁ z₂ : List (FastIntPoly d)), (∀ a ∈ z₁, normInfFast a.coeffs ≤ beta) →
      (∀ b ∈ z₂, normInfFast b.coeffs ≤ beta) →
      ∀ c ∈ lavVecSub z₁ z₂, normInfFast c.coeffs ≤ 2 * beta := by
  intro z₁
  induction z₁ with
  | nil => intro z₂ _ _ c hc; simp [lavVecSub] at hc
  | cons a as ih =>
    intro z₂ h1 h2 c hc
    cases z₂ with
    | nil => simp [lavVecSub] at hc
    | cons b bs =>
      simp only [lavVecSub, List.mem_cons] at hc
      rcases hc with hc | hc
      · have hs := normInfFast_sub_le a b
        have ha := h1 a (by simp)
        have hb := h2 b (by simp)
        rw [hc]
        omega
      · exact ih bs (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
          (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) c hc

theorem lavVecSub_nonzero {d : Nat} :
    ∀ (z₁ z₂ : List (FastIntPoly d)), z₁.length = z₂.length → z₁ ≠ z₂ →
      ∃ a ∈ lavVecSub z₁ z₂, a ≠ zeroVec d := by
  intro z₁
  induction z₁ with
  | nil =>
    intro z₂ hl hne
    cases z₂ with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hl
  | cons a as ih =>
    intro z₂ hl hne
    cases z₂ with
    | nil => simp at hl
    | cons b bs =>
      by_cases hab : a = b
      · have hne' : as ≠ bs := fun h => hne (by rw [hab, h])
        obtain ⟨c, hc, hcz⟩ := ih bs (by simpa using hl) hne'
        exact ⟨c, by simp [lavVecSub, hc], hcz⟩
      · refine ⟨intSub a b, by simp [lavVecSub], ?_⟩
        intro hz
        apply hab
        apply Sized.ext
        funext i
        have hi := congrArg (fun p => p.spec i) hz
        simp [zeroVec] at hi
        omega

/-- A break of Module-SIS for `A` at norm `2β`: a nonzero vector of that norm in the kernel of
`A` modulo `q`. -/
def MsisBreak {d : Nat} (pp : LavParams d) : Prop :=
  ∃ w : List (FastIntPoly d), (∃ a ∈ w, a ≠ zeroVec d) ∧
    (∀ a ∈ w, normInfFast a.coeffs ≤ 2 * pp.beta) ∧
    ∀ row ∈ pp.A, ∀ k : Fin d, (rowDot w row).spec k % (pp.q : Int) = 0

def lavKeyDomain : List UInt8 := [76, 65, 86, 45, 75, 69, 89]
def lavInputDomain : List UInt8 := [76, 65, 86, 45, 73, 78]
def lavExpandDomain : List UInt8 := [76, 65, 86, 45, 69, 88, 80]
def lavOutDomain : List UInt8 := [76, 65, 86, 45, 79, 85, 84]
def lavRingDomain : List UInt8 := [76, 65, 86, 45, 82, 73, 78, 71]

/-- The public key `t = A·z mod q`. -/
def lavImage {d : Nat} (pp : LavParams d) (z : List (FastIntPoly d)) : List (FastIntPoly d) :=
  pp.A.map fun row => reducePolyMod pp.q (rowDot z row)

/-- The registered 256-bit digest of a public key. -/
def lavKeyDigest (H : Hash) {d : Nat} (pk : List (FastIntPoly d)) : List UInt8 :=
  H (encodeFrameList lavKeyDomain [] (encodeIntRows (pk.map polyCoeffs)))

/-- The digest of a ring of registered keys, bound into every input evaluated under that ring. -/
def lavRingDigest (H : Hash) (ringKeys : List (List UInt8)) : List UInt8 :=
  H (encodeFrameList lavRingDomain [] (encodeFields ringKeys))

theorem lavRingDigest_binds (H : Hash) (r₁ r₂ : List (List UInt8))
    (h : lavRingDigest H r₁ = lavRingDigest H r₂) : r₁ = r₂ ∨ Collision H := by
  rcases hash_frame_binding H h with ⟨_, _, hr⟩ | hcol
  · exact Or.inl (encodeFields_injective hr)
  · exact Or.inr hcol

/-- The domain-separated input `domain ‖ ring ‖ epoch ‖ slot`. -/
def lavInput (ring : List UInt8) (epoch slot : Nat) : List UInt8 :=
  encodeFrameList lavInputDomain ring (leb128 epoch ++ leb128 slot)

theorem lavInput_injective {r₁ r₂ : List UInt8} {e₁ e₂ s₁ s₂ : Nat}
    (h : lavInput r₁ e₁ s₁ = lavInput r₂ e₂ s₂) : r₁ = r₂ ∧ e₁ = e₂ ∧ s₁ = s₂ := by
  obtain ⟨_, hr, hes⟩ := encodeFrameList_injective h
  obtain ⟨he, hs⟩ := leb128_prefix_inj hes
  exact ⟨hr, he, (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hs)).1⟩

def lavSeed (H : Hash) (ring : List UInt8) (epoch slot : Nat) : List UInt8 :=
  H (lavInput ring epoch slot)

/-- One seed names one `(ring, epoch, slot)`: an evaluation cannot be replayed at another slot or
under another ring. -/
theorem lavSeed_binds (H : Hash) (r₁ r₂ : List UInt8) (e₁ e₂ s₁ s₂ : Nat)
    (h : lavSeed H r₁ e₁ s₁ = lavSeed H r₂ e₂ s₂) :
    (r₁ = r₂ ∧ e₁ = e₂ ∧ s₁ = s₂) ∨ Collision H := by
  by_cases hPre : lavInput r₁ e₁ s₁ = lavInput r₂ e₂ s₂
  · exact Or.inl (lavInput_injective hPre)
  · exact Or.inr ⟨_, _, hPre, congrArg ofBE h⟩

/-- Entry `(i, j)` of the input-derived matrix: coefficient `k` is `H(domain ‖ seed ‖ i ‖ j ‖ k)`
read as an integer, modulo `q`. -/
def lavHashPoly (H : Hash) (q d : Nat) (seed : List UInt8) (i j : Nat) : FastIntPoly d :=
  Sized.ofFn fun k : Fin d =>
    ((ofBE (H (encodeFrameList lavExpandDomain seed (leb128 i ++ leb128 j ++ leb128 k.val))) : Nat)
      : Int) % (q : Int)

def lavHashMatrix (H : Hash) {d : Nat} (pp : LavParams d) (seed : List UInt8) :
    List (List (FastIntPoly d)) :=
  (List.range pp.outRows).map fun i => (List.range pp.cols).map fun j => lavHashPoly H pp.q d seed i j

/-- Rounding `⌊(p/q)·c⌉ mod p` of a residue. -/
def lavRound (q p : Nat) (c : Int) : Int :=
  ((c % (q : Int)) * (p : Int) + (q : Int) / 2) / (q : Int) % (p : Int)

/-- The rounded pre-output `y = ⌊B_x · z⌉_p`. -/
def lavPreOutput (H : Hash) {d : Nat} (pp : LavParams d) (seed : List UInt8)
    (z : List (FastIntPoly d)) : List (FastIntPoly d) :=
  (lavHashMatrix H pp seed).map fun row =>
    Sized.ofFn fun k => lavRound pp.q pp.p ((rowDot z row).spec k)

/-- The VRF value `v = H(domain ‖ key digest ‖ input ‖ y)`. -/
def lavOutput (H : Hash) (keyDigest input : List UInt8) {d : Nat} (y : List (FastIntPoly d)) :
    List UInt8 :=
  H (encodeFrameList lavOutDomain (encodeListField keyDigest ++ encodeListField input)
    (encodeIntRows (y.map polyCoeffs)))

def lavShort {d : Nat} (beta : Nat) (z : List (FastIntPoly d)) : Bool :=
  z.all fun a => decide (normInfFast a.coeffs ≤ beta)

theorem lavShort_iff {d : Nat} (beta : Nat) (z : List (FastIntPoly d)) :
    lavShort beta z = true ↔ ∀ a ∈ z, normInfFast a.coeffs ≤ beta := by
  simp [lavShort, List.all_eq_true]

/-- An opened evaluation: the public key, the short witness, the rounded pre-output. -/
structure LavProof (d : Nat) where
  pk : List (FastIntPoly d)
  z : List (FastIntPoly d)
  y : List (FastIntPoly d)

def lavVerify (H : Hash) {d : Nat} (pp : LavParams d) (keyDigest ring : List UInt8)
    (epoch slot : Nat) (v : List UInt8) (π : LavProof d) : Bool :=
  decide (lavKeyDigest H π.pk = keyDigest) &&
  decide (π.z.length = pp.cols) &&
  lavShort pp.beta π.z &&
  decide (lavImage pp π.z = π.pk) &&
  decide (lavPreOutput H pp (lavSeed H ring epoch slot) π.z = π.y) &&
  decide (v = lavOutput H keyDigest (lavInput ring epoch slot) π.y)

def lavEval (H : Hash) {d : Nat} (pp : LavParams d) (ring : List UInt8) (epoch slot : Nat)
    (sk : List (FastIntPoly d)) : List UInt8 × LavProof d :=
  let pk := lavImage pp sk
  let y := lavPreOutput H pp (lavSeed H ring epoch slot) sk
  (lavOutput H (lavKeyDigest H pk) (lavInput ring epoch slot) y, { pk := pk, z := sk, y := y })

/-- **Completeness.** A short key of the right length evaluates to an accepted pair at every
`(ring, epoch, slot)`, under the digest of its own public key. -/
theorem lavEval_complete (H : Hash) {d : Nat} (pp : LavParams d) (ring : List UInt8)
    (epoch slot : Nat) (sk : List (FastIntPoly d)) (hLen : sk.length = pp.cols)
    (hShort : lavShort pp.beta sk = true) :
    lavVerify H pp (lavKeyDigest H (lavImage pp sk)) ring epoch slot
      (lavEval H pp ring epoch slot sk).1 (lavEval H pp ring epoch slot sk).2 = true := by
  simp [lavVerify, lavEval, hLen, hShort]

/-- **Uniqueness.** Two accepted evaluations for one registered key digest and one
`(ring, epoch, slot)` with different values give a Module-SIS break for `A` (the difference of the
two witnesses: nonzero, of norm at most `2β`, in the kernel modulo `q`) or a collision of `H` (two
public keys under one digest). Nothing is assumed of the evaluator: it may hold the key and try
as many proofs as it likes. -/
theorem lav_unique_output_or_msisBreak {d : Nat} (H : Hash) (pp : LavParams d)
    (keyDigest ring : List UInt8) (epoch slot : Nat) (v₁ v₂ : List UInt8) (π₁ π₂ : LavProof d)
    (h₁ : lavVerify H pp keyDigest ring epoch slot v₁ π₁ = true)
    (h₂ : lavVerify H pp keyDigest ring epoch slot v₂ π₂ = true)
    (hne : v₁ ≠ v₂) : MsisBreak pp ∨ Collision H := by
  simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  obtain ⟨⟨⟨⟨⟨hk₁, hl₁⟩, hs₁⟩, hi₁⟩, hy₁⟩, hv₁⟩ := h₁
  obtain ⟨⟨⟨⟨⟨hk₂, hl₂⟩, hs₂⟩, hi₂⟩, hy₂⟩, hv₂⟩ := h₂
  rcases hash_frame_binding H (hk₁.trans hk₂.symm) with ⟨_, _, hrows⟩ | hcol
  · left
    have hpk : π₁.pk = π₂.pk := polyRows_injective (encodeIntRows_injective hrows)
    have hz : π₁.z ≠ π₂.z := by
      intro hzz
      apply hne
      rw [hv₁, hv₂, ← hy₁, ← hy₂, hzz]
    have hlen : π₁.z.length = π₂.z.length := hl₁.trans hl₂.symm
    refine ⟨lavVecSub π₁.z π₂.z, lavVecSub_nonzero _ _ hlen hz,
      lavVecSub_short pp.beta _ _ ((lavShort_iff _ _).mp hs₁) ((lavShort_iff _ _).mp hs₂), ?_⟩
    intro row hrow k
    rw [rowDot_sub_spec k _ _ row hlen]
    have himg : lavImage pp π₁.z = lavImage pp π₂.z := hi₁.trans (hpk.trans hi₂.symm)
    have hrowEq := map_eq_at himg row hrow
    have hk := congrArg (fun a => a.spec k) hrowEq
    simp only [reducePolyMod_spec] at hk
    rw [Int.sub_emod, hk, Int.sub_self, Int.zero_emod]
  · exact Or.inr hcol

/-- A ticket under a ring of registered key digests: the index of the key, the value, the proof. -/
structure LavTicket (d : Nat) where
  keyIndex : Nat
  output : List UInt8
  proof : LavProof d

/-- Ring verification: the input is bound to the digest of the whole ring. -/
def lavRingVerify (H : Hash) {d : Nat} (pp : LavParams d) (ringKeys : List (List UInt8))
    (epoch slot : Nat) (t : LavTicket d) : Bool :=
  match ringKeys[t.keyIndex]? with
  | some kd => lavVerify H pp kd (lavRingDigest H ringKeys) epoch slot t.output t.proof
  | none => false

theorem lavRingVerify_unique {d : Nat} (H : Hash) (pp : LavParams d)
    (ringKeys : List (List UInt8)) (epoch slot : Nat) (t₁ t₂ : LavTicket d)
    (hidx : t₁.keyIndex = t₂.keyIndex)
    (h₁ : lavRingVerify H pp ringKeys epoch slot t₁ = true)
    (h₂ : lavRingVerify H pp ringKeys epoch slot t₂ = true)
    (hne : t₁.output ≠ t₂.output) : MsisBreak pp ∨ Collision H := by
  unfold lavRingVerify at h₁ h₂
  rw [hidx] at h₁
  cases hk : ringKeys[t₂.keyIndex]? with
  | none => rw [hk] at h₂; simp at h₂
  | some kd =>
    rw [hk] at h₁ h₂
    exact lav_unique_output_or_msisBreak H pp kd _ epoch slot _ _ _ _ h₁ h₂ hne

/-- **`T`-uniqueness.** Accepted tickets with pairwise distinct values for one `(ring, epoch,
slot)` use pairwise distinct keys, short of a Module-SIS break or a collision: there are no more
accepted values to choose among than keys used to make them, however the evaluator grinds. -/
theorem lav_T_uniqueness {d : Nat} (H : Hash) (pp : LavParams d) (ringKeys : List (List UInt8))
    (epoch slot : Nat) :
    ∀ tickets : List (LavTicket d),
      (∀ t ∈ tickets, lavRingVerify H pp ringKeys epoch slot t = true) →
      (tickets.map fun t => t.output).Nodup →
      (tickets.map fun t => t.keyIndex).Nodup ∨ MsisBreak pp ∨ Collision H := by
  intro tickets
  induction tickets with
  | nil => intro _ _; exact Or.inl (by simp)
  | cons t ts ih =>
    intro hAll hND
    simp only [List.map_cons, List.nodup_cons] at hND ⊢
    obtain ⟨hOut, hRest⟩ := hND
    rcases ih (fun x hx => hAll x (List.mem_cons_of_mem _ hx)) hRest with hI | hB
    · by_cases hmem : t.keyIndex ∈ ts.map fun t => t.keyIndex
      · right
        obtain ⟨t', ht', hidx⟩ := List.mem_map.mp hmem
        exact lavRingVerify_unique H pp ringKeys epoch slot t' t hidx
          (hAll t' (List.mem_cons_of_mem _ ht')) (hAll t (by simp))
          (fun h => hOut (List.mem_map.mpr ⟨t', ht', h⟩))
      · exact Or.inl ⟨hmem, hI⟩
    · exact Or.inr hB

/-! ## 4. The auction machine: leader ticket, packed opening, tagged threshold decryption

One turn is one sealed batch: the slot leader's ticket for the current epoch, a ciphertext of the
aggregate input with its quorum of tagged partial decryptions, and the packed-bit opening whose
`ℤ_q` claims must be the decrypted plaintext. The state that accumulates is the epoch, the tags
already decrypted (a second decryption of one query would draw fresh flooding noise and let the
noise be averaged out), the number of partial decryptions released against the budget, and the
log of leader values. -/

structure AuctionConfig where
  tulva : TulvaProfile
  lav : LavParams tulva.params.d
  width : Nat
  ringKeys : List (List UInt8)
  queryBudget : Nat

structure AuctionTurn (cfg : AuctionConfig) where
  slot : Nat
  ticket : LavTicket cfg.tulva.params.d
  context : List UInt8
  ct : RlweCiphertext cfg.tulva.params.d
  entries : List (Int × TulvaShare cfg.tulva.params.d)
  commitment : List UInt8
  rows : List (List Int)
  claims : List BitzClaim

structure AuctionState where
  epoch : Nat
  queriesUsed : Nat
  usedTags : List (List UInt8)
  leaders : List (List UInt8)

def AuctionState.init : AuctionState :=
  { epoch := 0, queriesUsed := 0, usedTags := [], leaders := [] }

def auctionTurnCheck (H : Hash) (cfg : AuctionConfig) (st : AuctionState)
    (turn : AuctionTurn cfg) : Bool :=
  lavRingVerify H cfg.lav cfg.ringKeys st.epoch turn.slot turn.ticket &&
  decide (tulvaTag H turn.context turn.ct ∉ st.usedTags) &&
  decide (st.queriesUsed + turn.entries.length ≤ cfg.queryBudget) &&
  bitzVerify H cfg.tulva.params.q cfg.width turn.commitment turn.rows turn.claims &&
  tulvaCheck H cfg.tulva turn.context turn.ct turn.entries &&
  decide (tulvaDecode cfg.tulva turn.ct turn.entries = bitzPlainVec cfg.tulva.params.d turn.claims)

def auctionStep (H : Hash) (cfg : AuctionConfig) (st : AuctionState) (turn : AuctionTurn cfg) :
    Option AuctionState :=
  if auctionTurnCheck H cfg st turn then
    some { epoch := st.epoch + 1
           queriesUsed := st.queriesUsed + turn.entries.length
           usedTags := tulvaTag H turn.context turn.ct :: st.usedTags
           leaders := turn.ticket.output :: st.leaders }
  else none

def auctionRun (H : Hash) (cfg : AuctionConfig) :
    AuctionState → List (AuctionTurn cfg) → Option AuctionState
  | st, [] => some st
  | st, turn :: turns =>
    match auctionStep H cfg st turn with
    | some st' => auctionRun H cfg st' turns
    | none => none

/-- The invariant of the machine: the budget is respected and no tag was decrypted twice. -/
def AuctionInv (cfg : AuctionConfig) (st : AuctionState) : Prop :=
  st.queriesUsed ≤ cfg.queryBudget ∧ st.usedTags.Nodup

theorem auctionInv_init (cfg : AuctionConfig) : AuctionInv cfg AuctionState.init :=
  ⟨Nat.zero_le _, List.nodup_nil⟩

theorem auctionStep_spec (H : Hash) (cfg : AuctionConfig) (st st' : AuctionState)
    (turn : AuctionTurn cfg) (h : auctionStep H cfg st turn = some st') :
    auctionTurnCheck H cfg st turn = true ∧ st'.epoch = st.epoch + 1 ∧
    st'.queriesUsed = st.queriesUsed + turn.entries.length ∧
    st'.usedTags = tulvaTag H turn.context turn.ct :: st.usedTags ∧
    st'.leaders = turn.ticket.output :: st.leaders := by
  unfold auctionStep at h
  split at h
  · rename_i hc
    have hst := Option.some.inj h
    subst hst
    exact ⟨hc, rfl, rfl, rfl, rfl⟩
  · cases h

/-- A refused turn broke a named clause of the turn contract; nothing else is refused. -/
theorem auctionStep_refused_iff (H : Hash) (cfg : AuctionConfig) (st : AuctionState)
    (turn : AuctionTurn cfg) :
    auctionStep H cfg st turn = none ↔
      (lavRingVerify H cfg.lav cfg.ringKeys st.epoch turn.slot turn.ticket = false ∨
       tulvaTag H turn.context turn.ct ∈ st.usedTags ∨
       cfg.queryBudget < st.queriesUsed + turn.entries.length ∨
       bitzVerify H cfg.tulva.params.q cfg.width turn.commitment turn.rows turn.claims = false ∨
       tulvaCheck H cfg.tulva turn.context turn.ct turn.entries = false ∨
       tulvaDecode cfg.tulva turn.ct turn.entries ≠
         bitzPlainVec cfg.tulva.params.d turn.claims) := by
  unfold auctionStep auctionTurnCheck
  cases h1 : lavRingVerify H cfg.lav cfg.ringKeys st.epoch turn.slot turn.ticket <;>
  cases h4 : bitzVerify H cfg.tulva.params.q cfg.width turn.commitment turn.rows turn.claims <;>
  cases h5 : tulvaCheck H cfg.tulva turn.context turn.ct turn.entries <;>
  by_cases h2 : tulvaTag H turn.context turn.ct ∈ st.usedTags <;>
  by_cases h3 : st.queriesUsed + turn.entries.length ≤ cfg.queryBudget <;>
  by_cases h6 : tulvaDecode cfg.tulva turn.ct turn.entries =
    bitzPlainVec cfg.tulva.params.d turn.claims <;>
  simp [h2, h3, h6] <;> omega

/-- **Multi-turn safety.** Along any accepted run the invariant is kept, the epoch advances by
one per turn, the leader log grows by one per turn, no decrypted tag is forgotten, and the number
of released partial decryptions only grows and stays within the budget. -/
theorem auctionRun_safe (H : Hash) (cfg : AuctionConfig) :
    ∀ (turns : List (AuctionTurn cfg)) (st st' : AuctionState),
      auctionRun H cfg st turns = some st' → AuctionInv cfg st →
      AuctionInv cfg st' ∧ st'.epoch = st.epoch + turns.length ∧
      st'.leaders.length = st.leaders.length + turns.length ∧
      (∀ tag ∈ st.usedTags, tag ∈ st'.usedTags) ∧ st.queriesUsed ≤ st'.queriesUsed := by
  intro turns
  induction turns with
  | nil =>
    intro st st' h hInv
    have hst : st = st' := Option.some.inj h
    subst hst
    exact ⟨hInv, rfl, rfl, fun _ h => h, Nat.le_refl _⟩
  | cons turn turns ih =>
    intro st st' h hInv
    simp only [auctionRun] at h
    cases hs : auctionStep H cfg st turn with
    | none => rw [hs] at h; cases h
    | some mid =>
      rw [hs] at h
      obtain ⟨hc, hEp, hQ, hTags, hLead⟩ := auctionStep_spec H cfg st mid turn hs
      simp only [auctionTurnCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨_, hTag⟩, hBud⟩, _⟩, _⟩, _⟩ := hc
      have hMid : AuctionInv cfg mid :=
        ⟨by rw [hQ]; exact hBud, by rw [hTags]; exact List.nodup_cons.mpr ⟨hTag, hInv.2⟩⟩
      obtain ⟨hInv', hEp', hLead', hSub, hMono⟩ := ih mid st' h hMid
      refine ⟨hInv', ?_, ?_, ?_, by omega⟩
      · rw [hEp', hEp, List.length_cons]; omega
      · rw [hLead', hLead, List.length_cons, List.length_cons]; omega
      · intro tag htag
        exact hSub tag (by rw [hTags]; exact List.mem_cons_of_mem _ htag)

/-- Every turn of an accepted run passed the turn check at some reached state. -/
theorem auctionRun_turns_checked (H : Hash) (cfg : AuctionConfig) :
    ∀ (turns : List (AuctionTurn cfg)) (st st' : AuctionState),
      auctionRun H cfg st turns = some st' →
      ∀ turn ∈ turns, ∃ mid : AuctionState, st.epoch ≤ mid.epoch ∧
        auctionTurnCheck H cfg mid turn = true := by
  intro turns
  induction turns with
  | nil => intro _ _ _ turn hm; simp at hm
  | cons t ts ih =>
    intro st st' h turn hm
    simp only [auctionRun] at h
    cases hs : auctionStep H cfg st t with
    | none => rw [hs] at h; cases h
    | some mid =>
      rw [hs] at h
      obtain ⟨hc, hEp, _⟩ := auctionStep_spec H cfg st mid t hs
      rcases List.mem_cons.mp hm with hEq | hIn
      · exact ⟨st, Nat.le_refl _, by rw [hEq]; exact hc⟩
      · obtain ⟨m, hm1, hm2⟩ := ih mid st' h turn hIn
        exact ⟨m, by omega, hm2⟩

/-- **What an accepted turn establishes.** If the turn's shares are honest Shamir shares of the
key and its ciphertext encrypts `m` within the profile's noise bound, then `m` is the plaintext
vector of the claims; every row and claim hold one natural below `2^width` that is the `ℤ`
recomposition, the `ℤ_q` plaintext and the Goldilocks value; and the configuration is
`SmudgeSafe`. -/
theorem auctionTurn_cleared_and_certified (H : Hash) (cfg : AuctionConfig) (st : AuctionState)
    (turn : AuctionTurn cfg)
    (sk : FastIntPoly cfg.tulva.params.d) (higher noises : List (FastIntPoly cfg.tulva.params.d))
    (m eEnc : FastIntPoly cfg.tulva.params.d)
    (hChk : auctionTurnCheck H cfg st turn = true)
    (hDeg : higher.length + 1 ≤ cfg.tulva.threshold)
    (hEnc : RlweEncryptsWithError cfg.tulva.params sk turn.ct m eEnc)
    (hEncNorm : normInfFast eEnc.coeffs ≤ cfg.tulva.encNoiseBound)
    (hShares : TulvaSharesValid cfg.tulva.params turn.ct.c1 cfg.tulva.smudgeBound (sk :: higher)
      turn.entries noises)
    (hRoom : ∀ i : Fin cfg.tulva.params.d,
      -cfg.tulva.params.halfT ≤ (cfg.tulva.slack : Int) * m.spec i ∧
      (cfg.tulva.slack : Int) * m.spec i < cfg.tulva.params.halfT) :
    m = bitzPlainVec cfg.tulva.params.d turn.claims ∧
    (∀ row cl, (row, cl) ∈ turn.rows.zip turn.claims →
      ∃ n : Nat, n < 2 ^ cfg.width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n) ∧
    SmudgeSafe cfg.tulva.encNoiseBound cfg.tulva.smudgeBound cfg.tulva.secBits := by
  simp only [auctionTurnCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hBitz⟩, hTulva⟩, hDecEq⟩ := hChk
  have hDec := (tulvaCombine_ok_iff H cfg.tulva turn.context turn.ct turn.entries
    (tulvaDecode cfg.tulva turn.ct turn.entries)).mpr ⟨hTulva, rfl⟩
  obtain ⟨hm, hSafe, _⟩ := tulvaCombine_recovers_plaintext H cfg.tulva turn.context turn.ct
    turn.entries sk higher noises m eEnc _ hDec hDeg hEnc hEncNorm hShares hRoom
  obtain ⟨_, hRows, _⟩ := bitz_sameOpening_and_free_range_sound H cfg.tulva.params.q cfg.width
    turn.commitment turn.rows turn.claims hBitz
  exact ⟨hm.symm.trans hDecEq, hRows, hSafe⟩

/-- **The leader schedule fixes the leader log.** Two accepted runs from states with the same
epoch and log whose turns name the same `(slot, key)` at every position end with the same log of
leader values, short of a Module-SIS break or a collision: no choice of ciphertexts, shares or
proofs along the way changes who the leaders' values say they are. -/
theorem auctionRun_leaders_unique (H : Hash) (cfg : AuctionConfig) :
    ∀ (ts₁ ts₂ : List (AuctionTurn cfg)) (st₁ st₂ f₁ f₂ : AuctionState),
      st₁.epoch = st₂.epoch → st₁.leaders = st₂.leaders →
      (ts₁.map fun t => (t.slot, t.ticket.keyIndex)) =
        (ts₂.map fun t => (t.slot, t.ticket.keyIndex)) →
      auctionRun H cfg st₁ ts₁ = some f₁ → auctionRun H cfg st₂ ts₂ = some f₂ →
      f₁.leaders = f₂.leaders ∨ MsisBreak cfg.lav ∨ Collision H := by
  intro ts₁
  induction ts₁ with
  | nil =>
    intro ts₂ st₁ st₂ f₁ f₂ _ hL hMap h₁ h₂
    cases ts₂ with
    | nil =>
      have e₁ : st₁ = f₁ := Option.some.inj h₁
      have e₂ : st₂ = f₂ := Option.some.inj h₂
      exact Or.inl (by rw [← e₁, ← e₂]; exact hL)
    | cons _ _ => simp at hMap
  | cons t₁ ts₁ ih =>
    intro ts₂ st₁ st₂ f₁ f₂ hE hL hMap h₁ h₂
    cases ts₂ with
    | nil => simp at hMap
    | cons t₂ ts₂ =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hMap
      obtain ⟨⟨hSlot, hIdx⟩, hTail⟩ := hMap
      simp only [auctionRun] at h₁ h₂
      cases hs₁ : auctionStep H cfg st₁ t₁ with
      | none => rw [hs₁] at h₁; cases h₁
      | some m₁ =>
        cases hs₂ : auctionStep H cfg st₂ t₂ with
        | none => rw [hs₂] at h₂; cases h₂
        | some m₂ =>
          rw [hs₁] at h₁
          rw [hs₂] at h₂
          obtain ⟨hc₁, hEp₁, _, _, hLead₁⟩ := auctionStep_spec H cfg st₁ m₁ t₁ hs₁
          obtain ⟨hc₂, hEp₂, _, _, hLead₂⟩ := auctionStep_spec H cfg st₂ m₂ t₂ hs₂
          simp only [auctionTurnCheck, Bool.and_eq_true] at hc₁ hc₂
          have hv₁ := hc₁.1.1.1.1.1
          have hv₂ := hc₂.1.1.1.1.1
          rw [hE, hSlot] at hv₁
          by_cases hOut : t₁.ticket.output = t₂.ticket.output
          · exact ih ts₂ m₁ m₂ f₁ f₂ (by omega) (by rw [hLead₁, hLead₂, hOut, hL]) hTail h₁ h₂
          · exact Or.inr (lavRingVerify_unique H cfg.lav cfg.ringKeys st₂.epoch t₂.slot
              t₁.ticket t₂.ticket hIdx hv₁ hv₂ hOut)

end Obend.Crypto
end
