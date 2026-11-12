module
/- Tagged threshold decryption, packed-bit openings, lattice VRF, and bonded release.
Prime-field sharing privacy is separate from the even-modulus RLWE correctness contract.
LAV uses masked DLEQ responses with rejection; uniqueness requires explicit rewinding evidence.
The SIS regime check is necessary, not sufficient, for hardness. Bonded release penalizes refusal and public
invalidity; algebraically dishonest canonical shares still require TulvaSharesValid.
auctionRun is the settlement checker; bondedAuctionRun enforces commit/open sequencing. -/
public import Obend.Crypto.FastRing
public import Obend.Crypto.Transcript
public import Obend.Crypto.SameOpening
public import Obend.Crypto.DarkBazaar
import all Obend.Crypto.FastRing
import all Obend.Crypto.Transcript
import all Obend.Crypto.SameOpening
import all Obend.Crypto.DarkBazaar
public import Init.GrindInstances.Ring.Fin
public section
namespace Obend.Crypto
open Obend.Apps.ZkNtt Obend.Crypto.Fast Obend.Digest.HashBytes Obend.Ledger
set_option autoImplicit false
private theorem emod_eq_of_sub_eq_mul {a b q c : Int} (h : a - b = q * c) : a % q = b % q := by have ha : a = b + q * c := (by omega); rw [ha, Int.add_mul_emod_self_left]
private theorem sub_eq_mul_of_emod_eq {a b q : Int} (h : a % q = b % q) : ∃ c, a - b = q * c := by
  refine ⟨a / q - b / q, ?_⟩
  have ha := Int.emod_def a q
  have hb := Int.emod_def b q
  rw [Int.mul_sub]
  omega
def encodeFields (fs : List (List UInt8)) : List UInt8 := leb128 fs.length ++ fs.flatMap encodeListField
private theorem flatMap_fields_inj (xs : List (List UInt8)) : ∀ ys : List (List UInt8), xs.length = ys.length → xs.flatMap encodeListField = ys.flatMap encodeListField → xs = ys := by
  induction xs with
  | nil => intro ys hlen _; cases ys with
    | nil => rfl
    | cons _ _ => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
    intro ys hlen h
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simp only [List.length_cons] at hlen; omega
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, htail⟩ := encodeListField_prefix_inj h
      rw [hxy, ih ys hlen' htail]
theorem encodeFields_injective {xs ys : List (List UInt8)} (h : encodeFields xs = encodeFields ys) : xs = ys := by unfold encodeFields at h; obtain ⟨hlen, hbody⟩ := leb128_prefix_inj h; exact flatMap_fields_inj xs ys hlen hbody
theorem encodeSignedIntList_injective {xs ys : List Int} (h : encodeSignedIntList xs = encodeSignedIntList ys) : xs = ys :=
  encodeSignedIntBytes_injective (by unfold encodeSignedIntBytes; rw [h])
def encodeIntRows (rows : List (List Int)) : List UInt8 := encodeFields (rows.map encodeSignedIntList)
theorem encodeIntRows_injective {xs ys : List (List Int)} (h : encodeIntRows xs = encodeIntRows ys) : xs = ys :=
  (List.map_inj_right (fun _ _ => encodeSignedIntList_injective)).mp (encodeFields_injective h)
def polyCoeffs {d : Nat} (a : FastIntPoly d) : List Int := a.coeffs.toList
theorem polyCoeffs_injective {d : Nat} {a b : FastIntPoly d} (h : polyCoeffs a = polyCoeffs b) : a = b := by
  cases a with
  | mk ca ha =>
    cases b with
    | mk cb hb =>
      have hc : ca = cb := Array.toList_inj.mp h
      subst hc
      rfl
theorem polyRows_injective {d : Nat} {u v : List (FastIntPoly d)} (h : u.map polyCoeffs = v.map polyCoeffs) : u = v :=
  (List.map_inj_right (fun _ _ => polyCoeffs_injective)).mp h
structure ExactCollision
    (H : Hash) (pre₁ pre₂ : List UInt8) : Type where
  ne : pre₁ ≠ pre₂
  digest_eq : H pre₁ = H pre₂
structure TranscriptCollision
    (H : Hash) : Type where
  pre₁ : List UInt8
  pre₂ : List UInt8
  ne : pre₁ ≠ pre₂
  digest_eq : H pre₁ = H pre₂
def ExactCollision.transcript {H : Hash} {a b : List UInt8} (w : ExactCollision
    H a b) : TranscriptCollision
      H :=
  ⟨a, b, w.ne, w.digest_eq⟩
def hash_frame_binding (H : Hash) {a₁ b₁ c₁ a₂ b₂ c₂ : List UInt8} (h : H (encodeFrameList a₁ b₁ c₁) = H (encodeFrameList a₂ b₂ c₂)) : PSum (a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂) (ExactCollision
    H (encodeFrameList a₁ b₁ c₁) (encodeFrameList a₂ b₂ c₂)) :=
  if hPre : encodeFrameList a₁ b₁ c₁ = encodeFrameList a₂ b₂ c₂ then
    .inl (encodeFrameList_injective hPre) else .inr ⟨hPre, h⟩
private theorem lavFold_lin (xs : List Nat) (r s : Int) (f g : Nat → Int) (x y : Int) : xs.foldl (fun acc j => acc + (r * f j + s * g j)) (r * x + s * y) = r * xs.foldl (fun acc j => acc + f j) x + s * xs.foldl (fun acc j => acc + g j) y := by
  induction xs generalizing x y with
  | nil => rfl
  | cons j js ih => simp only [List.foldl_cons]; rw [show r * x + s * y + (r * f j + s * g j) = r * (x + f j) + s * (y + g j) by rw [Int.mul_add, Int.mul_add]; omega]; exact ih _ _
private theorem lavSplit_lin (d k : Nat) (r s : Int) (a b c : Nat → Int) : splitConvolution (· + ·) (· - ·) (· * ·) 0 d k (fun j => r * a j + s * b j) c = r * splitConvolution (· + ·) (· - ·) (· * ·) 0 d k a c + s * splitConvolution (· + ·) (· - ·) (· * ·) 0 d k b c := by
  unfold splitConvolution
  simp only [← Array.foldl_toList, Int.sub_eq_add_neg, Int.add_mul, Int.mul_assoc, Int.neg_add, ← Int.mul_neg]
  have hz : (0 : Int) = r * 0 + s * 0 := by simp only [Int.mul_zero, Int.add_zero]
  conv => lhs; arg 2; arg 2; rw [hz]
  rw [lavFold_lin, lavFold_lin]
private theorem lavMul_lin {d : Nat} (r s : Int) (p a b c : FastIntPoly d) (h : ∀ k, p.spec k = r * a.spec k + s * b.spec k) (k : Fin d) : (negacyclicMulFast p c).spec k = r * (negacyclicMulFast a c).spec k + s * (negacyclicMulFast b c).spec k := by
  have he : (fun j : Nat => p.coeffs[j]?.getD 0) = fun j : Nat => r * a.coeffs[j]?.getD 0 + s * b.coeffs[j]?.getD 0 := by
    funext j
    if hj : j < d then
      simpa only [Sized.spec, Array.getElem?_eq_getElem (by have := p.size_eq; omega : j < p.coeffs.size), Array.getElem?_eq_getElem (by have := a.size_eq; omega : j < a.coeffs.size), Array.getElem?_eq_getElem (by have := b.size_eq; omega : j < b.coeffs.size), Option.getD_some] using h ⟨j, hj⟩
    else simp only [Array.getElem?_eq_none (by have := p.size_eq; omega : p.coeffs.size ≤ j), Array.getElem?_eq_none (by have := a.size_eq; omega : a.coeffs.size ≤ j), Array.getElem?_eq_none (by have := b.size_eq; omega : b.coeffs.size ≤ j), Option.getD_none, Int.mul_zero, Int.add_zero]
  simp only [negacyclicMulFast, Sized.spec_ofFn]; rw [he]; exact lavSplit_lin d k.val r s _ _ _
theorem negacyclicMulFast_add_left {d : Nat} (a b c : FastIntPoly d) (k : Fin d) : (negacyclicMulFast (intAdd a b) c).spec k = (negacyclicMulFast a c).spec k + (negacyclicMulFast b c).spec k := by simpa only [Int.one_mul] using lavMul_lin 1 1 (intAdd a b) a b c (fun k => by simp only [addFast_eq_spec, Int.one_mul]) k
theorem negacyclicMulFast_scale_left {d : Nat} (x : Int) (a c : FastIntPoly d) (k : Fin d) : (negacyclicMulFast (intScale x a) c).spec k = x * (negacyclicMulFast a c).spec k := by simpa only [Int.zero_mul, Int.add_zero] using lavMul_lin x 0 (intScale x a) a a c (fun k => by simp only [scaleFast_eq_spec, Int.zero_mul, Int.add_zero]) k
theorem negacyclicMulFast_sub_left {d : Nat} (a b c : FastIntPoly d) (k : Fin d) : (negacyclicMulFast (intSub a b) c).spec k = (negacyclicMulFast a c).spec k - (negacyclicMulFast b c).spec k := by simpa only [Int.one_mul, Int.neg_one_mul, Int.sub_eq_add_neg] using lavMul_lin 1 (-1) (intSub a b) a b c (fun k => by simp only [subFast_eq_spec, Int.one_mul, Int.neg_one_mul, Int.sub_eq_add_neg]) k
theorem zeroVec_spec {d : Nat} (k : Fin d) : (zeroVec d).spec k = 0 := by have h : (zeroVec d).spec = fun _ => (0 : Int) := Sized.spec_ofFn _; rw [h]
theorem negacyclicMulFast_zero_left {d : Nat} (c : FastIntPoly d) (k : Fin d) : (negacyclicMulFast (zeroVec d) c).spec k = 0 := by simpa only [Int.zero_mul, Int.add_zero] using lavMul_lin 0 0 (zeroVec d) (zeroVec d) (zeroVec d) c (fun k => by simp only [zeroVec_spec, Int.zero_mul, Int.add_zero]) k
def hornerInt : List Int → Int → Int
  | [], _ => 0
  | a :: as, x => a + x * hornerInt as x
def shamirShare {d : Nat} : List (FastIntPoly d) → Int → FastIntPoly d
  | [], _ => zeroVec d
  | a :: as, x => intAdd a (intScale x (shamirShare as x))
def quorumSum : List (Int × Int) → (Int → Int) → Int
  | [], _ => 0
  | (x, l) :: rest, g => l * g x + quorumSum rest g
def checkQuorumCoeffs (q t : Nat) (slack : Int) (quorum : List (Int × Int)) : Bool :=
  (List.range t).all fun j =>
    decide ((quorumSum quorum (fun x => x ^ j) - (if j = 0 then slack else 0)) % (q : Int) = 0)
theorem quorumSum_zero (quorum : List (Int × Int)) : quorumSum quorum (fun _ => 0) = 0 := by
  induction quorum with
  | nil => rfl
  | cons p rest ih => obtain ⟨x, l⟩ := p; simp [quorumSum, ih]
theorem quorumSum_linear (quorum : List (Int × Int)) (a : Int) (f g : Int → Int) : quorumSum quorum (fun x => a * f x + g x) = a * quorumSum quorum f + quorumSum quorum g := by
  induction quorum with
  | nil => simp [quorumSum]
  | cons p rest ih =>
    obtain ⟨x, l⟩ := p
    simp only [quorumSum, ih]
    grind
theorem quorumSum_horner_dvd (q t : Nat) (slack : Int) (quorum : List (Int × Int)) (hCheck : checkQuorumCoeffs q t slack quorum = true) : ∀ (as : List Int) (j : Nat), j + as.length ≤ t → (q : Int) ∣ quorumSum quorum (fun x => x ^ j * hornerInt as x) - (if j = 0 then slack * as.headD 0 else 0) := by
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
theorem quorum_reconstructs (q t : Nat) (slack : Int) (quorum : List (Int × Int)) (hCheck : checkQuorumCoeffs q t slack quorum = true) (as : List Int) (hLen : as.length ≤ t) : ∃ c, quorumSum quorum (hornerInt as) - slack * as.headD 0 = (q : Int) * c := by
  obtain ⟨c, hc⟩ := quorumSum_horner_dvd q t slack quorum hCheck as 0 (by omega)
  have hf : (fun x : Int => x ^ 0 * hornerInt as x) = hornerInt as := by funext x; simp
  rw [hf] at hc
  exact ⟨c, by simpa using hc⟩
theorem shamirShare_mul_spec {d : Nat} (c : FastIntPoly d) (x : Int) (k : Fin d) (as : List (FastIntPoly d)) : (negacyclicMulFast (shamirShare as x) c).spec k = hornerInt (as.map fun a => (negacyclicMulFast a c).spec k) x := by
  induction as with
  | nil => simp only [shamirShare, List.map_nil, hornerInt]; exact negacyclicMulFast_zero_left c k
  | cons a as ih =>
    simp only [shamirShare, List.map_cons, hornerInt]
    rw [negacyclicMulFast_add_left, negacyclicMulFast_scale_left, ih]
abbrev ShamirPoly (q : Nat) : Nat → Type
  | 0 => Unit
  | n + 1 => Fin q × ShamirPoly q n
def shamirPolyEval {q : Nat} [NeZero q] : {n : Nat} → ShamirPoly q n → Fin q → Fin q
  | 0, _, _ => 0
  | _ + 1, p, x => p.1 + x * shamirPolyEval p.2 x
def shamirTranslate {q : Nat} [NeZero q] : {n : Nat} → ShamirPoly q n → Fin q → ShamirPoly q n → ShamirPoly q n
  | 0, _, _, _ => ()
  | _ + 1, v, a, p => (p.1 + a * v.1, shamirTranslate v.2 a p.2)
theorem shamirTranslate_eval {q n : Nat} [NeZero q] (v p : ShamirPoly q n) (a x : Fin q) : shamirPolyEval (shamirTranslate v a p) x = shamirPolyEval p x + a * shamirPolyEval v x := by
  induction n with
  | zero => simp only [shamirPolyEval]; grind
  | succ n ih => simp only [shamirPolyEval, shamirTranslate]; rw [ih]; grind
theorem shamirTranslate_inverse {q n : Nat} [NeZero q] (v p : ShamirPoly q n) (a : Fin q) : shamirTranslate v (-a) (shamirTranslate v a p) = p := by
  induction n with
  | zero => cases p; rfl
  | succ n ih => apply Prod.ext <;> simp only [shamirTranslate]; grind; exact ih v.2 p.2
def shamirPad {q : Nat} [NeZero q] : {n : Nat} → ShamirPoly q n → ShamirPoly q (n + 1)
  | 0, _ => (0, ())
  | _ + 1, p => (p.1, shamirPad p.2)
theorem shamirPad_eval {q n : Nat} [NeZero q] (p : ShamirPoly q n) (x : Fin q) : shamirPolyEval (shamirPad p) x = shamirPolyEval p x := by
  induction n with
  | zero => simp only [shamirPad, shamirPolyEval]; grind
  | succ n ih =>
    change p.1 + x * shamirPolyEval (shamirPad p.2) x = p.1 + x * shamirPolyEval p.2 x
    rw [ih]
def shamirExtend {q : Nat} [NeZero q] : {n m : Nat} → n ≤ m → ShamirPoly q n → ShamirPoly q m
  | 0, 0, _, _ => ()
  | 0, m + 1, _, _ => (0, shamirExtend (Nat.zero_le m) ())
  | _n + 1, _m + 1, h, p => (p.1, shamirExtend (Nat.le_of_succ_le_succ h) p.2)
theorem shamirExtend_eval {q n m : Nat} [NeZero q] (h : n ≤ m) (p : ShamirPoly q n) (x : Fin q) : shamirPolyEval (shamirExtend h p) x = shamirPolyEval p x := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n; rfl
  | succ m ih => cases n with
    | zero => simp only [shamirExtend, shamirPolyEval]; rw [ih]; simp only [shamirPolyEval]; grind
    | succ n => simp only [shamirExtend, shamirPolyEval]; rw [ih]
def shamirSeparator {q : Nat} [NeZero q] : (C : List (Fin q)) → ShamirPoly q (C.length + 1)
  | [] => (1, ())
  | c :: cs => shamirTranslate (0, shamirSeparator cs) (-(c ^ (q - 2))) (shamirPad (shamirSeparator cs))
theorem shamirFin_inv {q : Nat} [NeZero q] (hq : IsPrimeNat q) (c : Fin q) (hc : c ≠ 0) : c * c ^ (q - 2) = 1 := by
  have hn : ¬ q ∣ c.val := by
    intro hd
    have hz : c.val = 0 := Nat.eq_zero_of_dvd_of_lt hd c.isLt
    exact hc (Fin.ext (by simpa using hz))
  have he : q - 2 + 1 = q - 1 := by have := hq.1; omega
  apply Fin.ext
  simp only [Fin.val_mul, Fin.val_pow]
  rw [Nat.mul_mod_mod, Nat.mul_comm, ← Nat.pow_succ, show (q - 2).succ = q - 1 from he, hq.pow_sub_one_mod hn]
  exact (Nat.mod_eq_of_lt hq.1).symm
theorem shamirSeparator_spec {q : Nat} [NeZero q] (hq : IsPrimeNat q) (C : List (Fin q)) (hC : ∀ c ∈ C, c ≠ 0) : shamirPolyEval (shamirSeparator C) 0 = 1 ∧ ∀ x ∈ C, shamirPolyEval (shamirSeparator C) x = 0 := by
  induction C with
  | nil => simp only [shamirSeparator, shamirPolyEval, List.not_mem_nil, false_implies, implies_true, and_true]; grind
  | cons c cs ih =>
    obtain ⟨hz, hr⟩ := ih (fun x hx => hC x (by simp [hx]))
    have hinv := shamirFin_inv hq c (hC c (by simp))
    have he (x : Fin q) : shamirPolyEval (shamirSeparator (c :: cs)) x =
        shamirPolyEval (shamirSeparator cs) x +
          (-(c ^ (q - 2))) * (0 + x * shamirPolyEval (shamirSeparator cs) x) := by
      change shamirPolyEval (shamirTranslate _ _ _) x = _
      rw [shamirTranslate_eval, shamirPad_eval]; rfl
    constructor
    · rw [he, hz]; grind
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [he]; grind only
      · rw [he, hr x hx]; grind only
/-- Translation is an explicit bijection between secret fibers, preserving the exact coalition view.
No distribution assumption is hidden: uniform coefficient vectors are transported by this bijection. -/
theorem shamir_below_threshold_uniform_privacy {q threshold : Nat} [NeZero q] (hq : IsPrimeNat q) (C : List (Fin q)) (hC : ∀ c ∈ C, c ≠ 0) (hsmall : C.length < threshold) (sk₀ sk₁ : Fin q) : let P := fun s => {p : ShamirPoly q threshold // shamirPolyEval p 0 = s}
    ∃ (F : P sk₀ → P sk₁) (G : P sk₁ → P sk₀),
      (∀ p, G (F p) = p) ∧ (∀ p, F (G p) = p) ∧
      ∀ p, C.map (shamirPolyEval (F p).val) = C.map (shamirPolyEval p.val) := by
  let v := shamirExtend (show C.length + 1 ≤ threshold by omega) (shamirSeparator C)
  have hv0 : shamirPolyEval v 0 = 1 := by rw [shamirExtend_eval]; exact (shamirSeparator_spec hq C hC).1
  have hvC (x : Fin q) (hx : x ∈ C) : shamirPolyEval v x = 0 := by
    rw [shamirExtend_eval]; exact (shamirSeparator_spec hq C hC).2 x hx
  let F : {p : ShamirPoly q threshold // shamirPolyEval p 0 = sk₀} →
      {p : ShamirPoly q threshold // shamirPolyEval p 0 = sk₁} := fun p =>
    ⟨shamirTranslate v (sk₁ - sk₀) p.val, by rw [shamirTranslate_eval, p.property, hv0]; grind⟩
  let G : {p : ShamirPoly q threshold // shamirPolyEval p 0 = sk₁} →
      {p : ShamirPoly q threshold // shamirPolyEval p 0 = sk₀} := fun p =>
    ⟨shamirTranslate v (-(sk₁ - sk₀)) p.val, by rw [shamirTranslate_eval, p.property, hv0]; grind⟩
  refine ⟨F, G, ?_, ?_, ?_⟩
  · intro p; apply Subtype.ext; exact shamirTranslate_inverse v p.val (sk₁ - sk₀)
  · intro p; apply Subtype.ext
    have he : sk₁ - sk₀ = -(-(sk₁ - sk₀)) := by grind
    change shamirTranslate v (sk₁ - sk₀) (shamirTranslate v (-(sk₁ - sk₀)) p.val) = p.val
    conv => lhs; arg 2; rw [he]
    exact shamirTranslate_inverse v p.val (-(sk₁ - sk₀))
  · intro p; apply List.map_congr_left; intro x hx
    change shamirPolyEval (shamirTranslate v (sk₁ - sk₀) p.val) x = _
    rw [shamirTranslate_eval, hvC x hx]; grind
def tulvaTagDomain : List UInt8 := [84, 85, 76, 86, 65, 45, 84, 65, 71]
def ciphertextBytes {d : Nat} (ct : RlweCiphertext d) : List UInt8 := encodeIntRows [polyCoeffs ct.c0, polyCoeffs ct.c1]
theorem ciphertextBytes_injective {d : Nat} {ct₁ ct₂ : RlweCiphertext d} (h : ciphertextBytes ct₁ = ciphertextBytes ct₂) : ct₁ = ct₂ := by
  have hr := encodeIntRows_injective h
  simp only [List.cons.injEq, and_true] at hr
  cases ct₁; cases ct₂
  simp only [RlweCiphertext.mk.injEq]
  exact ⟨polyCoeffs_injective hr.1, polyCoeffs_injective hr.2⟩
def tulvaTag (H : Hash) (context : List UInt8) {d : Nat} (ct : RlweCiphertext d) : List UInt8 := H (encodeFrameList tulvaTagDomain context (ciphertextBytes ct))
def tulvaTag_binds_query (H : Hash) (ctx₁ ctx₂ : List UInt8) {d : Nat} (ct₁ ct₂ : RlweCiphertext d) (h : tulvaTag H ctx₁ ct₁ = tulvaTag H ctx₂ ct₂) : PSum (ctx₁ = ctx₂ ∧ ct₁ = ct₂) (ExactCollision
    H (encodeFrameList tulvaTagDomain ctx₁ (ciphertextBytes ct₁)) (encodeFrameList tulvaTagDomain ctx₂ (ciphertextBytes ct₂))) := by
  rcases hash_frame_binding H h with ⟨_, hctx, hct⟩ | hcol
  · exact PSum.inl ⟨hctx, ciphertextBytes_injective hct⟩
  · exact PSum.inr hcol
structure TulvaShare (d : Nat) where
  point : Int
  tag : List UInt8
  sharePoly : FastIntPoly d
  deriving DecidableEq
def tulvaPartialDecrypt (H : Hash) (pp : RlweParams) (context : List UInt8) (ct : RlweCiphertext pp.d) (point : Int) (skShare eSmudge : FastIntPoly pp.d) : TulvaShare pp.d :=
  { point := point
    tag := tulvaTag H context ct
    sharePoly := (computePartialShare pp point.toNat skShare ct.c1 eSmudge).sharePoly }
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
def tulvaQuorum {d : Nat} : List (Int × TulvaShare d) → List (Int × Int)
  | [] => []
  | e :: es => (e.2.point, e.1) :: tulvaQuorum es
def tulvaWeightedSum {d : Nat} : List (Int × TulvaShare d) → FastIntPoly d
  | [] => zeroVec d
  | e :: es => intAdd (intScale e.1 e.2.sharePoly) (tulvaWeightedSum es)
def lambdaWeight {d : Nat} : List (Int × TulvaShare d) → Nat
  | [] => 0
  | e :: es => e.1.natAbs + lambdaWeight es
def tulvaNoiseTotal (prof : TulvaProfile) {d : Nat} (entries : List (Int × TulvaShare d)) : Nat := prof.slack * prof.encNoiseBound + lambdaWeight entries * prof.smudgeBound
def tulvaCheck (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) : Bool :=
  prof.params.wfB && decide (0 < prof.slack) &&
  checkSmudgeSafe prof.encNoiseBound prof.smudgeBound prof.secBits &&
  entries.all (fun e => decide (e.2.tag = tulvaTag H context ct)) &&
  checkQuorumCoeffs prof.params.q prof.threshold prof.slack (tulvaQuorum entries) &&
  decide (tulvaNoiseTotal prof entries < prof.params.noiseCap)
def tulvaRefusalOf (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) : TulvaRefusal :=
  if !(prof.params.wfB && decide (0 < prof.slack)) then .invalidParams
  else if !checkSmudgeSafe prof.encNoiseBound prof.smudgeBound prof.secBits then .unsmudged
  else if !entries.all (fun e => decide (e.2.tag = tulvaTag H context ct)) then .tagMismatch
  else if !checkQuorumCoeffs prof.params.q prof.threshold prof.slack (tulvaQuorum entries) then
    .badCoefficients
  else .noiseBudgetExceeded (tulvaNoiseTotal prof entries) prof.params.noiseCap
def tulvaDecode (prof : TulvaProfile) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) : FastIntPoly prof.params.d :=
  let phase := reducePolyMod prof.params.q
    (intAdd (intScale (prof.slack : Int) ct.c0) (tulvaWeightedSum entries))
  Sized.ofFn fun i => rlweDecodeSignedCoeff prof.params (phase.spec i) / (prof.slack : Int)
def tulvaCombine (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) : Except TulvaRefusal (FastIntPoly prof.params.d) :=
  if tulvaCheck H prof context ct entries then .ok (tulvaDecode prof ct entries)
  else .error (tulvaRefusalOf H prof context ct entries)
theorem tulvaCombine_ok_iff (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) (mOut : FastIntPoly prof.params.d) : tulvaCombine H prof context ct entries = .ok mOut ↔ tulvaCheck H prof context ct entries = true ∧ tulvaDecode prof ct entries = mOut := by
  unfold tulvaCombine
  constructor
  · intro h
    split at h
    · rename_i hc; exact ⟨hc, Except.ok.inj h⟩
    · cases h
  · rintro ⟨hc, hd⟩
    simp only [hc, ↓reduceIte, hd]
def TulvaSharesValid (pp : RlweParams) (c1 : FastIntPoly pp.d) (smudgeBound : Nat) (poly : List (FastIntPoly pp.d)) : List (Int × TulvaShare pp.d) → List (FastIntPoly pp.d) → Prop
  | [], [] => True
  | e :: es, n :: ns =>
    (∀ i : Fin pp.d, e.2.sharePoly.spec i % (pp.q : Int) =
        ((negacyclicMulFast (shamirShare poly e.2.point) c1).spec i + n.spec i) % (pp.q : Int)) ∧
    normInfFast n.coeffs ≤ smudgeBound ∧
    TulvaSharesValid pp c1 smudgeBound poly es ns
  | _, _ => False
theorem tulvaPartialDecrypt_valid (H : Hash) (pp : RlweParams) (context : List UInt8) (ct : RlweCiphertext pp.d) (point : Int) (poly : List (FastIntPoly pp.d)) (eSmudge : FastIntPoly pp.d) (i : Fin pp.d) : (tulvaPartialDecrypt H pp context ct point (shamirShare poly point) eSmudge).sharePoly.spec i % (pp.q : Int) = ((negacyclicMulFast (shamirShare poly point) ct.c1).spec i + eSmudge.spec i) % (pp.q : Int) := by
  simp only [tulvaPartialDecrypt, computePartialShare, reducePolyMod_spec, addFast_eq_spec]
  exact Int.emod_emod _ _
theorem tulvaWeightedSum_phase (pp : RlweParams) (c1 : FastIntPoly pp.d) (S : Nat) (poly : List (FastIntPoly pp.d)) (i : Fin pp.d) : ∀ (entries : List (Int × TulvaShare pp.d)) (noises : List (FastIntPoly pp.d)), TulvaSharesValid pp c1 S poly entries noises → ∃ eta c : Int, eta.natAbs ≤ lambdaWeight entries * S ∧ (tulvaWeightedSum entries).spec i - (quorumSum (tulvaQuorum entries) (hornerInt (poly.map fun a => (negacyclicMulFast a c1).spec i)) + eta) = (pp.q : Int) * c := by
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
theorem tulvaCombine_recovers_plaintext (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) (sk : FastIntPoly prof.params.d) (higher noises : List (FastIntPoly prof.params.d)) (m eEnc mOut : FastIntPoly prof.params.d) (hDec : tulvaCombine H prof context ct entries = .ok mOut) (hDeg : higher.length + 1 ≤ prof.threshold) (hEnc : RlweEncryptsWithError prof.params sk ct m eEnc) (hEncNorm : normInfFast eEnc.coeffs ≤ prof.encNoiseBound) (hShares : TulvaSharesValid prof.params ct.c1 prof.smudgeBound (sk :: higher) entries noises) (hRoom : ∀ i : Fin prof.params.d, -prof.params.halfT ≤ (prof.slack : Int) * m.spec i ∧ (prof.slack : Int) * m.spec i < prof.params.halfT) : mOut = m ∧ SmudgeSafe prof.encNoiseBound prof.smudgeBound prof.secBits ∧ tulvaNoiseTotal prof entries < prof.params.noiseCap := by
  obtain ⟨hChk, hOut⟩ := (tulvaCombine_ok_iff H prof context ct entries mOut).mp hDec
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  obtain ⟨⟨⟨⟨⟨hwf, hSlack⟩, hSm⟩, _⟩, hQ⟩, hTot⟩ := hChk
  refine ⟨?_, (checkSmudgeSafe_iff _ _ _).mp hSm, hTot⟩
  subst hOut
  apply Sized.ext; funext i
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
theorem tulva_smudge_no_wraparound (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) (h : tulvaCheck H prof context ct entries = true) (e eta : Int) (he : e.natAbs ≤ prof.encNoiseBound) (hEta : eta.natAbs ≤ lambdaWeight entries * prof.smudgeBound) : ((prof.slack : Int) * e + eta).natAbs ≤ tulvaNoiseTotal prof entries ∧ tulvaNoiseTotal prof entries < prof.params.q / (2 * prof.params.t) ∧ - (prof.params.q : Int) < (prof.slack : Int) * e + eta ∧ (prof.slack : Int) * e + eta < prof.params.q := by
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmul := Nat.mul_le_mul_left prof.slack he
  have hadd := Int.natAbs_add_le ((prof.slack : Int) * e) eta
  have hm : ((prof.slack : Int) * e).natAbs = prof.slack * e.natAbs := by
    simp [Int.natAbs_mul]
  have hcap := Nat.div_le_self prof.params.q (2 * prof.params.t)
  simp only [tulvaNoiseTotal, RlweParams.noiseCap] at *
  omega
theorem tulvaCombine_refuses_unsmudged (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) (hZero : prof.smudgeBound = 0) (mOut : FastIntPoly prof.params.d) : tulvaCombine H prof context ct entries ≠ .ok mOut := by
  intro h
  obtain ⟨hChk, _⟩ := (tulvaCombine_ok_iff H prof context ct entries mOut).mp h
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  have hSm := (checkSmudgeSafe_iff _ _ _).mp hChk.1.1.1.2
  rw [hZero] at hSm
  exact smudgeSafe_refuses_unsmudged _ _ hSm
theorem tulvaCombine_refuses_noise_overflow (H : Hash) (prof : TulvaProfile) (context : List UInt8) (ct : RlweCiphertext prof.params.d) (entries : List (Int × TulvaShare prof.params.d)) (hOver : prof.params.noiseCap ≤ tulvaNoiseTotal prof entries) (mOut : FastIntPoly prof.params.d) : tulvaCombine H prof context ct entries ≠ .ok mOut := by
  intro h
  obtain ⟨hChk, _⟩ := (tulvaCombine_ok_iff H prof context ct entries mOut).mp h
  simp only [tulvaCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  omega
theorem tulva_unsmudged_boundary_oracle_leaks (pp : RlweParams) (hwf : pp.wfB = true) (m eIn eOut : Int) (hmLo : -pp.halfT ≤ m) (hmHi : m + 1 < pp.halfT) (hIn : eIn.natAbs < pp.noiseCap) (hOutLo : (pp.noiseCap : Int) < eOut) (hOutHi : eOut < 3 * (pp.noiseCap : Int)) : rlweDecodeSignedCoeff pp (pp.delta * m + eIn) = m ∧ rlweDecodeSignedCoeff pp (pp.delta * m + eOut) = m + 1 := by
  obtain ⟨_, _, _, _, _, hDelta, _⟩ := rlweParams_identities pp hwf
  refine ⟨rlweDecodeSignedCoeff_exact pp _ m eIn hwf rfl hmLo (by omega) hIn, ?_⟩
  have hEq : pp.delta * m + eOut = pp.delta * (m + 1) + (eOut - 2 * (pp.noiseCap : Int)) := by
    rw [Int.mul_add, hDelta]
    omega
  exact rlweDecodeSignedCoeff_exact pp _ (m + 1) (eOut - 2 * (pp.noiseCap : Int)) hwf
    (by rw [hEq]) (by omega) hmHi (by omega)
def smudgeSupport (S : Nat) : List Int := (List.range (2 * S + 1)).map fun (k : Nat) => (k : Int) - (S : Int)
def smudgeUncoupled (S : Nat) (shift : Int) : List Int := (smudgeSupport S).filter fun e => !decide (-(S : Int) ≤ e + shift ∧ e + shift ≤ S)
theorem mem_smudgeSupport (S : Nat) (e : Int) : e ∈ smudgeSupport S ↔ -(S : Int) ≤ e ∧ e ≤ S := by
  unfold smudgeSupport
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have := List.mem_range.mp hk
    omega
  · intro h
    exact ⟨(e + S).toNat, List.mem_range.mpr (by omega), by omega⟩
theorem coupled_of_not_uncoupled {S : Nat} {shift e : Int} (hs : e ∈ smudgeSupport S) (hn : e ∉ smudgeUncoupled S shift) : -(S : Int) ≤ e + shift ∧ e + shift ≤ S := by
  unfold smudgeUncoupled at hn
  rw [List.mem_filter] at hn
  by_cases hb : -(S : Int) ≤ e + shift ∧ e + shift ≤ S
  · exact hb
  · have hd : decide (-(S : Int) ≤ e + shift ∧ e + shift ≤ S) = false := decide_eq_false hb
    exact absurd ⟨hs, by rw [hd]; rfl⟩ hn
private theorem rangeFilter_length_le (p : Nat → Bool) (lo hi : Nat) : ∀ n, (∀ k, k < n → p k = true → k < lo ∨ hi ≤ k) → ((List.range n).filter p).length ≤ min n lo + (n - hi) := by
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
theorem smudgeUncoupled_length_le (S : Nat) (shift : Int) : (smudgeUncoupled S shift).length ≤ shift.natAbs := by
  unfold smudgeUncoupled smudgeSupport
  rw [List.filter_map, List.length_map]
  refine Nat.le_trans
    (rangeFilter_length_le _ (-shift).toNat (2 * S + 1 - shift.toNat) (2 * S + 1) ?_) (by omega)
  intro k _ hp
  simp at hp
  omega
theorem tulva_smudge_shift_overlap_bound (S B : Nat) (shift : Int) (h : shift.natAbs ≤ B) : 2 * S + 1 - shift.natAbs ≤ ((smudgeSupport S).filter fun e => decide (-(S : Int) ≤ e + shift ∧ e + shift ≤ S)).length ∧ ∀ y : Int, -(S : Int) + B ≤ y → y ≤ (S : Int) - B → ∃ e ∈ smudgeSupport S, e + shift = y := by
  have splitCount (xs : List Int) (p : Int → Bool) :
      (xs.filter p).length + (xs.filter fun x => !p x).length = xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => cases hx : p x <;> simp only [List.filter_cons, hx, Bool.not_false, Bool.not_true, List.length_cons, Bool.false_eq_true, reduceIte] <;> omega
  have hc := splitCount (smudgeSupport S)
    (fun e : Int => decide (-(S : Int) ≤ e + shift ∧ e + shift ≤ S))
  have hu := smudgeUncoupled_length_le S shift
  simp only [smudgeUncoupled] at hu
  have hs : (smudgeSupport S).length = 2 * S + 1 := by simp [smudgeSupport]
  refine ⟨by omega, ?_⟩
  intro y hlo hhi
  exact ⟨y - shift, (mem_smudgeSupport _ _).mpr (by omega), by omega⟩
theorem smudgeUncoupled_unsmudged (shift : Int) (h : shift ≠ 0) : smudgeUncoupled 0 shift = smudgeSupport 0 := by
  simp [smudgeUncoupled, smudgeSupport]
  omega
theorem tulva_smudge_floods_noise {noiseBound smudgeBound secBits : Nat} (h : SmudgeSafe noiseBound smudgeBound secBits) (shift : Int) (hShift : shift.natAbs ≤ noiseBound) : (smudgeUncoupled smudgeBound shift).length * 2 ^ secBits ≤ smudgeBound ∧ (smudgeSupport smudgeBound).length = 2 * smudgeBound + 1 := by
  refine ⟨?_, by simp [smudgeSupport]⟩
  have hLen := Nat.le_trans (smudgeUncoupled_length_le smudgeBound shift) hShift
  exact Nat.le_trans (Nat.mul_le_mul_right _ hLen) h.2.2
theorem tulvaShare_explained_by_other_key (pp : RlweParams) (g : Nat) (sk sk' c1 e : FastIntPoly pp.d) (S : Nat) (hCoupled : ∀ i : Fin pp.d, e.spec i ∈ smudgeSupport S ∧ e.spec i ∉ smudgeUncoupled S ((negacyclicMulFast sk c1).spec i - (negacyclicMulFast sk' c1).spec i)) : ∃ e' : FastIntPoly pp.d, normInfFast e'.coeffs ≤ S ∧ computePartialShare pp g sk' c1 e' = computePartialShare pp g sk c1 e := by
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
def psiZ : List Int → Int
  | [] => 0
  | c :: cs => c + 2 * psiZ cs
@[expose] def psiFp (row : List Int) : Goldilocks := goldOfInt (psiZ row)
def psiRq (q : Nat) : List Int → Int
  | [] => 0
  | c :: cs => (c + 2 * psiRq q cs) % (q : Int)
def checkBooleanRow (row : List Int) : Bool := row.all fun c => decide (c * (1 - c) = 0)
theorem boolean_cell_iff (c : Int) : c * (1 - c) = 0 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    rcases Int.mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (h | h) <;> rw [h] <;> rfl
theorem psiFp_eq_goldOfInt (row : List Int) : psiFp row = goldOfInt (psiZ row) := rfl
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
theorem psiZ_range (row : List Int) (hB : checkBooleanRow row = true) : 0 ≤ psiZ row ∧ psiZ row < ((2 ^ row.length : Nat) : Int) := by
  induction row with
  | nil => exact ⟨by decide, by decide⟩
  | cons c cs ih =>
    simp only [checkBooleanRow, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨h0, h1⟩ := ih hB.2
    have hc := (boolean_cell_iff c).mp hB.1
    simp only [psiZ, List.length_cons, Nat.pow_succ]
    constructor <;> omega
theorem psiZ_eq_bitsToNat (row : List Int) (hB : checkBooleanRow row = true) : psiZ row = ((bitsToNat (row.map fun c => decide (c = 1)) : Nat) : Int) := by
  induction row with
  | nil => simp [psiZ, bitsToNat]
  | cons c cs ih =>
    simp only [checkBooleanRow, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hB
    have hih := ih hB.2
    rcases (boolean_cell_iff c).mp hB.1 with h | h
    · subst h; simp [psiZ, bitsToNat, hih]
    · subst h; simp [psiZ, bitsToNat, hih]
def bitzOrderWitness (qtyRow totalRow : List Int) (salt : GoldilocksExt2) : OrderBitWitness :=
  { qtyBits := qtyRow.map fun c => decide (c = 1)
    totalBits := totalRow.map fun c => decide (c = 1)
    salt := salt }
theorem bitzOrderWitness_opens (qtyRow totalRow : List Int) (salt : GoldilocksExt2) (hq : checkBooleanRow qtyRow = true) (ht : checkBooleanRow totalRow = true) : (((bitzOrderWitness qtyRow totalRow salt).qty : Nat) : Int) = psiZ qtyRow ∧ (((bitzOrderWitness qtyRow totalRow salt).total : Nat) : Int) = psiZ totalRow :=
  ⟨(psiZ_eq_bitsToNat qtyRow hq).symm, (psiZ_eq_bitsToNat totalRow ht).symm⟩
def bitzDomain : List UInt8 := [66, 73, 84, 90]
def bitzCommit (H : Hash) (width : Nat) (rows : List (List Int)) : List UInt8 := H (encodeFrameList bitzDomain (leb128 width) (encodeIntRows rows))
def bitzCommit_binding (H : Hash) (w₁ w₂ : Nat) (rows₁ rows₂ : List (List Int)) (h : bitzCommit H w₁ rows₁ = bitzCommit H w₂ rows₂) : PSum (w₁ = w₂ ∧ rows₁ = rows₂) (ExactCollision
    H (encodeFrameList bitzDomain (leb128 w₁) (encodeIntRows rows₁)) (encodeFrameList bitzDomain (leb128 w₂) (encodeIntRows rows₂))) := by
  rcases hash_frame_binding H h with ⟨_, hw, hrows⟩ | hcol
  · exact PSum.inl ⟨(leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hw)).1,
      encodeIntRows_injective hrows⟩
  · exact PSum.inr hcol
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
def bitzVerify (H : Hash) (q width : Nat) (commitment : List UInt8) (rows : List (List Int)) (claims : List BitzClaim) : Bool :=
  decide (bitzCommit H width rows = commitment) && decide (2 ^ width ≤ q) &&
    decide (2 ^ width ≤ goldilocksPrime) && bitzRowsOk q width rows claims
theorem bitzRow_certified (q width : Nat) (row : List Int) (cl : BitzClaim) (hq : 2 ^ width ≤ q) (hp : 2 ^ width ≤ goldilocksPrime) (hLen : row.length = width) (hBool : checkBooleanRow row = true) (hRq : psiRq q row = cl.rq) (hFp : psiFp row = cl.fp) : ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n := by
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
theorem bitzRowsOk_certified (q width : Nat) (hq : 2 ^ width ≤ q) (hp : 2 ^ width ≤ goldilocksPrime) : ∀ (rows : List (List Int)) (claims : List BitzClaim), bitzRowsOk q width rows claims = true → rows.length = claims.length ∧ ∀ row cl, (row, cl) ∈ rows.zip claims → ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n := by
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
      refine ⟨by simp only [List.length_cons, hlen], ?_⟩
      intro row cl hm
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨hr, hc⟩ | hm
      · rw [hr, hc]; exact bitzRow_certified q width r c hq hp hLen hBool hRq hFp
      · exact hall row cl hm
def bitz_sameOpening_and_free_range_sound (H : Hash) (q width : Nat) (commitment : List UInt8) (rows : List (List Int)) (claims : List BitzClaim) (h : bitzVerify H q width commitment rows claims = true) : PProd (rows.length = claims.length ∧ ∀ row cl, (row, cl) ∈ rows.zip claims → ∃ n : Nat, n < 2 ^ width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n) (∀ rows', bitzCommit H width rows' = commitment → PSum (rows' = rows) (ExactCollision
    H (encodeFrameList bitzDomain (leb128 width) (encodeIntRows rows')) (encodeFrameList bitzDomain (leb128 width) (encodeIntRows rows)))) := by
  simp only [bitzVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hCom, hq⟩, hp⟩, hRows⟩ := h
  refine ⟨bitzRowsOk_certified q width hq hp rows claims hRows, ?_⟩
  intro rows' h'
  cases bitzCommit_binding H width width rows' rows (h'.trans hCom.symm) with
  | inl hr => exact .inl hr.2
  | inr hc => exact .inr hc
theorem bitzVerify_complete (H : Hash) (q width : Nat) (rows : List (List Int)) (hq : 2 ^ width ≤ q) (hp : 2 ^ width ≤ goldilocksPrime) (hRows : ∀ row ∈ rows, row.length = width ∧ checkBooleanRow row = true) : bitzVerify H q width (bitzCommit H width rows) rows (rows.map fun r => ⟨psiRq q r, psiFp r⟩) = true := by
  have hOk : bitzRowsOk q width rows (rows.map fun r => ⟨psiRq q r, psiFp r⟩) = true := by
    induction rows with
    | nil => rfl
    | cons r rs ih =>
      have hr := hRows r (by simp)
      have hih := ih (fun row hrow => hRows row (List.mem_cons_of_mem _ hrow))
      simp [bitzRowsOk, hr.1, hr.2, hih]
  simp [bitzVerify, hq, hp, hOk]
def bitzPlainVec (d : Nat) (claims : List BitzClaim) : FastIntPoly d := Sized.ofFn fun i => ((claims[i.val]?).map (·.rq)).getD 0
structure LavParams (d : Nat) where
  q : Nat
  p : Nat
  beta : Nat
  cMax : Nat
  gamma : Nat
  cols : Nat
  outRows : Nat
  A : List (List (FastIntPoly d))
def LavParams.zBound {d : Nat} (pp : LavParams d) : Nat := pp.gamma - pp.cMax * pp.beta
def LavParams.sisBound {d : Nat} (pp : LavParams d) : Nat := 4 * pp.cMax * pp.zBound
def LavParams.wfB {d : Nat} (pp : LavParams d) : Bool :=
  decide (2 < pp.q ∧ (∀ n ∈ List.range pp.q, 1 < n → pp.q % n ≠ 0) ∧
    0 < pp.A.length ∧ 0 < pp.cols ∧ 0 < pp.beta ∧
    (∀ row ∈ pp.A, row.length = pp.cols) ∧ 1 < pp.cMax ∧ pp.cMax < pp.q ∧
    pp.cMax * pp.beta < pp.gamma ∧ 2 * pp.sisBound < pp.q ∧
    (2 * pp.sisBound + 1) ^ pp.cols < pp.q ^ pp.A.length)
theorem LavParams.prime {d : Nat} (pp : LavParams d) (h : pp.wfB = true) : IsPrimeNat pp.q := by
  have h := of_decide_eq_true h
  have hpos : 0 < pp.q := Nat.lt_trans (by decide : 0 < 2) h.1
  refine ⟨Nat.le_of_lt h.1, fun n hn => ?_⟩
  have hb := Nat.le_of_dvd hpos hn
  if he : n = pp.q then exact .inr he else
    have hl : n < pp.q := Nat.lt_of_le_of_ne hb he
    have hn0 : n ≠ 0 := by intro e; subst n; exact (Nat.ne_of_gt hpos) (Nat.zero_dvd.mp hn)
    have hn1 : n ≤ 1 := Nat.le_of_not_gt (fun h1 => h.2.1 n (List.mem_range.mpr hl) h1 (Nat.mod_eq_zero_of_dvd hn))
    exact .inl (Nat.le_antisymm hn1 (Nat.pos_of_ne_zero hn0))
def rowDot {d : Nat} : List (FastIntPoly d) → List (FastIntPoly d) → FastIntPoly d
  | [], _ => zeroVec d
  | _ :: _, [] => zeroVec d
  | z :: zs, a :: as => intAdd (negacyclicMulFast z a) (rowDot zs as)
def lavVecSub {d : Nat} : List (FastIntPoly d) → List (FastIntPoly d) → List (FastIntPoly d)
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => intSub a b :: lavVecSub as bs
theorem lavVecSub_length {d : Nat} (a b : List (FastIntPoly d)) (h : a.length = b.length) : (lavVecSub a b).length = a.length := by
  induction a generalizing b with
  | nil => simp [lavVecSub]
  | cons a as ih =>
    cases b with
    | nil => cases h
    | cons b bs => simp only [lavVecSub, List.length_cons, ih bs (Nat.succ.inj h)]
theorem rowDot_sub_spec {d : Nat} (k : Fin d) : ∀ (z₁ z₂ row : List (FastIntPoly d)), z₁.length = z₂.length → (rowDot (lavVecSub z₁ z₂) row).spec k = (rowDot z₁ row).spec k - (rowDot z₂ row).spec k := by
  intro z₁
  induction z₁ with
  | nil =>
    intro z₂ row hl
    cases z₂ with
    | nil => simp [lavVecSub, rowDot, zeroVec_spec]
    | cons _ _ => cases hl
  | cons a as ih =>
    intro z₂ row hl
    cases z₂ with
    | nil => cases hl
    | cons b bs =>
      cases row with
      | nil => simp [lavVecSub, rowDot, zeroVec_spec]
      | cons r rs =>
        have hl' : as.length = bs.length := by exact Nat.succ.inj hl
        simp only [lavVecSub, rowDot, addFast_eq_spec]
        rw [negacyclicMulFast_sub_left, ih bs rs hl']
        omega
theorem lavVecSub_short {d : Nat} (beta : Nat) : ∀ (z₁ z₂ : List (FastIntPoly d)), (∀ a ∈ z₁, normInfFast a.coeffs ≤ beta) → (∀ b ∈ z₂, normInfFast b.coeffs ≤ beta) → ∀ c ∈ lavVecSub z₁ z₂, normInfFast c.coeffs ≤ 2 * beta := by
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
theorem lavVecSub_nonzero {d : Nat} : ∀ (z₁ z₂ : List (FastIntPoly d)), z₁.length = z₂.length → z₁ ≠ z₂ → ∃ a ∈ lavVecSub z₁ z₂, a ≠ zeroVec d := by
  intro z₁
  induction z₁ with
  | nil =>
    intro z₂ hl hne
    cases z₂ with
    | nil => exact absurd rfl hne
    | cons _ _ => cases hl
  | cons a as ih =>
    intro z₂ hl hne
    cases z₂ with
    | nil => cases hl
    | cons b bs =>
      by_cases hab : a = b
      · have hne' : as ≠ bs := fun h => hne (by rw [hab, h])
        obtain ⟨c, hc, hcz⟩ := ih bs (by exact Nat.succ.inj hl) hne'
        exact ⟨c, by simp [lavVecSub, hc], hcz⟩
      · refine ⟨intSub a b, by simp [lavVecSub], ?_⟩
        intro hz
        apply hab
        apply Sized.ext
        funext i
        have hi := congrArg (fun p => p.spec i) hz
        simp [zeroVec] at hi
        omega
def lavLin {d : Nat} (a : Int) (x : List (FastIntPoly d)) (b : Int) (y : List (FastIntPoly d)) : List (FastIntPoly d) := x.zipWith (fun u v => intAdd (intScale a u) (intScale b v)) y
theorem lavLin_length {d : Nat} (a b : Int) (x y : List (FastIntPoly d)) (h : x.length = y.length) : (lavLin a x b y).length = x.length := by simp [lavLin, h]
theorem rowDot_lin {d : Nat} (a b : Int) (x y row : List (FastIntPoly d)) (h : x.length = y.length) (k : Fin d) : (rowDot (lavLin a x b y) row).spec k = a * (rowDot x row).spec k + b * (rowDot y row).spec k := by
  induction x generalizing y row with
  | nil => have hy : y = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm); subst y; simp [lavLin, rowDot, zeroVec_spec]
  | cons u us ih =>
    cases y with
    | nil => simp at h
    | cons v vs => cases row with
      | nil => simp [lavLin, rowDot, zeroVec_spec]
      | cons r rs =>
        have ht : us.length = vs.length := by simpa using h
        simp only [lavLin, List.zipWith_cons_cons, rowDot, addFast_eq_spec]
        rw [negacyclicMulFast_add_left, negacyclicMulFast_scale_left, negacyclicMulFast_scale_left]
        have hih := ih vs rs ht
        unfold lavLin at hih
        rw [hih]
        rw [Int.mul_add, Int.mul_add]; omega
theorem lavLin_short {d : Nat} (a b : Int) (x y : List (FastIntPoly d)) (X Y : Nat) (hx : ∀ u ∈ x, normInfFast u.coeffs ≤ X) (hy : ∀ v ∈ y, normInfFast v.coeffs ≤ Y) : ∀ w ∈ lavLin a x b y, normInfFast w.coeffs ≤ a.natAbs * X + b.natAbs * Y := by
  induction x generalizing y with
  | nil => simp [lavLin]
  | cons u us ih =>
    cases y with
    | nil => simp [lavLin]
    | cons v vs =>
      intro w hw
      simp only [lavLin, List.zipWith_cons_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact Nat.le_trans (normInfFast_add_le _ _) (Nat.add_le_add
          (Nat.le_trans (normInfFast_scale_le a u) (Nat.mul_le_mul_left _ (hx u (by simp))))
          (Nat.le_trans (normInfFast_scale_le b v) (Nat.mul_le_mul_left _ (hy v (by simp)))))
      · exact ih vs (fun u hu => hx u (by simp [hu])) (fun v hv => hy v (by simp [hv])) w hw
def reduceVecMod {d : Nat} (q : Nat) (x : List (FastIntPoly d)) := x.map (reducePolyMod q)
def polyVecScaleMod {d : Nat} (q : Nat) (c : Nat) (x : List (FastIntPoly d)) := x.map (fun u => reducePolyMod q (intScale c u))
def polyVecAddMod {d : Nat} (q : Nat) (x y : List (FastIntPoly d)) := reduceVecMod q (lavLin 1 x 1 y)
def lavMatImage {d : Nat} (q : Nat) (M : List (List (FastIntPoly d))) (x : List (FastIntPoly d)) := M.map (fun row => reducePolyMod q (rowDot x row))
theorem lavMatImage_lin {d : Nat} (q : Nat) (M : List (List (FastIntPoly d))) (c : Nat) (x y : List (FastIntPoly d)) (h : x.length = y.length) : lavMatImage q M (lavLin 1 x c y) = polyVecAddMod q (lavMatImage q M x) (polyVecScaleMod q c (lavMatImage q M y)) := by
  unfold lavMatImage polyVecAddMod polyVecScaleMod reduceVecMod lavLin
  rw [List.map_map, List.zipWith_map]
  simp only [List.zipWith_self, List.map_map]
  apply List.map_congr_left; intro row _; apply Sized.ext; funext k
  simp only [Function.comp_apply, reducePolyMod_spec, addFast_eq_spec, scaleFast_eq_spec, Int.one_mul]
  rw [show (rowDot (List.zipWith (fun u v => intAdd (intScale 1 u) (intScale c v)) x y) row).spec k =
    (rowDot x row).spec k + (c : Int) * (rowDot y row).spec k by simpa only [lavLin, Int.one_mul] using rowDot_lin 1 c x y row h k]
  simp [Int.add_emod, Int.mul_emod]
theorem lavModEq_coeff {d : Nat} (q : Nat) (M : List (List (FastIntPoly d))) (z w p : List (FastIntPoly d)) (c : Nat) (hw : w.length = M.length) (hp : p.length = M.length) (he : lavMatImage q M z = polyVecAddMod q w (polyVecScaleMod q c p)) (i : Nat) (hi : i < M.length) (k : Fin d) : (rowDot z M[i]).spec k % (q : Int) = (w[i].spec k + (c : Int) * p[i].spec k) % (q : Int) := by
  have e := congrArg (fun xs => (xs[i]?).map (fun u => u.spec k)) he
  simp only [lavMatImage, polyVecAddMod, polyVecScaleMod, reduceVecMod, lavLin,
    List.getElem?_map, List.getElem?_zipWith, List.getElem?_eq_getElem (by omega : i < w.length),
    List.getElem?_eq_getElem (by omega : i < p.length), List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq, reducePolyMod_spec, addFast_eq_spec, scaleFast_eq_spec, Int.one_mul] at e
  simpa [Int.add_emod, Int.mul_emod] using e
theorem lavCancel {q : Nat} (hp : IsPrimeNat q) {c x : Int} (hc : c ≠ 0) (hb : c.natAbs < q) (h : (c * x) % (q : Int) = 0) : x % (q : Int) = 0 := by
  have hd := Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero h)
  rw [Int.natAbs_mul] at hd
  have hn : ¬ q ∣ c.natAbs := fun hd => hc (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hd hb))
  exact Int.emod_eq_zero_of_dvd (Int.ofNat_dvd_left.mpr (hp.dvd_mul hd hn))
structure MsisBreakWitness {d : Nat} (pp : LavParams d) : Type where
  w : List (FastIntPoly d)
  len_eq : w.length = pp.cols
  nonzero : ∃ a ∈ w, a ≠ zeroVec d
  short : ∀ a ∈ w, normInfFast a.coeffs ≤ pp.sisBound
  kernel : ∀ row ∈ pp.A, ∀ k : Fin d, (rowDot w row).spec k % (pp.q : Int) = 0
structure IsEmpty (α : Type) : Prop where
  false : α → False
theorem lav_msisBreak_nonvacuous (p outRows : Nat) :
    ∃ pp : LavParams 1, pp.p = p ∧ pp.outRows = outRows ∧ pp.wfB = true ∧ IsEmpty (MsisBreakWitness pp) := by
  let one : FastIntPoly 1 := ⟨#[1], rfl⟩
  let pp : LavParams 1 := ⟨37, p, 1, 2, 4, 1, outRows, [[one]]⟩
  have hwf : (⟨37, 2, 1, 2, 4, 1, 1, [[one]]⟩ : LavParams 1).wfB = true := by decide
  refine ⟨pp, rfl, rfl, hwf, ⟨?_⟩⟩
  rintro ⟨w, hlen, ⟨a, ha, hne⟩, hnorm, hker⟩
  have hw : w = [a] := by
    cases w with
    | nil => simp at ha
    | cons b bs =>
      have hb : bs = [] := List.eq_nil_of_length_eq_zero (by simpa [pp] using hlen)
      subst bs
      have hab : a = b := by simpa using ha
      rw [hab]
  subst w
  have hn := coeff_le_norm a (0 : Fin 1)
  have hb := hnorm a (by simp)
  have hk := hker [one] (by simp [pp]) (0 : Fin 1)
  have he : (rowDot [a] [one]).spec 0 = a.spec 0 := by
    simp only [rowDot, addFast_eq_spec, zeroVec_spec, Int.add_zero,
      negacyclicMulFast_eq_spec]
    simp [negacyclicSpec, sumInt, wrapSign, one, Sized.spec]
  rw [he] at hk
  have hz : a.spec 0 = 0 := by simp only [pp, LavParams.sisBound, LavParams.zBound] at hk hb; omega
  apply hne
  apply Sized.ext; funext i
  have hi : i = (0 : Fin 1) := Fin.ext (by omega)
  rw [hi, hz, zeroVec_spec]
def lavKeyDomain : List UInt8 := [76, 65, 86, 45, 75, 69, 89]
def lavInputDomain : List UInt8 := [76, 65, 86, 45, 73, 78]
def lavExpandDomain : List UInt8 := [76, 65, 86, 45, 69, 88, 80]
def lavOutDomain : List UInt8 := [76, 65, 86, 45, 79, 85, 84]
def lavRingDomain : List UInt8 := [76, 65, 86, 45, 82, 73, 78, 71]
def lavImage {d : Nat} (pp : LavParams d) (z : List (FastIntPoly d)) : List (FastIntPoly d) := pp.A.map fun row => reducePolyMod pp.q (rowDot z row)
def lavKeyPreimage {d : Nat} (pk : List (FastIntPoly d)) : List UInt8 := encodeFrameList lavKeyDomain [] (encodeIntRows (pk.map polyCoeffs))
def lavKeyDigest (H : Hash) {d : Nat} (pk : List (FastIntPoly d)) : List UInt8 := H (lavKeyPreimage pk)
def lavRingDigest (H : Hash) (ringKeys : List (List UInt8)) : List UInt8 := H (encodeFrameList lavRingDomain [] (encodeFields ringKeys))
def lavRingDigest_binds (H : Hash) (r₁ r₂ : List (List UInt8)) (h : lavRingDigest H r₁ = lavRingDigest H r₂) : PSum (r₁ = r₂) (ExactCollision
    H (encodeFrameList lavRingDomain [] (encodeFields r₁)) (encodeFrameList lavRingDomain [] (encodeFields r₂))) := by
  rcases hash_frame_binding H h with ⟨_, _, hr⟩ | hcol
  · exact PSum.inl (encodeFields_injective hr)
  · exact PSum.inr hcol
def lavInput (ring : List UInt8) (epoch slot : Nat) : List UInt8 := encodeFrameList lavInputDomain ring (leb128 epoch ++ leb128 slot)
theorem lavInput_injective {r₁ r₂ : List UInt8} {e₁ e₂ s₁ s₂ : Nat} (h : lavInput r₁ e₁ s₁ = lavInput r₂ e₂ s₂) : r₁ = r₂ ∧ e₁ = e₂ ∧ s₁ = s₂ := by
  obtain ⟨_, hr, hes⟩ := encodeFrameList_injective h
  obtain ⟨he, hs⟩ := leb128_prefix_inj hes
  exact ⟨hr, he, (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hs)).1⟩
def lavSeed (H : Hash) (ring : List UInt8) (epoch slot : Nat) : List UInt8 := H (lavInput ring epoch slot)
def lavSeed_binds (H : Hash) (r₁ r₂ : List UInt8) (e₁ e₂ s₁ s₂ : Nat) (h : lavSeed H r₁ e₁ s₁ = lavSeed H r₂ e₂ s₂) : PSum (r₁ = r₂ ∧ e₁ = e₂ ∧ s₁ = s₂) (ExactCollision
    H (lavInput r₁ e₁ s₁) (lavInput r₂ e₂ s₂)) :=
  if hPre : lavInput r₁ e₁ s₁ = lavInput r₂ e₂ s₂ then
    .inl (lavInput_injective hPre) else .inr ⟨hPre, h⟩
def lavHashPoly (H : Hash) (q d : Nat) (seed : List UInt8) (i j : Nat) : FastIntPoly d :=
  Sized.ofFn fun k : Fin d =>
    ((ofBE (H (encodeFrameList lavExpandDomain seed (leb128 i ++ leb128 j ++ leb128 k.val))) : Nat)
      : Int) % (q : Int)
def lavHashMatrix (H : Hash) {d : Nat} (pp : LavParams d) (seed : List UInt8) : List (List (FastIntPoly d)) := (List.range pp.outRows).map fun i => (List.range pp.cols).map fun j => lavHashPoly H pp.q d seed i j
def lavRound (q p : Nat) (c : Int) : Int := ((c % (q : Int)) * (p : Int) + (q : Int) / 2) / (q : Int) % (p : Int)
def lavOutput (H : Hash) (keyDigest input : List UInt8) {d : Nat} (y : List (FastIntPoly d)) : List UInt8 :=
  H (encodeFrameList lavOutDomain (encodeListField keyDigest ++ encodeListField input)
    (encodeIntRows (y.map polyCoeffs)))
def lavShort {d : Nat} (beta : Nat) (z : List (FastIntPoly d)) : Bool := z.all fun a => decide (normInfFast a.coeffs ≤ beta)
theorem lavShort_iff {d : Nat} (beta : Nat) (z : List (FastIntPoly d)) : lavShort beta z = true ↔ ∀ a ∈ z, normInfFast a.coeffs ≤ beta := by simp [lavShort, List.all_eq_true]
def lavHashImage (H : Hash) {d : Nat} (pp : LavParams d) (seed : List UInt8) (z : List (FastIntPoly d)) := lavMatImage pp.q (lavHashMatrix H pp seed) z
def lavOutputFromPre (H : Hash) {d : Nat} (pp : LavParams d) (kd input : List UInt8) (u : List (FastIntPoly d)) := lavOutput H kd input (u.map fun a => Sized.ofFn fun k => lavRound pp.q pp.p (a.spec k))
def lavChallenge (H : Hash) {d : Nat} (pp : LavParams d) (kd input : List UInt8) (pk u wA wB : List (FastIntPoly d)) : Nat :=
  1 + ofBE (H (encodeFields [[76, 65, 86, 45, 68, 76, 69, 81],
    encodeFields ([d, pp.q, pp.p, pp.beta, pp.cMax, pp.gamma, pp.cols, pp.outRows].map leb128),
    encodeFields (pp.A.map fun row => encodeIntRows (row.map polyCoeffs)), kd, input,
    encodeIntRows (pk.map polyCoeffs), encodeIntRows (u.map polyCoeffs),
    encodeIntRows (wA.map polyCoeffs), encodeIntRows (wB.map polyCoeffs)])) % pp.cMax
def lavResponse {d : Nat} (c : Nat) (sk mask : List (FastIntPoly d)) := lavLin 1 mask c sk
def lavMaskShift {d : Nat} (c : Nat) (sk z : List (FastIntPoly d)) := lavLin 1 z (-(c : Int)) sk
theorem lavMaskShift_cancel {d : Nat} (c : Nat) (sk z : List (FastIntPoly d)) (hl : sk.length = z.length) : lavResponse c sk (lavMaskShift c sk z) = z := by
  induction sk generalizing z with
  | nil => have hz : z = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm); subst z; rfl
  | cons a as ih =>
    cases z with
    | nil => simp at hl
    | cons b bs =>
      simp only [lavResponse, lavMaskShift, lavLin, List.zipWith_cons_cons, List.cons.injEq]
      refine ⟨?_, ih bs (by simpa using hl)⟩
      apply Sized.ext; funext k; simp only [addFast_eq_spec, scaleFast_eq_spec, Int.neg_mul, Int.one_mul]; omega
/-- Response-only compatibility for arbitrarily many evaluations. Public images still constrain keys. -/
theorem lav_response_hides_sk_multi_eval {d : Nat} (pp : LavParams d) (cs : List Nat) (zs : List (List (FastIntPoly d))) (sk' : List (FastIntPoly d)) (hroom : pp.cMax * pp.beta ≤ pp.gamma) (hl : cs.length = zs.length) (hc : ∀ c ∈ cs, c ≤ pp.cMax) (hz : ∀ z ∈ zs, z.length = sk'.length ∧ lavShort pp.zBound z = true) (hs : lavShort pp.beta sk' = true) : (∀ pair ∈ cs.zip zs, lavShort pp.gamma (lavMaskShift pair.1 sk' pair.2) = true) ∧ (cs.zip zs).map (fun pair => lavResponse pair.1 sk' (lavMaskShift pair.1 sk' pair.2)) = zs := by
  constructor
  · intro pair hm
    have hm' := List.of_mem_zip hm
    have hn := lavLin_short 1 (-(pair.1 : Int)) pair.2 sk' pp.zBound pp.beta
      ((lavShort_iff _ _).mp (hz _ hm'.2).2) ((lavShort_iff _ _).mp hs)
    apply (lavShort_iff _ _).mpr; intro w hw
    have hb := hn w hw
    have hmul := Nat.mul_le_mul_right pp.beta (hc _ hm'.1)
    simp only [Int.natAbs_one, Int.natAbs_neg, Int.natAbs_natCast, Nat.one_mul] at hb
    unfold LavParams.zBound at hb; omega
  · induction cs generalizing zs with
    | nil => have he : zs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm); subst zs; rfl
    | cons c cs ih =>
      cases zs with
      | nil => simp at hl
      | cons z zs =>
        simp only [List.zip_cons_cons, List.map_cons]
        rw [lavMaskShift_cancel c sk' z (hz z (by simp)).1.symm]
        exact congrArg (z :: ·) (ih zs (by simpa using hl) (fun c h => hc c (by simp [h])) (fun z h => hz z (by simp [h])))
structure LavProof (d : Nat) where
  pk : List (FastIntPoly d)
  u : List (FastIntPoly d)
  wA : List (FastIntPoly d)
  wB : List (FastIntPoly d)
  z : List (FastIntPoly d)
def lavVerify (H : Hash) {d : Nat} (pp : LavParams d) (keyDigest ring : List UInt8) (epoch slot : Nat) (v : List UInt8) (π : LavProof d) : Bool :=
  let c := lavChallenge H pp keyDigest (lavInput ring epoch slot) π.pk π.u π.wA π.wB
  pp.wfB && decide (lavKeyDigest H π.pk = keyDigest ∧ π.z.length = pp.cols ∧
    π.pk.length = pp.A.length ∧ π.u.length = pp.outRows ∧ π.wA.length = pp.A.length ∧
    π.wB.length = pp.outRows ∧ π.u = reduceVecMod pp.q π.u) && lavShort pp.zBound π.z &&
    decide (lavImage pp π.z = polyVecAddMod pp.q π.wA (polyVecScaleMod pp.q c π.pk) ∧
      lavHashImage H pp (lavSeed H ring epoch slot) π.z = polyVecAddMod pp.q π.wB (polyVecScaleMod pp.q c π.u) ∧
      v = lavOutputFromPre H pp keyDigest (lavInput ring epoch slot) π.u)
theorem lavVerify_params {d : Nat} (H : Hash) (pp : LavParams d) (kd ring : List UInt8) (epoch slot : Nat) (v : List UInt8) (π : LavProof d) (h : lavVerify H pp kd ring epoch slot v π = true) : pp.wfB = true ∧ π.z.length = pp.cols ∧ (2 * pp.sisBound + 1) ^ pp.cols < pp.q ^ pp.A.length := by
  simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2.2.1, (of_decide_eq_true h.1.1.1).2.2.2.2.2.2.2.2.2.2⟩
def lavPrepare (H : Hash) {d : Nat} (pp : LavParams d) (ring : List UInt8) (epoch slot : Nat) (sk mask : List (FastIntPoly d)) : LavProof d :=
  let pk := lavImage pp sk
  let u := lavHashImage H pp (lavSeed H ring epoch slot) sk
  let wA := lavImage pp mask
  let wB := lavHashImage H pp (lavSeed H ring epoch slot) mask
  ⟨pk, u, wA, wB, lavResponse (lavChallenge H pp (lavKeyDigest H pk) (lavInput ring epoch slot) pk u wA wB) sk mask⟩
/-- Caller supplies fresh uniform masks; rejection returns none, never an unmasked fallback. -/
def lavEval (H : Hash) {d : Nat} (pp : LavParams d) (ring : List UInt8) (epoch slot : Nat) (sk mask : List (FastIntPoly d)) : Option (List UInt8 × LavProof d) :=
  let π := lavPrepare H pp ring epoch slot sk mask
  if pp.wfB && decide (sk.length = pp.cols ∧ mask.length = pp.cols) &&
      lavShort pp.beta sk && lavShort pp.gamma mask && lavShort pp.zBound π.z then
    some (lavOutputFromPre H pp (lavKeyDigest H π.pk) (lavInput ring epoch slot) π.u, π)
  else none
theorem lavEval_complete (H : Hash) {d : Nat} (pp : LavParams d) (ring : List UInt8) (epoch slot : Nat) (sk mask : List (FastIntPoly d)) (hLen : sk.length = pp.cols) (hmLen : mask.length = pp.cols) (hShort : lavShort pp.beta sk = true) (hmShort : lavShort pp.gamma mask = true) (hwf : pp.wfB = true) (hz : lavShort pp.zBound (lavPrepare H pp ring epoch slot sk mask).z = true) : ∃ ev, lavEval H pp ring epoch slot sk mask = some ev ∧ lavVerify H pp (lavKeyDigest H (lavImage pp sk)) ring epoch slot ev.1 ev.2 = true := by
  let π := lavPrepare H pp ring epoch slot sk mask
  refine ⟨(lavOutputFromPre H pp (lavKeyDigest H π.pk) (lavInput ring epoch slot) π.u, π), ?_, ?_⟩
  · simp [lavEval, π, hwf, hLen, hmLen, hShort, hmShort, hz]
  · have hcan : ∀ xs : List (FastIntPoly d), reduceVecMod pp.q xs = reduceVecMod pp.q (reduceVecMod pp.q xs) := by
      intro xs; simp only [reduceVecMod, List.map_map]; apply List.map_congr_left; intro a _
      apply Sized.ext; funext k; simp [reducePolyMod_spec]
    have ha := lavMatImage_lin pp.q pp.A
      (lavChallenge H pp (lavKeyDigest H π.pk) (lavInput ring epoch slot) π.pk π.u π.wA π.wB) mask sk (hmLen.trans hLen.symm)
    have hb := lavMatImage_lin pp.q (lavHashMatrix H pp (lavSeed H ring epoch slot))
      (lavChallenge H pp (lavKeyDigest H π.pk) (lavInput ring epoch slot) π.pk π.u π.wA π.wB) mask sk (hmLen.trans hLen.symm)
    have huc : π.u = reduceVecMod pp.q π.u := by
      simpa [π, lavPrepare, lavHashImage, lavMatImage, reduceVecMod, List.map_map] using
        hcan ((lavHashMatrix H pp (lavSeed H ring epoch slot)).map (rowDot sk))
    simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hwf, ?_⟩, hz⟩, ha, hb, rfl⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, huc⟩
    · exact (lavLin_length 1 _ mask sk (hmLen.trans hLen.symm)).trans hmLen
    all_goals simp [π, lavPrepare, lavImage, lavHashImage, lavMatImage, lavHashMatrix]
/-- Chosen-challenge algebraic simulator; Fiat–Shamir challenge programming is a separate assumption. -/
def lavSimulate (H : Hash) {d : Nat} (pp : LavParams d) (seed : List UInt8) (pk u : List (FastIntPoly d)) (c : Nat) (z : List (FastIntPoly d)) : LavProof d :=
  ⟨pk, u, reduceVecMod pp.q (lavLin 1 (lavImage pp z) (-(c : Int)) pk),
    reduceVecMod pp.q (lavLin 1 (lavHashImage H pp seed z) (-(c : Int)) u), z⟩
theorem lavSimulate_correct (H : Hash) {d : Nat} (pp : LavParams d) (seed : List UInt8) (pk u : List (FastIntPoly d)) (c : Nat) (z : List (FastIntPoly d)) (hp : pk.length = pp.A.length) (hu : u.length = pp.outRows) : let π := lavSimulate H pp seed pk u c z
    lavImage pp π.z = polyVecAddMod pp.q π.wA (polyVecScaleMod pp.q c π.pk) ∧
    lavHashImage H pp seed π.z = polyVecAddMod pp.q π.wB (polyVecScaleMod pp.q c π.u) := by
  have hs (M : List (List (FastIntPoly d))) (p : List (FastIntPoly d)) (hl : p.length = M.length) :
      lavMatImage pp.q M z = polyVecAddMod pp.q
        (reduceVecMod pp.q (lavLin 1 (lavMatImage pp.q M z) (-(c : Int)) p)) (polyVecScaleMod pp.q c p) := by
    apply List.ext_getElem (by simp [lavMatImage, polyVecAddMod, polyVecScaleMod, reduceVecMod, lavLin, hl])
    intro i hi hi'
    have hiM : i < M.length := by simpa [lavMatImage] using hi
    have hip : i < p.length := by omega
    apply Sized.ext; funext k
    simp only [lavMatImage, polyVecAddMod, polyVecScaleMod, reduceVecMod, lavLin,
      List.getElem_map, List.getElem_zipWith, reducePolyMod_spec, addFast_eq_spec, scaleFast_eq_spec, Int.one_mul, Int.neg_mul]
    rw [← Int.add_emod]
    simp only [Int.add_assoc]
    have hz : -((c : Int) * p[i].spec k) + (c : Int) * p[i].spec k = 0 := by omega
    rw [hz, Int.add_zero, Int.emod_emod]
  exact ⟨hs pp.A pk hp, hs (lavHashMatrix H pp seed) u (by simpa [lavHashMatrix] using hu)⟩
/-- Rewinding evidence is supplied to reductions, never broadcast in a ticket. -/
structure LavForkedProof {d : Nat} (pp : LavParams d) (B : List (List (FastIntPoly d))) (π : LavProof d) (c : Nat) where
  challenge : Nat
  response : List (FastIntPoly d)
  lower : 1 ≤ challenge
  upper : challenge ≤ pp.cMax
  distinct : c ≠ challenge
  length_eq : response.length = π.z.length
  short : lavShort pp.zBound response = true
  eqA : lavImage pp response = polyVecAddMod pp.q π.wA (polyVecScaleMod pp.q challenge π.pk)
  eqB : lavMatImage pp.q B response = polyVecAddMod pp.q π.wB (polyVecScaleMod pp.q challenge π.u)
@[expose] def LavRewind {d : Nat} (H : Hash) (pp : LavParams d) (ring : List UInt8) (epoch slot : Nat) (π : LavProof d) :=
  LavForkedProof pp (lavHashMatrix H pp (lavSeed H ring epoch slot)) π
    (lavChallenge H pp (lavKeyDigest H π.pk) (lavInput ring epoch slot) π.pk π.u π.wA π.wB)
def lavScale {d : Nat} (c : Int) (z : List (FastIntPoly d)) := z.map (intScale c)
theorem rowDot_scale {d : Nat} (c : Int) (z row : List (FastIntPoly d)) (k : Fin d) : (rowDot (lavScale c z) row).spec k = c * (rowDot z row).spec k := by
  induction z generalizing row with
  | nil => simp [lavScale, rowDot, zeroVec_spec]
  | cons a as ih => cases row with
    | nil => simp [lavScale, rowDot, zeroVec_spec]
    | cons b bs => simp only [lavScale, List.map_cons, rowDot, addFast_eq_spec, negacyclicMulFast_scale_left]; have ht := ih bs; unfold lavScale at ht; rw [ht, Int.mul_add]
theorem lavDelta_coeff {d : Nat} (q : Nat) (M : List (List (FastIntPoly d))) (z z' w p : List (FastIntPoly d)) (c c' : Nat) (hl : z.length = z'.length) (hw : w.length = M.length) (hp : p.length = M.length) (h : lavMatImage q M z = polyVecAddMod q w (polyVecScaleMod q c p)) (h' : lavMatImage q M z' = polyVecAddMod q w (polyVecScaleMod q c' p)) (i : Nat) (hi : i < M.length) (k : Fin d) : (rowDot (lavVecSub z z') M[i]).spec k % (q : Int) = (((c : Int) - c') * p[i].spec k) % (q : Int) := by
  rw [rowDot_sub_spec k _ _ _ hl, Int.sub_emod, lavModEq_coeff q M z w p c hw hp h i hi k,
    lavModEq_coeff q M z' w p c' hw hp h' i hi k, ← Int.sub_emod]
  congr 1; rw [Int.sub_mul]; omega
theorem lavCross_mod (q : Int) (a b r s u v : Int) (h : r % q = (a * u) % q) (h' : s % q = (b * v) % q) : (b * r - a * s) % q = (a * b * (u - v)) % q := by
  obtain ⟨t, ht⟩ := sub_eq_mul_of_emod_eq h
  obtain ⟨t', ht'⟩ := sub_eq_mul_of_emod_eq h'
  apply emod_eq_of_sub_eq_mul (c := b * t - a * t')
  have hr : r = a * u + q * t := by omega
  have hs : s = b * v + q * t' := by omega
  rw [hr, hs]; simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc]
  rw [Int.mul_left_comm b a u, Int.mul_left_comm b q t, Int.mul_left_comm a q t']; omega
theorem lavCanonical_coeff {d : Nat} (q : Nat) (u : List (FastIntPoly d)) (h : u = reduceVecMod q u) (i : Nat) (hi : i < u.length) (k : Fin d) : u[i].spec k % (q : Int) = u[i].spec k := by
  have he := congrArg (fun xs => (xs[i]?).map (fun a => a.spec k)) h; simpa [reduceVecMod, List.getElem?_map, List.getElem?_eq_getElem hi, reducePolyMod_spec] using he.symm
theorem lavDelta_bounds (c c' m : Nat) (hl : 1 ≤ c) (hu : c ≤ m) (hl' : 1 ≤ c') (hu' : c' ≤ m) (hne : c ≠ c') : ((c : Int) - c') ≠ 0 ∧ ((c : Int) - c').natAbs < m := by constructor <;> omega
def extractLavUniqueOrMsis {d : Nat} (H : Hash) (pp : LavParams d) (keyDigest ring : List UInt8) (epoch slot : Nat) (v₁ v₂ : List UInt8) (π₁ π₂ : LavProof d) (h₁ : lavVerify H pp keyDigest ring epoch slot v₁ π₁ = true) (h₂ : lavVerify H pp keyDigest ring epoch slot v₂ π₂ = true) (f₁ : LavRewind H pp ring epoch slot π₁) (f₂ : LavRewind H pp ring epoch slot π₂) : PSum (v₁ = v₂) (PSum (MsisBreakWitness pp) (ExactCollision
    H (lavKeyPreimage π₁.pk) (lavKeyPreimage π₂.pk))) := by
  simp only [lavVerify, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  obtain ⟨⟨⟨hw, hk₁, hl₁, hp₁, hu₁, ha₁, hb₁, hcan₁⟩, hs₁⟩, heA₁, heB₁, hv₁⟩ := h₁
  obtain ⟨⟨⟨_, hk₂, hl₂, hp₂, hu₂, ha₂, hb₂, hcan₂⟩, hs₂⟩, heA₂, heB₂, hv₂⟩ := h₂
  have hhash : H (lavKeyPreimage π₁.pk) = H (lavKeyPreimage π₂.pk) := hk₁.trans hk₂.symm
  if hpre : lavKeyPreimage π₁.pk = lavKeyPreimage π₂.pk then
    have hpk : π₁.pk = π₂.pk := polyRows_injective (encodeIntRows_injective (encodeFrameList_injective hpre).2.2)
    let c₁ := lavChallenge H pp keyDigest (lavInput ring epoch slot) π₁.pk π₁.u π₁.wA π₁.wB
    let c₂ := lavChallenge H pp keyDigest (lavInput ring epoch slot) π₂.pk π₂.u π₂.wA π₂.wB
    have ff₁ : LavForkedProof pp (lavHashMatrix H pp (lavSeed H ring epoch slot)) π₁ c₁ := by simpa [LavRewind, hk₁] using f₁
    have ff₂ : LavForkedProof pp (lavHashMatrix H pp (lavSeed H ring epoch slot)) π₂ c₂ := by simpa [LavRewind, hk₂] using f₂
    have wf := of_decide_eq_true hw
    have hc : 1 < pp.cMax ∧ pp.cMax < pp.q := ⟨wf.2.2.2.2.2.2.1, wf.2.2.2.2.2.2.2.1⟩
    have cBounds : ∀ kd input pk u wA wB, 1 ≤ lavChallenge H pp kd input pk u wA wB ∧
        lavChallenge H pp kd input pk u wA wB ≤ pp.cMax := by
      intros; unfold lavChallenge; constructor
      · omega
      · rw [Nat.add_comm]; exact Nat.succ_le_of_lt (Nat.mod_lt _ (by omega))
    have cb₁ := cBounds keyDigest (lavInput ring epoch slot) π₁.pk π₁.u π₁.wA π₁.wB
    have cb₂ := cBounds keyDigest (lavInput ring epoch slot) π₂.pk π₂.u π₂.wA π₂.wB
    let a : Int := (c₁ : Int) - ff₁.challenge
    let b : Int := (c₂ : Int) - ff₂.challenge
    have ab : a ≠ 0 ∧ a.natAbs < pp.cMax := lavDelta_bounds c₁ ff₁.challenge pp.cMax cb₁.1 cb₁.2 ff₁.lower ff₁.upper ff₁.distinct
    have bb : b ≠ 0 ∧ b.natAbs < pp.cMax := lavDelta_bounds c₂ ff₂.challenge pp.cMax cb₂.1 cb₂.2 ff₂.lower ff₂.upper ff₂.distinct
    let dz₁ := lavVecSub π₁.z ff₁.response
    let dz₂ := lavVecSub π₂.z ff₂.response
    have dl₁ : dz₁.length = pp.cols := (lavVecSub_length _ _ ff₁.length_eq.symm).trans hl₁
    have dl₂ : dz₂.length = pp.cols := (lavVecSub_length _ _ ff₂.length_eq.symm).trans hl₂
    let x := lavScale b dz₁
    let y := lavScale a dz₂
    have xl : x.length = pp.cols := by simpa [x, lavScale] using dl₁
    have yl : y.length = pp.cols := by simpa [y, lavScale] using dl₂
    have eA₁ := lavDelta_coeff pp.q pp.A π₁.z ff₁.response π₁.wA π₁.pk c₁ ff₁.challenge ff₁.length_eq.symm ha₁ hp₁ heA₁ ff₁.eqA
    have eA₂ := lavDelta_coeff pp.q pp.A π₂.z ff₂.response π₂.wA π₂.pk c₂ ff₂.challenge ff₂.length_eq.symm ha₂ hp₂ heA₂ ff₂.eqA
    have bl : (lavHashMatrix H pp (lavSeed H ring epoch slot)).length = pp.outRows := by simp [lavHashMatrix]
    have eB₁ := lavDelta_coeff pp.q (lavHashMatrix H pp (lavSeed H ring epoch slot)) π₁.z ff₁.response π₁.wB π₁.u c₁ ff₁.challenge ff₁.length_eq.symm (hb₁.trans bl.symm) (hu₁.trans bl.symm) heB₁ ff₁.eqB
    have eB₂ := lavDelta_coeff pp.q (lavHashMatrix H pp (lavSeed H ring epoch slot)) π₂.z ff₂.response π₂.wB π₂.u c₂ ff₂.challenge ff₂.length_eq.symm (hb₂.trans bl.symm) (hu₂.trans bl.symm) heB₂ ff₂.eqB
    if hxy : x = y then
      apply PSum.inl
      have hu : π₁.u = π₂.u := by
        apply List.ext_getElem (hu₁.trans hu₂.symm); intro i hi₁ hi₂
        apply Sized.ext; funext k
        have hi : i < (lavHashMatrix H pp (lavSeed H ring epoch slot)).length := by omega
        have he := congrArg (fun z => (rowDot z (lavHashMatrix H pp (lavSeed H ring epoch slot))[i]).spec k) hxy
        change (rowDot (lavScale b dz₁) _).spec k = (rowDot (lavScale a dz₂) _).spec k at he
        rw [rowDot_scale, rowDot_scale] at he
        have hm := lavCross_mod (pp.q : Int) a b _ _ _ _ (eB₁ i hi k) (eB₂ i hi k)
        rw [show b * (rowDot dz₁ (lavHashMatrix H pp (lavSeed H ring epoch slot))[i]).spec k -
          a * (rowDot dz₂ (lavHashMatrix H pp (lavSeed H ring epoch slot))[i]).spec k = 0 by omega, Int.zero_emod] at hm
        have hm' : (a * (b * (π₁.u[i].spec k - π₂.u[i].spec k))) % (pp.q : Int) = 0 := by simpa [Int.mul_assoc] using hm.symm
        have hz := lavCancel (pp.prime hw) bb.1 (Nat.lt_trans bb.2 hc.2)
          (lavCancel (pp.prime hw) ab.1 (Nat.lt_trans ab.2 hc.2) hm')
        rw [Int.sub_emod, lavCanonical_coeff pp.q π₁.u hcan₁ i hi₁ k, lavCanonical_coeff pp.q π₂.u hcan₂ i hi₂ k] at hz
        have hcon := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hz
        simpa [lavCanonical_coeff pp.q π₁.u hcan₁ i hi₁ k, lavCanonical_coeff pp.q π₂.u hcan₂ i hi₂ k] using hcon
      rw [hv₁, hv₂, hu]
    else
      refine .inr (.inl ⟨lavVecSub x y, (lavVecSub_length x y (xl.trans yl.symm)).trans xl,
        lavVecSub_nonzero x y (xl.trans yl.symm) hxy, ?_, ?_⟩)
      · have bound (c : Int) (z z' : List (FastIntPoly d)) (hc : c.natAbs < pp.cMax)
            (hz : lavShort pp.zBound z = true) (hz' : lavShort pp.zBound z' = true) :
            ∀ u ∈ lavScale c (lavVecSub z z'), normInfFast u.coeffs ≤ pp.cMax * (2 * pp.zBound) := by
          intro u hu; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
          exact Nat.le_trans (normInfFast_scale_le c v) (Nat.mul_le_mul (by omega)
            (lavVecSub_short pp.zBound z z' ((lavShort_iff _ _).mp hz) ((lavShort_iff _ _).mp hz') v hv))
        intro u hu
        have hn := lavVecSub_short (pp.cMax * (2 * pp.zBound)) x y (bound b _ _ bb.2 hs₁ ff₁.short) (bound a _ _ ab.2 hs₂ ff₂.short) u hu
        have hb : 2 * (pp.cMax * (2 * pp.zBound)) = pp.sisBound := by
          unfold LavParams.sisBound
          rw [Nat.mul_left_comm pp.cMax 2, ← Nat.mul_assoc 2 2, ← Nat.mul_assoc]
        rwa [hb] at hn
      · intro row hr k
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
        subst row
        rw [rowDot_sub_spec k x y _ (xl.trans yl.symm), rowDot_scale, rowDot_scale]
        have hm := lavCross_mod (pp.q : Int) a b _ _ _ _ (eA₁ i hi k) (eA₂ i hi k)
        have hp : π₁.pk[i] = π₂.pk[i] := by
          have he := congrArg (fun xs => xs[i]?) hpk
          simpa only [List.getElem?_eq_getElem (by omega : i < π₁.pk.length), List.getElem?_eq_getElem (by omega : i < π₂.pk.length), Option.some.injEq] using he
        simpa [hp] using hm
  else exact .inr (.inr ⟨hpre, hhash⟩)
theorem lav_unique_output_or_msisBreak {d : Nat} (H : Hash) (pp : LavParams d) (keyDigest ring : List UInt8) (epoch slot : Nat) (v₁ v₂ : List UInt8) (π₁ π₂ : LavProof d) (h₁ : lavVerify H pp keyDigest ring epoch slot v₁ π₁ = true) (h₂ : lavVerify H pp keyDigest ring epoch slot v₂ π₂ = true) (f₁ : LavRewind H pp ring epoch slot π₁) (f₂ : LavRewind H pp ring epoch slot π₂) : Nonempty (PSum (v₁ = v₂) (PSum (MsisBreakWitness pp) (ExactCollision H (lavKeyPreimage π₁.pk) (lavKeyPreimage π₂.pk)))) :=
  ⟨extractLavUniqueOrMsis H pp keyDigest ring epoch slot v₁ v₂ π₁ π₂ h₁ h₂ f₁ f₂⟩
structure LavTicket (d : Nat) where
  keyIndex : Nat
  output : List UInt8
  proof : LavProof d
def lavRingVerify (H : Hash) {d : Nat} (pp : LavParams d) (ringKeys : List (List UInt8)) (epoch slot : Nat) (t : LavTicket d) : Bool :=
  match ringKeys[t.keyIndex]? with
  | some kd => lavVerify H pp kd (lavRingDigest H ringKeys) epoch slot t.output t.proof
  | none => false
def lavRingVerify_unique {d : Nat} (H : Hash) (pp : LavParams d) (ringKeys : List (List UInt8)) (epoch slot : Nat) (t₁ t₂ : LavTicket d) (hidx : t₁.keyIndex = t₂.keyIndex) (h₁ : lavRingVerify H pp ringKeys epoch slot t₁ = true) (h₂ : lavRingVerify H pp ringKeys epoch slot t₂ = true) (f₁ : LavRewind H pp (lavRingDigest H ringKeys) epoch slot t₁.proof) (f₂ : LavRewind H pp (lavRingDigest H ringKeys) epoch slot t₂.proof) : PSum (t₁.output = t₂.output) (PSum (MsisBreakWitness pp) (TranscriptCollision
    H)) := by
  unfold lavRingVerify at h₁ h₂
  rw [hidx] at h₁
  cases hk : ringKeys[t₂.keyIndex]? with
  | none => rw [hk] at h₂; cases h₂
  | some kd =>
    rw [hk] at h₁ h₂
    cases extractLavUniqueOrMsis H pp kd _ epoch slot _ _ _ _ h₁ h₂ f₁ f₂ with
    | inl he => exact .inl he
    | inr hb => cases hb with
      | inl w => exact .inr (.inl w)
      | inr w => exact .inr (.inr w.transcript)
def lav_T_uniqueness {d : Nat} (H : Hash) (pp : LavParams d) (ringKeys : List (List UInt8)) (epoch slot : Nat) (tickets : List (LavTicket d)) : (∀ t ∈ tickets, lavRingVerify H pp ringKeys epoch slot t = true) → (∀ t ∈ tickets, LavRewind H pp (lavRingDigest H ringKeys) epoch slot t.proof) → (tickets.map fun t => t.output).Nodup → PSum (tickets.map fun t => t.keyIndex).Nodup (PSum (MsisBreakWitness pp) (TranscriptCollision
    H)) := by
  match tickets with
  | [] => intro _ _ _; exact .inl (by simp)
  | t :: ts =>
    intro hAll forks hND
    obtain ⟨hOut, hRest⟩ := List.nodup_cons.mp hND
    cases lav_T_uniqueness H pp ringKeys epoch slot ts (fun x hx => hAll x (by simp [hx])) (fun x hx => forks x (by simp [hx])) hRest with
    | inr w => exact .inr w
    | inl hI =>
      let rec scan (rest : List (LavTicket d)) : (∀ x ∈ rest, x ∈ ts) →
          PSum (t.keyIndex ∉ rest.map (·.keyIndex)) (PSum (MsisBreakWitness pp) (TranscriptCollision
            H)) := by
        match rest with
        | [] => intro _; exact .inl (by simp)
        | x :: xs =>
          intro hsub
          if he : x.keyIndex = t.keyIndex then
            cases lavRingVerify_unique H pp ringKeys epoch slot x t he (hAll x (by simp [hsub x (by simp)]))
                (hAll t (by simp)) (forks x (by simp [hsub x (by simp)])) (forks t (by simp)) with
            | inl ho => exact False.elim (hOut (List.mem_map.mpr ⟨x, hsub x (by simp), ho⟩))
            | inr w => exact .inr w
          else
            cases scan xs (fun y hy => hsub y (by simp [hy])) with
            | inl hn => exact .inl (by simpa [List.mem_map, eq_comm] using And.intro he hn)
            | inr w => exact .inr w
      termination_by structural rest
      cases scan ts (fun _ h => h) with
      | inl hn => exact .inl (List.nodup_cons.mpr ⟨hn, hI⟩)
      | inr w => exact .inr w
termination_by structural tickets
abbrev BondedShareCommit := {bytes : List UInt8 // bytes.length = 32}
structure BondedCommitteeMember where
  memberId : Nat
  weight : Int
  bond : Nat
  lockedCommit : BondedShareCommit
structure BondedShareOpening (d : Nat) where
  share : TulvaShare d
  salt : List UInt8
  deriving DecidableEq
def shareOpeningBytes {d : Nat} (memberId : Nat) (o : BondedShareOpening d) : List UInt8 :=
  encodeFields [encodeSignedIntList [memberId, o.share.point], o.share.tag,
    encodeSignedIntList (polyCoeffs o.share.sharePoly), o.salt]
def commitShare (H : Hash) {d : Nat} (auctionTag : List UInt8) (memberId : Nat) (o : BondedShareOpening d) : List UInt8 := H (encodeFrameList [66, 79, 78, 68, 45, 83, 72, 65, 82, 69] auctionTag (shareOpeningBytes memberId o))
def bondedShareCommit_binding_or_collision (H : Hash) {d : Nat} (tag₁ tag₂ : List UInt8) (id₁ id₂ : Nat) (o₁ o₂ : BondedShareOpening d) (h : commitShare H tag₁ id₁ o₁ = commitShare H tag₂ id₂ o₂) : PSum (tag₁ = tag₂ ∧ id₁ = id₂ ∧ o₁ = o₂) (ExactCollision
    H (encodeFrameList [66, 79, 78, 68, 45, 83, 72, 65, 82, 69] tag₁ (shareOpeningBytes id₁ o₁)) (encodeFrameList [66, 79, 78, 68, 45, 83, 72, 65, 82, 69] tag₂ (shareOpeningBytes id₂ o₂))) := by
  rcases hash_frame_binding H h with ⟨_, ht, hb⟩ | hc
  · have hf := encodeFields_injective hb
    simp only [List.cons.injEq, and_true] at hf
    have hi := encodeSignedIntList_injective hf.1
    simp only [List.cons.injEq, and_true] at hi
    have hp := polyCoeffs_injective (encodeSignedIntList_injective hf.2.2.1)
    refine PSum.inl ⟨ht, by omega, ?_⟩
    cases o₁ with | mk s₁ salt₁ =>
      cases o₂ with | mk s₂ salt₂ =>
        cases s₁; cases s₂
        simp_all
  · exact PSum.inr hc
def bondedLockCheck (threshold : Nat) (members : List BondedCommitteeMember) : Bool :=
  decide (0 < threshold ∧ threshold ≤ members.length ∧
    (members.map (·.memberId)).Nodup ∧ ∀ m ∈ members, 0 < m.bond)
/-- Public validity covers query, identity and canonical coefficient bounds; algebraic honesty
still has the explicit TulvaSharesValid contract of decryption correctness. -/
def bondedOpeningValid (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (m : BondedCommitteeMember) : Option (BondedShareOpening d) → Bool
  | none => false
  | some o => decide (commitShare H tag m.memberId o = m.lockedCommit.val ∧
      o.share.point = (m.memberId : Int) ∧ o.share.tag = tag ∧
      ∀ a ∈ polyCoeffs o.share.sharePoly, 0 ≤ a ∧ a < (q : Int))
theorem bondedOpeningValid_refused (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (m : BondedCommitteeMember) (o : BondedShareOpening d) : bondedOpeningValid H q tag m (some o) = false ↔ commitShare H tag m.memberId o ≠ m.lockedCommit.val ∨ o.share.point ≠ (m.memberId : Int) ∨ o.share.tag ≠ tag ∨ ∃ a ∈ polyCoeffs o.share.sharePoly, a < 0 ∨ (q : Int) ≤ a := by
  simp only [bondedOpeningValid, decide_eq_false_iff_not]
  grind
def bondedSlash (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (m : BondedCommitteeMember) (o : Option (BondedShareOpening d)) : Nat :=
  if bondedOpeningValid H q tag m o then 0 else m.bond
structure BondedResolution (d : Nat) where
  slashedTotal : Nat
  refunds : List (Nat × Nat)
  entries : List (Int × TulvaShare d)
def bondedAuctionResolve (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (members : List BondedCommitteeMember) (opens : Nat → Option (BondedShareOpening d)) (slashedTotal : Nat) : BondedResolution d :=
  { slashedTotal := slashedTotal + (members.map fun m => bondedSlash H q tag m (opens m.memberId)).sum
    refunds := members.map fun m => (m.memberId, m.bond - bondedSlash H q tag m (opens m.memberId))
    entries := members.filterMap fun m =>
      if bondedOpeningValid H q tag m (opens m.memberId) then
        (opens m.memberId).map fun o => (m.weight, o.share) else none }
theorem bondedAuctionResolve_conserves (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (ms : List BondedCommitteeMember) (opens : Nat → Option (BondedShareOpening d)) (total : Nat) : (bondedAuctionResolve H q tag ms opens total).slashedTotal + ((bondedAuctionResolve H q tag ms opens total).refunds.map (·.2)).sum = total + (ms.map (·.bond)).sum := by
  simp only [bondedAuctionResolve, List.map_map, Function.comp_def]
  induction ms with
  | nil => simp
  | cons m ms ih =>
    have hb : bondedSlash H q tag m (opens m.memberId) ≤ m.bond := by
      unfold bondedSlash; split <;> omega
    simp only [List.map_cons, List.sum_cons] at *
    omega
theorem honest_member_never_slashed (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (m : BondedCommitteeMember) (o : Option (BondedShareOpening d)) (h : bondedOpeningValid H q tag m o = true) : bondedSlash H q tag m o = 0 ∧ m.bond - bondedSlash H q tag m o = m.bond := by
  simp [bondedSlash, h]
theorem bondedAuctionResolve_slashes (H : Hash) (q : Nat) (tag : List UInt8) {d : Nat} (m : BondedCommitteeMember) (ms : List BondedCommitteeMember) (opens : Nat → Option (BondedShareOpening d)) (total : Nat) (hb : 0 < m.bond) (h : bondedOpeningValid H q tag m (opens m.memberId) = false) : (bondedAuctionResolve H q tag (m :: ms) opens total).slashedTotal = (bondedAuctionResolve H q tag ms opens total).slashedTotal + m.bond ∧ (bondedAuctionResolve H q tag ms opens total).slashedTotal < (bondedAuctionResolve H q tag (m :: ms) opens total).slashedTotal := by
  simp only [bondedAuctionResolve, List.map_cons, List.sum_cons, bondedSlash, h, Bool.false_eq_true, reduceIte]
  omega
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
def AuctionState.init : AuctionState := { epoch := 0, queriesUsed := 0, usedTags := [], leaders := [] }
def auctionTurnCheck (H : Hash) (cfg : AuctionConfig) (st : AuctionState) (turn : AuctionTurn cfg) : Bool :=
  lavRingVerify H cfg.lav cfg.ringKeys st.epoch turn.slot turn.ticket &&
  decide (tulvaTag H turn.context turn.ct ∉ st.usedTags) &&
  decide (st.queriesUsed + turn.entries.length ≤ cfg.queryBudget) &&
  bitzVerify H cfg.tulva.params.q cfg.width turn.commitment turn.rows turn.claims &&
  tulvaCheck H cfg.tulva turn.context turn.ct turn.entries &&
  decide (tulvaDecode cfg.tulva turn.ct turn.entries = bitzPlainVec cfg.tulva.params.d turn.claims)
def auctionStep (H : Hash) (cfg : AuctionConfig) (st : AuctionState) (turn : AuctionTurn cfg) : Option AuctionState :=
  if auctionTurnCheck H cfg st turn then
    some { epoch := st.epoch + 1
           queriesUsed := st.queriesUsed + turn.entries.length
           usedTags := tulvaTag H turn.context turn.ct :: st.usedTags
           leaders := turn.ticket.output :: st.leaders }
  else none
def auctionRun (H : Hash) (cfg : AuctionConfig) : AuctionState → List (AuctionTurn cfg) → Option AuctionState
  | st, [] => some st
  | st, turn :: turns =>
    match auctionStep H cfg st turn with
    | some st' => auctionRun H cfg st' turns
    | none => none
def AuctionInv (cfg : AuctionConfig) (st : AuctionState) : Prop :=
  st.queriesUsed ≤ cfg.queryBudget ∧ st.usedTags.Nodup
theorem auctionInv_init (cfg : AuctionConfig) : AuctionInv cfg AuctionState.init :=
  ⟨Nat.zero_le _, List.nodup_nil⟩
theorem auctionStep_spec (H : Hash) (cfg : AuctionConfig) (st st' : AuctionState) (turn : AuctionTurn cfg) (h : auctionStep H cfg st turn = some st') : auctionTurnCheck H cfg st turn = true ∧ st'.epoch = st.epoch + 1 ∧ st'.queriesUsed = st.queriesUsed + turn.entries.length ∧ st'.usedTags = tulvaTag H turn.context turn.ct :: st.usedTags ∧ st'.leaders = turn.ticket.output :: st.leaders := by
  unfold auctionStep at h
  split at h
  · rename_i hc
    have hst := Option.some.inj h
    subst hst
    exact ⟨hc, rfl, rfl, rfl, rfl⟩
  · cases h
theorem auctionStep_refused_iff (H : Hash) (cfg : AuctionConfig) (st : AuctionState) (turn : AuctionTurn cfg) : auctionStep H cfg st turn = none ↔ (lavRingVerify H cfg.lav cfg.ringKeys st.epoch turn.slot turn.ticket = false ∨ tulvaTag H turn.context turn.ct ∈ st.usedTags ∨ cfg.queryBudget < st.queriesUsed + turn.entries.length ∨ bitzVerify H cfg.tulva.params.q cfg.width turn.commitment turn.rows turn.claims = false ∨ tulvaCheck H cfg.tulva turn.context turn.ct turn.entries = false ∨ tulvaDecode cfg.tulva turn.ct turn.entries ≠ bitzPlainVec cfg.tulva.params.d turn.claims) := by
  unfold auctionStep auctionTurnCheck
  cases h1 : lavRingVerify H cfg.lav cfg.ringKeys st.epoch turn.slot turn.ticket <;>
  cases h4 : bitzVerify H cfg.tulva.params.q cfg.width turn.commitment turn.rows turn.claims <;>
  cases h5 : tulvaCheck H cfg.tulva turn.context turn.ct turn.entries <;>
  by_cases h2 : tulvaTag H turn.context turn.ct ∈ st.usedTags <;>
  by_cases h3 : st.queriesUsed + turn.entries.length ≤ cfg.queryBudget <;>
  by_cases h6 : tulvaDecode cfg.tulva turn.ct turn.entries =
    bitzPlainVec cfg.tulva.params.d turn.claims <;>
  simp [h2, h3, h6] <;> omega
theorem auctionRun_safe (H : Hash) (cfg : AuctionConfig) : ∀ (turns : List (AuctionTurn cfg)) (st st' : AuctionState), auctionRun H cfg st turns = some st' → AuctionInv cfg st → AuctionInv cfg st' ∧ st'.epoch = st.epoch + turns.length ∧ st'.leaders.length = st.leaders.length + turns.length ∧ (∀ tag ∈ st.usedTags, tag ∈ st'.usedTags) ∧ st.queriesUsed ≤ st'.queriesUsed := by
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
theorem auctionRun_turns_checked (H : Hash) (cfg : AuctionConfig) : ∀ (turns : List (AuctionTurn cfg)) (st st' : AuctionState), auctionRun H cfg st turns = some st' → ∀ turn ∈ turns, ∃ mid : AuctionState, st.epoch ≤ mid.epoch ∧ auctionTurnCheck H cfg mid turn = true := by
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
theorem auctionTurn_cleared_and_certified (H : Hash) (cfg : AuctionConfig) (st : AuctionState) (turn : AuctionTurn cfg) (sk : FastIntPoly cfg.tulva.params.d) (higher noises : List (FastIntPoly cfg.tulva.params.d)) (m eEnc : FastIntPoly cfg.tulva.params.d) (hChk : auctionTurnCheck H cfg st turn = true) (hDeg : higher.length + 1 ≤ cfg.tulva.threshold) (hEnc : RlweEncryptsWithError cfg.tulva.params sk turn.ct m eEnc) (hEncNorm : normInfFast eEnc.coeffs ≤ cfg.tulva.encNoiseBound) (hShares : TulvaSharesValid cfg.tulva.params turn.ct.c1 cfg.tulva.smudgeBound (sk :: higher) turn.entries noises) (hRoom : ∀ i : Fin cfg.tulva.params.d, -cfg.tulva.params.halfT ≤ (cfg.tulva.slack : Int) * m.spec i ∧ (cfg.tulva.slack : Int) * m.spec i < cfg.tulva.params.halfT) : m = bitzPlainVec cfg.tulva.params.d turn.claims ∧ (∀ row cl, (row, cl) ∈ turn.rows.zip turn.claims → ∃ n : Nat, n < 2 ^ cfg.width ∧ psiZ row = n ∧ cl.rq = n ∧ cl.fp.val = n) ∧ SmudgeSafe cfg.tulva.encNoiseBound cfg.tulva.smudgeBound cfg.tulva.secBits := by
  simp only [auctionTurnCheck, Bool.and_eq_true, decide_eq_true_eq] at hChk
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hBitz⟩, hTulva⟩, hDecEq⟩ := hChk
  have hDec := (tulvaCombine_ok_iff H cfg.tulva turn.context turn.ct turn.entries
    (tulvaDecode cfg.tulva turn.ct turn.entries)).mpr ⟨hTulva, rfl⟩
  obtain ⟨hm, hSafe, _⟩ := tulvaCombine_recovers_plaintext H cfg.tulva turn.context turn.ct
    turn.entries sk higher noises m eEnc _ hDec hDeg hEnc hEncNorm hShares hRoom
  obtain ⟨⟨_, hRows⟩, _⟩ := bitz_sameOpening_and_free_range_sound H cfg.tulva.params.q cfg.width
    turn.commitment turn.rows turn.claims hBitz
  exact ⟨hm.symm.trans hDecEq, hRows, hSafe⟩
def auctionRun_leaders_unique (H : Hash) (cfg : AuctionConfig) (ts₁ : List (AuctionTurn cfg)) : ∀ (ts₂ : List (AuctionTurn cfg)) (st₁ st₂ f₁ f₂ : AuctionState), st₁.epoch = st₂.epoch → st₁.leaders = st₂.leaders → (ts₁.map fun t => (t.slot, t.ticket.keyIndex)) = (ts₂.map fun t => (t.slot, t.ticket.keyIndex)) → auctionRun H cfg st₁ ts₁ = some f₁ → auctionRun H cfg st₂ ts₂ = some f₂ → (∀ epoch t, t ∈ ts₁ → lavRingVerify H cfg.lav cfg.ringKeys epoch t.slot t.ticket = true → LavRewind H cfg.lav (lavRingDigest H cfg.ringKeys) epoch t.slot t.ticket.proof) → (∀ epoch t, t ∈ ts₂ → lavRingVerify H cfg.lav cfg.ringKeys epoch t.slot t.ticket = true → LavRewind H cfg.lav (lavRingDigest H cfg.ringKeys) epoch t.slot t.ticket.proof) → PSum (f₁.leaders = f₂.leaders) (PSum (MsisBreakWitness cfg.lav) (TranscriptCollision
    H)) := by
  match ts₁ with
  | [] =>
    intro ts₂ st₁ st₂ f₁ f₂ _ hL hMap h₁ h₂ _ _
    cases ts₂ with
    | nil =>
      have e₁ : st₁ = f₁ := Option.some.inj h₁
      have e₂ : st₂ = f₂ := Option.some.inj h₂
      exact PSum.inl (by rw [← e₁, ← e₂]; exact hL)
    | cons _ _ => simp at hMap
  | t₁ :: ts₁ =>
    intro ts₂ st₁ st₂ f₁ f₂ hE hL hMap h₁ h₂ forks₁ forks₂
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
          · exact auctionRun_leaders_unique H cfg ts₁ ts₂ m₁ m₂ f₁ f₂ (by omega) (by rw [hLead₁, hLead₂, hOut, hL]) hTail h₁ h₂
              (fun e t ht => forks₁ e t (by simp [ht])) (fun e t ht => forks₂ e t (by simp [ht]))
          · have ff₁ := forks₁ st₁.epoch t₁ (by simp) hc₁.1.1.1.1.1
            have ff₂ := forks₂ st₂.epoch t₂ (by simp) hv₂
            rw [hE, hSlot] at ff₁
            cases lavRingVerify_unique H cfg.lav cfg.ringKeys st₂.epoch t₂.slot t₁.ticket t₂.ticket hIdx hv₁ hv₂ ff₁ ff₂ with
            | inl he => exact False.elim (hOut he)
            | inr w => exact .inr w
termination_by structural ts₁
structure BondedAuctionState where
  auction : AuctionState
  slashedTotal : Nat
  refunds : List (Nat × Nat)
  closedTags : List (List UInt8)
  released : Nat := 0
  pending : Option (List UInt8 × List BondedCommitteeMember)
inductive BondedAuctionAction (cfg : AuctionConfig) where
  | commit (tag : List UInt8) (members : List BondedCommitteeMember)
  | resolve (turn : AuctionTurn cfg) (opens : Nat → Option (BondedShareOpening cfg.tulva.params.d))
def bondedAuctionStep (H : Hash) (cfg : AuctionConfig) (st : BondedAuctionState) : BondedAuctionAction cfg → BondedAuctionState
  | .commit tag ms =>
    if st.pending.isNone && decide (tag ∉ st.closedTags ∧
        st.released + ms.length ≤ cfg.queryBudget) && bondedLockCheck cfg.tulva.threshold ms then
      { st with pending := some (tag, ms), closedTags := tag :: st.closedTags } else st
  | .resolve turn opens =>
    match st.pending with
    | none => st
    | some (tag, ms) =>
      if tag = tulvaTag H turn.context turn.ct then
        let r := bondedAuctionResolve H cfg.tulva.params.q tag ms opens st.slashedTotal
        { st with
          pending := none
          slashedTotal := r.slashedTotal
          refunds := st.refunds ++ r.refunds
          released := st.released + ms.length
          auction := (auctionStep H cfg st.auction { turn with entries := r.entries }).getD st.auction }
      else st
def bondedAuctionRun (H : Hash) (cfg : AuctionConfig) : BondedAuctionState → List (BondedAuctionAction cfg) → BondedAuctionState
  | st, [] => st
  | st, a :: actions => bondedAuctionRun H cfg (bondedAuctionStep H cfg st a) actions
def BondedAuctionInv (cfg : AuctionConfig) (st : BondedAuctionState) : Prop :=
  ∀ tag ms, st.pending = some (tag, ms) → 0 < cfg.tulva.threshold ∧
    cfg.tulva.threshold ≤ ms.length ∧ (ms.map (·.memberId)).Nodup ∧ ∀ m ∈ ms, 0 < m.bond
theorem bondedAuctionStep_locked (H : Hash) (cfg : AuctionConfig) (st : BondedAuctionState) (a : BondedAuctionAction cfg) (h : BondedAuctionInv cfg st) : BondedAuctionInv cfg (bondedAuctionStep H cfg st a) := by
  cases a with
  | commit tag ms =>
    simp only [bondedAuctionStep]; split
    · rename_i hc
      intro tag' ms' hp
      have he := Option.some.inj hp
      cases he
      simp only [Bool.and_eq_true] at hc
      exact of_decide_eq_true hc.2
    · exact h
  | resolve turn opens =>
    simp only [bondedAuctionStep]; split
    · exact h
    · split
      · intro tag ms hp; cases hp
      · exact h
theorem bondedAuctionRun_locked (H : Hash) (cfg : AuctionConfig) (actions : List (BondedAuctionAction cfg)) (st : BondedAuctionState) (h : BondedAuctionInv cfg st) : BondedAuctionInv cfg (bondedAuctionRun H cfg st actions) := by
  induction actions generalizing st with
  | nil => exact h
  | cons a as ih => exact ih _ (bondedAuctionStep_locked H cfg st a h)
theorem bondedAuctionStep_monotone (H : Hash) (cfg : AuctionConfig) (st : BondedAuctionState) (a : BondedAuctionAction cfg) : st.slashedTotal ≤ (bondedAuctionStep H cfg st a).slashedTotal := by
  cases a with
  | commit tag ms => simp only [bondedAuctionStep]; split <;> exact Nat.le_refl _
  | resolve turn opens =>
    simp only [bondedAuctionStep]
    split
    · exact Nat.le_refl _
    · split
      · simp only [bondedAuctionResolve]; exact Nat.le_add_right _ _
      · exact Nat.le_refl _
theorem bondedAuctionRun_slashing_persists (H : Hash) (cfg : AuctionConfig) (actions : List (BondedAuctionAction cfg)) (st : BondedAuctionState) : st.slashedTotal ≤ (bondedAuctionRun H cfg st actions).slashedTotal := by
  induction actions generalizing st with
  | nil => exact Nat.le_refl _
  | cons a as ih => exact Nat.le_trans (bondedAuctionStep_monotone H cfg st a) (ih _)
end Obend.Crypto
end
