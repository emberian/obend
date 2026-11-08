module
public import Lean

/-! # Goldilocks arithmetic specifications

Pure arithmetic shared by the ZK application, its RTL and portable u32 GPU
refinement. Keeping it independent of the elaborator and hardware judge lets
arithmetic consumers build without loading those unrelated subsystems.
-/
@[expose] public section
namespace Obend.Apps.ZkNtt

/-! ## 2. Goldilocks Prime ($p = 2^{64} - 2^{32} + 1$) 128-to-64 Reduction Soundness -/

/-- The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = 18446744069414584321$. -/
def goldilocksPrime : Nat := 18446744069414584321

/-- The Goldilocks reduction constant $\epsilon = 2^{32} - 1 = 4294967295$. -/
def goldilocksEpsilon : Nat := 4294967295

/-- Fundamental Goldilocks identity: $2^{64} = p + \epsilon$ and $2^{64} \bmod p = \epsilon$. -/
theorem goldilocks_base_congruence :
    2 ^ 64 = goldilocksPrime + goldilocksEpsilon ∧
    (2 ^ 64) % goldilocksPrime = goldilocksEpsilon ∧
    (2 ^ 96 + 1) % goldilocksPrime = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Reference 128-to-64 Goldilocks step in `Nat`:
    for a 128-bit integer $x = \text{lo} + 2^{64} \cdot \text{hiLo32} + 2^{96} \cdot \text{hiHi32}$,
    since $2^{64} = p + \epsilon$, we have $\text{lo} + 2^{64} \cdot \text{hiLo32} \equiv \text{lo} + \epsilon \cdot \text{hiLo32} \pmod p$. -/
theorem goldilocks_reduce96_mod_sound (lo hiLo32 : Nat) :
    (lo + (2 ^ 64) * hiLo32) % goldilocksPrime =
      (lo + goldilocksEpsilon * hiLo32) % goldilocksPrime := by
  have hBase : 2 ^ 64 = goldilocksPrime + goldilocksEpsilon := by decide
  rw [hBase, Nat.right_distrib, ← Nat.add_assoc]
  have hSwap : lo + goldilocksPrime * hiLo32 + goldilocksEpsilon * hiLo32 =
      (lo + goldilocksEpsilon * hiLo32) + goldilocksPrime * hiLo32 := by omega
  rw [hSwap, Nat.add_mul_mod_self_left]

/-- Canonicalize any 64-bit natural number `x < 2^64` into `[0, p - 1]` (matching `canon64` in
    `GoldilocksField.obend` and `gl_canon` in `zk_ntt_coproc.sv`). -/
def goldilocksCanon64 (x : Nat) : Nat :=
  if goldilocksPrime ≤ x then x - goldilocksPrime else x

theorem goldilocksCanon64_spec {x : Nat} (hx : x < 2 ^ 64) :
    goldilocksCanon64 x < goldilocksPrime ∧
    goldilocksCanon64 x = x % goldilocksPrime := by
  unfold goldilocksCanon64
  split
  · rename_i hge
    have hlt : x - goldilocksPrime < goldilocksPrime := by unfold goldilocksPrime at *; omega
    refine ⟨hlt, ?_⟩
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
  · rename_i hlt'
    have hlt : x < goldilocksPrime := by omega
    exact ⟨hlt, (Nat.mod_eq_of_lt hlt).symm⟩

/-- Canonical 64-bit Goldilocks modular addition (matching `gl_add` in `zk_ntt_coproc.sv`). -/
def goldilocksAddSpec (a b : Nat) : Nat :=
  let ca := goldilocksCanon64 a
  let cb := goldilocksCanon64 b
  if goldilocksPrime ≤ ca + cb then ca + cb - goldilocksPrime else ca + cb

/-- Equivalence between the overflow-free 64-bit `.obend` `fieldAdd` (`remP <= ca ? ca - remP : ca + cb`)
    and the 65-bit RTL `gl_add` (`P <= ca + cb ? ca + cb - P : ca + cb`). -/
theorem goldilocksAddSpec_eq_obend {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    let ca := goldilocksCanon64 a
    let cb := goldilocksCanon64 b
    let remP := goldilocksPrime - cb
    (if remP ≤ ca then ca - remP else ca + cb) = goldilocksAddSpec a b := by
  have hca := (goldilocksCanon64_spec ha).1
  have hcb := (goldilocksCanon64_spec hb).1
  dsimp only [goldilocksAddSpec]
  split <;> split <;> omega

theorem goldilocksAddSpec_spec {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    goldilocksAddSpec a b < goldilocksPrime ∧
    goldilocksAddSpec a b = (a + b) % goldilocksPrime := by
  rcases goldilocksCanon64_spec ha with ⟨hcaLt, hcaMod⟩
  rcases goldilocksCanon64_spec hb with ⟨hcbLt, hcbMod⟩
  have hSumMod : (a + b) % goldilocksPrime =
      (goldilocksCanon64 a + goldilocksCanon64 b) % goldilocksPrime := by
    rw [Nat.add_mod, ← hcaMod, ← hcbMod]
  unfold goldilocksAddSpec
  dsimp only
  split
  · rename_i hge
    have hlt : goldilocksCanon64 a + goldilocksCanon64 b - goldilocksPrime < goldilocksPrime := by omega
    refine ⟨hlt, ?_⟩
    rw [hSumMod, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
  · rename_i hlt'
    have hlt : goldilocksCanon64 a + goldilocksCanon64 b < goldilocksPrime := by omega
    rw [hSumMod, Nat.mod_eq_of_lt hlt]
    exact ⟨hlt, rfl⟩

/-- Canonical 64-bit Goldilocks modular subtraction (matching `fieldSub` in `GoldilocksField.obend`
    and `gl_sub` in `zk_ntt_coproc.sv`). -/
def goldilocksSubSpec (a b : Nat) : Nat :=
  let ca := goldilocksCanon64 a
  let cb := goldilocksCanon64 b
  if cb ≤ ca then ca - cb else (goldilocksPrime - cb) + ca

theorem goldilocksSubSpec_spec {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    goldilocksSubSpec a b < goldilocksPrime ∧
    goldilocksSubSpec a b =
      (goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b) % goldilocksPrime := by
  rcases goldilocksCanon64_spec ha with ⟨hcaLt, _⟩
  rcases goldilocksCanon64_spec hb with ⟨hcbLt, _⟩
  unfold goldilocksSubSpec
  dsimp only
  split
  · rename_i hle
    have hlt : goldilocksCanon64 a - goldilocksCanon64 b < goldilocksPrime := by omega
    refine ⟨hlt, ?_⟩
    have hDecomp : goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b =
        (goldilocksCanon64 a - goldilocksCanon64 b) + goldilocksPrime * 1 := by omega
    rw [hDecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rename_i hgt
    have hlt : (goldilocksPrime - goldilocksCanon64 b) + goldilocksCanon64 a < goldilocksPrime := by omega
    refine ⟨hlt, ?_⟩
    have hEq : goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b =
        (goldilocksPrime - goldilocksCanon64 b) + goldilocksCanon64 a := by omega
    rw [hEq, Nat.mod_eq_of_lt hlt]

/-- Complete 128-to-64 Goldilocks shift/mask modular reduction specification matching
    `goldilocksReduce128` in `GoldilocksField.obend` and `gl_reduce128` in `zk_ntt_coproc.sv`:
    * `hiLo = hi & 0xFFFFFFFF = hi % 2^32`
    * `hiHi = (hi >>> 32) & 0xFFFFFFFF = hi / 2^32` (for `hi < 2^64`)
    * `mid = (hiLo << 32) - hiLo = hiLo * 2^32 - hiLo`
    * `result = gl_sub(gl_add(lo, mid), hiHi)` -/
def goldilocksReduce128Spec (lo hi : Nat) : Nat :=
  let hiLo := hi % 4294967296
  let hiHi := hi / 4294967296
  let mid := hiLo * 4294967296 - hiLo
  goldilocksSubSpec (goldilocksAddSpec lo mid) hiHi

/-- The arithmetic core of the reduction, over atoms: with `hi = hiLo + 2^32 hiHi`, `t1 = (lo + mid) mod p`
(`t1 + p q = lo + mid`) and `mid = 2^32 hiLo - hiLo`, the two sides differ by a multiple of `p`
(`2^64 = p + 2^32 - 1` and `2^96 = (2^32 + 1) p - 1`). -/
theorem goldilocksReduce128_identity (lo hi hiLo hiHi t1 q : Nat)
    (hHiLo : hiLo < 4294967296) (hHiHi : hiHi < 4294967296)
    (hhi : hiLo + 4294967296 * hiHi = hi)
    (ht1 : t1 + goldilocksPrime * q = lo + (hiLo * 4294967296 - hiLo)) :
    (t1 + goldilocksPrime - hiHi) % goldilocksPrime = (lo + 2 ^ 64 * hi) % goldilocksPrime := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have key : lo + 2 ^ 64 * hi + goldilocksPrime * 1 =
      (t1 + goldilocksPrime - hiHi) + goldilocksPrime * (q + hiLo + 4294967297 * hiHi) := by
    rw [h64]; unfold goldilocksPrime at *; omega
  rw [← Nat.add_mul_mod_self_left (lo + 2 ^ 64 * hi) goldilocksPrime 1, key, Nat.add_mul_mod_self_left]

/-- **`goldilocksReduce128Spec_sound`**: for every `lo, hi < 2^64` the shift/mask reduction is canonical
and equals `(lo + 2^64 * hi) % p`. -/
theorem goldilocksReduce128Spec_sound {lo hi : Nat}
    (hLo : lo < 2 ^ 64) (hHi : hi < 2 ^ 64) :
    goldilocksReduce128Spec lo hi < goldilocksPrime ∧
    goldilocksReduce128Spec lo hi = (lo + 2 ^ 64 * hi) % goldilocksPrime := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hHiLo : hi % 4294967296 < 4294967296 := Nat.mod_lt hi (by decide)
  have hHiHi : hi / 4294967296 < 4294967296 :=
    Nat.div_lt_of_lt_mul (by rw [h64] at hHi; omega)
  unfold goldilocksReduce128Spec
  dsimp only
  have hMidLt : hi % 4294967296 * 4294967296 - hi % 4294967296 < 2 ^ 64 := by rw [h64]; omega
  have hHiHiLt : hi / 4294967296 < 2 ^ 64 := by rw [h64]; omega
  obtain ⟨ht1LtP, ht1Mod⟩ := goldilocksAddSpec_spec hLo hMidLt
  have ht1Lt64 :
      goldilocksAddSpec lo (hi % 4294967296 * 4294967296 - hi % 4294967296) < 2 ^ 64 := by
    unfold goldilocksPrime at ht1LtP; rw [h64]; omega
  obtain ⟨hSubLtP, hSubMod⟩ := goldilocksSubSpec_spec ht1Lt64 hHiHiLt
  refine ⟨hSubLtP, ?_⟩
  rw [hSubMod]
  have hc1 : goldilocksCanon64 (goldilocksAddSpec lo (hi % 4294967296 * 4294967296 - hi % 4294967296)) =
      goldilocksAddSpec lo (hi % 4294967296 * 4294967296 - hi % 4294967296) := by
    unfold goldilocksCanon64; split <;> omega
  have hc2 : goldilocksCanon64 (hi / 4294967296) = hi / 4294967296 := by
    unfold goldilocksCanon64 goldilocksPrime; split <;> omega
  rw [hc1, hc2, ht1Mod]
  exact goldilocksReduce128_identity lo hi (hi % 4294967296) (hi / 4294967296) _ _ hHiLo hHiHi
    (Nat.mod_add_div hi 4294967296)
    (Nat.mod_add_div (lo + (hi % 4294967296 * 4294967296 - hi % 4294967296)) goldilocksPrime)

/-! ## 2b. Multiplication and the transcript at the `Nat` level (the model the golden runs) -/

/-- `x mod p`. -/
def glN (x : Nat) : Nat := x % goldilocksPrime

/-- `(a * b) mod p`: the specification `glMul`'s limb network implements. -/
def goldilocksMulSpec (a b : Nat) : Nat := glN (glN a * glN b)


end Obend.Apps.ZkNtt
