module
/-
# `ObendKeccakMirProofs` — Constructive MIR Panic-Freedom, Typestate Refusal, & Zeroization Proofs

Machine-checked Lean 4.35 proofs directly over the Charon + Aeneas extracted MIR of
`crates/obend-keccak` (`ObendKeccak.Types`, `ObendKeccak.Funs`):

1. **Deterministic & Ranked Loop Verification**: Fuel-monotone `loopFuel_det_steps` and
   `loopFuel_total_rank` combinators (`0 Classical`, `0 sorry`, `0 axiom`).
2. **FIPS 202 Constants & Rotation Table Exactness**: Extracted `KECCAK_ROUND_CONSTANTS` (24 lanes)
   and `KECCAK_ROTATION_OFFSETS` (25 offsets), plus `SHAKE128` / `SHAKE256` / `SHA3-512` rates and
   domain suffixes (`0x06`, `0x1f`, `0x04`).
3. **Universal `keccak_f1600` Totality & Panic-Freedom**: `keccak_f1600_total` proves that for all
   $2^{1600}$ 25-lane states (`Array Std.U64 25#usize`), the extracted 24-round MIR loop terminates
   without integer overflow, shift overflow, or out-of-bounds indexing.
4. **Sponge Rate-Guard, Typestate Refusal, Midstate Roundtrip & Drop Zeroization**:
   - `valid_rate_iff` + explicit refusal witnesses for `RATE = 0`, `RATE > 200`, and `RATE % 8 != 0`;
   - `keccak_sponge_new_zero_suffix_fails` (`suffix = 0` rejected with `.fail .assertionFailure`);
   - `keccak_sponge_absorb_after_squeeze_fails` (late `absorb` after `squeezing = true` rejected
     across `KeccakSponge.absorb`, `Shake256.absorb`, `Cshake256.absorb`, and `Kmac256.absorb`);
   - `keccak_sponge_midstate_spec` + `keccak_sponge_from_midstate_roundtrip`;
   - `zero_lanes_spec`, `keccak_sponge_scrub_spec`, `keccak_sponge_drop_zeroizes`, and
     `midstate_drop_zeroizes` proving complete 25-lane wipe on `Drop`.
5. **Bit-Length Overflow Guard**: `bit_length_spec` (`n <= 2^61 - 1` succeeds vs `n >= 2^61`
   rejected with `.fail .assertionFailure`).
-/

public import Aeneas
public import ObendKeccak.Types
public import ObendKeccak.Funs
import all ObendKeccak.Types
import all ObendKeccak.Funs

public section

namespace ObendKeccak.MirProofs

open Aeneas Aeneas.Std Result ControlFlow Error
open obend_keccak

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## 1. Loop & Container Proof Combinators -/

theorem usize_ofNat_val (k : Nat) (hk : k < 2 ^ 64) :
    (UScalar.ofNat .Usize k).val = k := by
  change (BitVec.ofNat 64 k).toNat = k
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem u32_ofNat_val (k : Nat) (hk : k < 2 ^ 32) :
    (UScalar.ofNat .U32 k).val = k := by
  change (BitVec.ofNat 32 k).toNat = k
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem result_bind_total {α β : Type} (r : Result α) (f : α → Result β)
    (hr : ∃ x, r = .ok x) (hf : ∀ x, ∃ y, f x = .ok y) :
    ∃ y, (r >>= f) = .ok y := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hf x
  exact ⟨y, by simp [hx, hy]⟩

theorem checked_add_val {ty : UScalarTy} (a b : UScalar ty)
    (h : a.val + b.val < 2 ^ ty.numBits) :
    ∃ c, (a + b : Result (UScalar ty)) = .ok c ∧ c.val = a.val + b.val := by
  refine ⟨⟨a.bv + b.bv⟩, ?_, ?_⟩
  · simp only [hAdd_uscalar_eq, h, ite_true]
  · exact (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt h)

theorem checked_add_ofNat_usize (k : Nat) (hk : k + 1 < 2 ^ 64) :
    (UScalar.ofNat .Usize k + 1#usize : Result Std.Usize) =
      .ok (UScalar.ofNat .Usize (k + 1)) := by
  have hk0 : k < 2 ^ 64 := by omega
  have hlt : (UScalar.ofNat .Usize k).val + (1#usize).val < 2 ^ (UScalarTy.Usize.numBits) := by
    rw [usize_ofNat_val k hk0, usize_ofNat_val 1 (by decide)]
    exact hk
  simp only [hAdd_uscalar_eq, hlt, ite_true]
  apply congrArg Result.ok
  apply UScalar.eq_of_val_eq
  change ((BitVec.ofNat 64 k) + (BitVec.ofNat 64 1)).toNat = (BitVec.ofNat 64 (k + 1)).toNat
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hk0, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
    Nat.mod_eq_of_lt hk]

theorem array_index_getD {α : Type} {n : Std.Usize}
    (a : Aeneas.Std.Array α n) (i : Std.Usize) (d : α) (hi : i.val < n.val) :
    Aeneas.Std.Array.index_usize a i = .ok (a.val.getD i.val d) := by
  have h : i.val < a.val.length := by rw [a.property]; exact hi
  simp only [Aeneas.Std.Array.index_usize, dite_eq_left_of_eq_true (eq_true h), List.getElem_eq_getD d]

theorem array_index_total {α : Type} {n : Std.Usize}
    (a : Aeneas.Std.Array α n) (i : Std.Usize) (hi : i.val < n.val) :
    ∃ x, Aeneas.Std.Array.index_usize a i = .ok x := by
  have h : i.val < a.val.length := by rw [a.property]; exact hi
  exact ⟨a.val[i.val]'h, dite_eq_left_of_eq_true (eq_true h)⟩

theorem array_update_eq {α : Type} {n : Std.Usize}
    (a : Aeneas.Std.Array α n) (i : Std.Usize) (v : α) (b : Aeneas.Std.Array α n)
    (hi : i.val < n.val) (hb : b.val = a.val.set i.val v) :
    Aeneas.Std.Array.update a i v = .ok b := by
  have hlt : i.val < a.val.length := by rw [a.property]; exact hi
  have h0 : Aeneas.Std.Array.update a i v =
      .ok ⟨a.val.set i.val v, by rw [List.length_set]; exact a.property⟩ :=
    dite_eq_left_of_eq_true (eq_true hlt)
  rw [h0]
  exact congrArg Result.ok (Aeneas.Std.Array.ext hb.symm)

theorem array_index_mut_eq {α : Type} {n : Std.Usize}
    (a : Aeneas.Std.Array α n) (i : Std.Usize) (d : α) (hi : i.val < n.val) :
    ∃ back : α → Aeneas.Std.Array α n,
      Aeneas.Std.Array.index_mut_usize a i = .ok (a.val.getD i.val d, back) ∧
      ∀ v, (back v).val = a.val.set i.val v := by
  have h : i.val < a.val.length := by rw [a.property]; exact hi
  refine ⟨fun v => ⟨a.val.set i.val v, by rw [List.length_set]; exact a.property⟩, ?_, fun _ => rfl⟩
  simp only [Aeneas.Std.Array.index_mut_usize, dite_eq_left_of_eq_true (eq_true h), List.getElem_eq_getD d]

/-- Deterministic `N`-step loop evaluator: given exact step transitions `st 0 -> st 1 -> ... -> st N`
    and exit `.done out` at `st N`, `loopFuel` evaluates `st k` to `.ok out` in `N - k + 1` fuel. -/
theorem loopFuel_det_steps {α β : Type} (body : α → Result (ControlFlow α β))
    (st : Nat → α) (out : β) (N : Nat)
    (hstep : ∀ k, k < N → body (st k) = .ok (.cont (st (k + 1))))
    (hdone : body (st N) = .ok (.done out)) :
    ∀ k, k ≤ N → loopFuel (N - k + 1) body (st k) = .ok out := by
  intro k hk
  obtain ⟨rem, hrem⟩ : ∃ rem, N - k = rem := ⟨N - k, rfl⟩
  induction rem generalizing k with
  | zero =>
    have hkeq : k = N := by omega
    subst hkeq
    simp only [Nat.sub_self, Nat.zero_add, loopFuel_succ, hdone, result_bind_ok]
  | succ rem ih =>
    have hklt : k < N := by omega
    have hrem' : N - (k + 1) = rem := by omega
    have hfuel : N - k + 1 = (rem + 1) + 1 := by omega
    rw [hfuel, loopFuel_succ, hstep k hklt, result_bind_ok]
    have hnext : N - (k + 1) + 1 = rem + 1 := by omega
    rw [← hnext]
    exact ih (k + 1) (by omega) hrem'

theorem loop_det_steps {α β : Type} (body : α → Result (ControlFlow α β))
    (st : Nat → α) (out : β) (N : Nat) (hfuel : N + 1 ≤ loopMaxFuel)
    (hstep : ∀ k, k < N → body (st k) = .ok (.cont (st (k + 1))))
    (hdone : body (st N) = .ok (.done out)) :
    loop body (st 0) = .ok out := by
  apply loop_ok_of_loopFuel hfuel
  simpa only [Nat.sub_zero] using loopFuel_det_steps body st out N hstep hdone 0 (Nat.zero_le N)

theorem loopFuel_total_rank {α β : Type} (body : α → Result (ControlFlow α β))
    (P : Nat → α → Prop) (Q : β → Prop)
    (hzero : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y)
    (hstep : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x')
    (n : Nat) (x : α) (hx : P n x) :
    ∃ y, loopFuel (n + 1) body x = .ok y ∧ Q y := by
  induction n generalizing x with
  | zero =>
    obtain ⟨y, hy, hq⟩ := hzero x hx
    exact ⟨y, by rw [loopFuel_succ, hy, result_bind_ok], hq⟩
  | succ n ih =>
    obtain ⟨x', hbody, hp⟩ := hstep n x hx
    obtain ⟨y, hy, hq⟩ := ih x' hp
    exact ⟨y, by rw [loopFuel_succ, hbody, result_bind_ok]; exact hy, hq⟩

/-! ## 2. Extracted FIPS 202 Constants & Rates -/

theorem shake128_rate_bytes_eq : obend_keccak.SHAKE128_RATE_BYTES = 168#usize := by
  unfold obend_keccak.SHAKE128_RATE_BYTES
  rfl

theorem shake256_rate_bytes_eq : obend_keccak.SHAKE256_RATE_BYTES = 136#usize := by
  unfold obend_keccak.SHAKE256_RATE_BYTES
  rfl

theorem sha3_512_rate_bytes_eq : obend_keccak.SHA3_512_RATE_BYTES = 72#usize := by
  unfold obend_keccak.SHA3_512_RATE_BYTES
  rfl

theorem domain_suffixes_eq :
    obend_keccak.SHA3_SUFFIX = 6#u8 ∧
    obend_keccak.SHAKE_SUFFIX = 31#u8 ∧
    obend_keccak.CSHAKE_SUFFIX = 4#u8 := by
  unfold obend_keccak.SHA3_SUFFIX obend_keccak.SHAKE_SUFFIX obend_keccak.CSHAKE_SUFFIX
  exact ⟨rfl, rfl, rfl⟩

theorem keccak_round_constants_index (r : Nat) (hr : r < 24) :
    Aeneas.Std.Array.index_usize obend_keccak.KECCAK_ROUND_CONSTANTS (UScalar.ofNat .Usize r) =
      .ok (obend_keccak.KECCAK_ROUND_CONSTANTS.val.getD r 0#u64) := by
  have hr64 : r < 2 ^ 64 := by omega
  have hval := usize_ofNat_val r hr64
  have hlt : (UScalar.ofNat .Usize r).val < (24#usize).val := by
    rw [hval, usize_ofNat_val 24 (by decide)]
    exact hr
  have hget := array_index_getD obend_keccak.KECCAK_ROUND_CONSTANTS (UScalar.ofNat .Usize r) 0#u64 hlt
  rw [hval] at hget
  exact hget

theorem keccak_rotation_offsets_val :
    obend_keccak.KECCAK_ROTATION_OFFSETS.val.map UScalar.val =
      [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
       41, 45, 15, 21, 8, 18, 2, 61, 56, 14] := by
  unfold obend_keccak.KECCAK_ROTATION_OFFSETS
  rfl

/-! ## 3. Universal `keccak_f1600` Panic-Freedom Across All $2^{1600}$ States -/

abbrev Lanes25Tuple :=
  Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
  Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
  Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
  Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
  Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64

theorem keccak_f1600_loop_total
    (a00 a10 a20 a30 a40 a01 a11 a21 a31 a41 a02 a12 a22 a32 a42
     a03 a13 a23 a33 a43 a04 a14 a24 a34 a44 : Std.U64) :
    ∃ out : Lanes25Tuple,
      obend_keccak.keccak_f1600_loop
        a00 a10 a20 a30 a40 a01 a11 a21 a31 a41 a02 a12 a22 a32 a42
        a03 a13 a23 a33 a43 a04 a14 a24 a34 a44 0#usize = .ok out := by
  let body := fun (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
                   x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, r) =>
    obend_keccak.keccak_f1600_loop.body
      x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
      x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 r
  let P := fun (n : Nat)
    (st : Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
          Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
          Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
          Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 ×
          Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.U64 × Std.Usize) =>
    st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val + n = 24
  have hz : ∀ st, P 0 st → ∃ y, body st = .ok (.done y) ∧ True := by
    rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
            x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, r⟩ hr
    change r.val + 0 = 24 at hr
    have hnot : ¬ (r < 24#usize) := by
      rw [UScalar.lt_iff_val, usize_ofNat_val 24 (by decide)]
      omega
    refine ⟨(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
             x15, x16, x17, x18, x19, x20, x21, x22, x23, x24), ?_, True.intro⟩
    simp only [body, obend_keccak.keccak_f1600_loop.body, hnot, ite_false]
  have hstep : ∀ n st, P (n + 1) st → ∃ st', body st = .ok (.cont st') ∧ P n st' := by
    rintro n ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
              x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, r⟩ hr
    change r.val + (n + 1) = 24 at hr
    have hrlt : r < 24#usize := by
      rw [UScalar.lt_iff_val, usize_ofNat_val 24 (by decide)]
      omega
    obtain ⟨rc, hrc⟩ := array_index_total obend_keccak.KECCAK_ROUND_CONSTANTS r (by
      rw [usize_ofNat_val 24 (by decide)]; omega)
    obtain ⟨r', hr', vr'⟩ := checked_add_val r 1#usize (by
      rw [usize_ofNat_val 1 (by decide)]; change r.val + 1 < 2 ^ 64; omega)
    simp only [body, obend_keccak.keccak_f1600_loop.body, hrlt, ite_true,
      bind_eq_result_bind, lift_eq_ok, result_bind_ok, hrc, hr']
    refine ⟨_, rfl, ?_⟩
    change r'.val + n = 24
    rw [usize_ofNat_val 1 (by decide)] at vr'
    omega
  obtain ⟨out, hout, _⟩ := loopFuel_total_rank body P (fun _ => True) hz hstep 24
    (a00, a10, a20, a30, a40, a01, a11, a21, a31, a41, a02, a12, a22, a32, a42,
     a03, a13, a23, a33, a43, a04, a14, a24, a34, a44, 0#usize) (by rfl)
  refine ⟨out, ?_⟩
  unfold obend_keccak.keccak_f1600_loop
  exact loop_ok_of_loopFuel (fuel := 25) (by decide) hout

/-- **Universal `keccak_f1600` Panic-Freedom**: for every 25-lane input array (`2^1600` states),
    the extracted Rust MIR `obend_keccak::keccak_f1600` terminates with `.ok state'`. -/
theorem keccak_f1600_total (state : Aeneas.Std.Array Std.U64 25#usize) :
    ∃ state', obend_keccak.keccak_f1600 state = .ok state' := by
  have hidx (k : Std.Usize) (hk : k.val < (25#usize).val) :
      ∃ v, Aeneas.Std.Array.index_usize state k = .ok v :=
    array_index_total state k hk
  obtain ⟨x0, hx0⟩ := hidx 0#usize (by decide)
  obtain ⟨x1, hx1⟩ := hidx 1#usize (by decide)
  obtain ⟨x2, hx2⟩ := hidx 2#usize (by decide)
  obtain ⟨x3, hx3⟩ := hidx 3#usize (by decide)
  obtain ⟨x4, hx4⟩ := hidx 4#usize (by decide)
  obtain ⟨x5, hx5⟩ := hidx 5#usize (by decide)
  obtain ⟨x6, hx6⟩ := hidx 6#usize (by decide)
  obtain ⟨x7, hx7⟩ := hidx 7#usize (by decide)
  obtain ⟨x8, hx8⟩ := hidx 8#usize (by decide)
  obtain ⟨x9, hx9⟩ := hidx 9#usize (by decide)
  obtain ⟨x10, hx10⟩ := hidx 10#usize (by decide)
  obtain ⟨x11, hx11⟩ := hidx 11#usize (by decide)
  obtain ⟨x12, hx12⟩ := hidx 12#usize (by decide)
  obtain ⟨x13, hx13⟩ := hidx 13#usize (by decide)
  obtain ⟨x14, hx14⟩ := hidx 14#usize (by decide)
  obtain ⟨x15, hx15⟩ := hidx 15#usize (by decide)
  obtain ⟨x16, hx16⟩ := hidx 16#usize (by decide)
  obtain ⟨x17, hx17⟩ := hidx 17#usize (by decide)
  obtain ⟨x18, hx18⟩ := hidx 18#usize (by decide)
  obtain ⟨x19, hx19⟩ := hidx 19#usize (by decide)
  obtain ⟨x20, hx20⟩ := hidx 20#usize (by decide)
  obtain ⟨x21, hx21⟩ := hidx 21#usize (by decide)
  obtain ⟨x22, hx22⟩ := hidx 22#usize (by decide)
  obtain ⟨x23, hx23⟩ := hidx 23#usize (by decide)
  obtain ⟨x24, hx24⟩ := hidx 24#usize (by decide)
  obtain ⟨⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14,
           y15, y16, y17, y18, y19, y20, y21, y22, y23, y24⟩, hloop⟩ :=
    keccak_f1600_loop_total x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
      x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
  refine ⟨Aeneas.Std.Array.make 25#usize
    [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14,
     y15, y16, y17, y18, y19, y20, y21, y22, y23, y24], ?_⟩
  unfold obend_keccak.keccak_f1600
  simp only [hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12,
    hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23, hx24,
    hloop, bind_eq_result_bind, result_bind_ok]

/-! ## 4. `zero_lanes`, `scrub`, and `Drop` Zeroization Proofs -/

private theorem set_drop_ZeroLanes : ∀ (xs : List Std.U64) (k : Nat),
    k < xs.length →
    (List.replicate k 0#u64 ++ xs.drop k).set k 0#u64 =
      List.replicate (k + 1) 0#u64 ++ xs.drop (k + 1)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: xs, 0, _ => by simp
  | x :: xs, k + 1, h => by
    have ih := set_drop_ZeroLanes xs k (Nat.lt_of_succ_lt_succ h)
    simpa only [List.replicate_succ, List.cons_append, List.drop_succ_cons, List.set_cons_succ] using
      congrArg (0#u64 :: ·) ih

private theorem replicate_plus_drop_len (lanes : Aeneas.Std.Array Std.U64 25#usize) (k : Nat) (hk : k ≤ 25) :
    (List.replicate k 0#u64 ++ lanes.val.drop k).length = (25#usize).val := by
  have hlen : lanes.val.length = 25 := lanes.property
  rw [usize_ofNat_val 25 (by decide)]
  simp only [List.length_append, List.length_replicate, List.length_drop, hlen]
  omega

/-- **Complete 25-Lane Wipe (`zero_lanes_spec`)**: `obend_keccak::zero_lanes` overwrites all 25
    lanes with `0#u64` for every initial array `lanes`. -/
theorem zero_lanes_spec (lanes : Aeneas.Std.Array Std.U64 25#usize) :
    obend_keccak.zero_lanes lanes = .ok (Aeneas.Std.Array.repeat 25#usize 0#u64) := by
  let arrAt (k : Nat) : Aeneas.Std.Array Std.U64 25#usize :=
    if hk : k ≤ 25 then
      ⟨List.replicate k 0#u64 ++ lanes.val.drop k, replicate_plus_drop_len lanes k hk⟩
    else
      Aeneas.Std.Array.repeat 25#usize 0#u64
  let st (k : Nat) : Aeneas.Std.Array Std.U64 25#usize × Std.Usize :=
    (arrAt k, UScalar.ofNat .Usize k)
  let body := fun (l1, i1) => obend_keccak.zero_lanes_loop.body l1 i1
  have hstep : ∀ k, k < 25 → body (st k) = .ok (.cont (st (k + 1))) := by
    intro k hk
    have hk25 : k ≤ 25 := Nat.le_of_lt hk
    have hk1_25 : k + 1 ≤ 25 := hk
    have hval := usize_ofNat_val k (by omega)
    have hlt : UScalar.ofNat .Usize k < 25#usize := by
      rw [UScalar.lt_iff_val, hval, usize_ofNat_val 25 (by decide)]
      exact hk
    have hupd : Aeneas.Std.Array.update (arrAt k) (UScalar.ofNat .Usize k) 0#u64 = .ok (arrAt (k + 1)) := by
      apply array_update_eq
      · rw [hval, usize_ofNat_val 25 (by decide)]; exact hk
      · simp only [arrAt, hk25, hk1_25, ↓reduceDIte, hval]
        exact (set_drop_ZeroLanes lanes.val k (by rw [lanes.property]; exact hk)).symm
    have hadd := checked_add_ofNat_usize k (by omega)
    simp only [body, st, obend_keccak.zero_lanes_loop.body, hlt, ite_true,
      hupd, hadd, bind_eq_result_bind, result_bind_ok]
  have hdone : body (st 25) = .ok (.done (Aeneas.Std.Array.repeat 25#usize 0#u64)) := by
    have hnot : ¬ (UScalar.ofNat .Usize 25 < 25#usize) := by decide
    have harr25 : arrAt 25 = Aeneas.Std.Array.repeat 25#usize 0#u64 := by
      apply Aeneas.Std.Array.ext
      have h25 : (25 : Nat) ≤ 25 := Nat.le_refl 25
      simp only [arrAt, h25, ↓reduceDIte, Aeneas.Std.Array.repeat]
      have hdrop : lanes.val.drop 25 = [] := by
        rw [List.drop_eq_nil_iff, lanes.property]
        decide
      rw [hdrop, List.append_nil, usize_ofNat_val 25 (by decide)]
    simp only [body, st, obend_keccak.zero_lanes_loop.body, hnot, ite_false, harr25]
  have hloop : obend_keccak.zero_lanes_loop lanes 0#usize = .ok (Aeneas.Std.Array.repeat 25#usize 0#u64) := by
    have h0 : arrAt 0 = lanes := by
      apply Aeneas.Std.Array.ext
      simp [arrAt]
    unfold obend_keccak.zero_lanes_loop
    rw [← h0]
    exact loop_det_steps body st (Aeneas.Std.Array.repeat 25#usize 0#u64) 25 (by decide) hstep hdone
  unfold obend_keccak.zero_lanes
  exact hloop

/-- **`KeccakSponge::scrub` Zeroizes All Lanes, Position, Domain Suffix, and Phase**. -/
theorem keccak_sponge_scrub_spec {RATE : Std.Usize} (sp : obend_keccak.KeccakSponge RATE) :
    obend_keccak.KeccakSponge.scrub sp =
      .ok { lanes := Aeneas.Std.Array.repeat 25#usize 0#u64, pos := 0#usize, suffix := 0#u8, squeezing := false } := by
  unfold obend_keccak.KeccakSponge.scrub
  rw [bind_eq_result_bind, zero_lanes_spec sp.lanes, result_bind_ok]

/-- **`KeccakSponge` `Drop::drop` Zeroizes All Key/State Material**. -/
theorem keccak_sponge_drop_zeroizes {RATE : Std.Usize} (sp : obend_keccak.KeccakSponge RATE) :
    obend_keccak.KeccakSponge.Insts.CoreOpsDropDrop.drop sp =
      .ok { lanes := Aeneas.Std.Array.repeat 25#usize 0#u64, pos := 0#usize, suffix := 0#u8, squeezing := false } := by
  unfold obend_keccak.KeccakSponge.Insts.CoreOpsDropDrop.drop
  exact keccak_sponge_scrub_spec sp

/-- **`Midstate` `Drop::drop` Zeroizes All 25 Keyed Lanes and Domain Suffix**. -/
theorem midstate_drop_zeroizes {RATE : Std.Usize} (m : obend_keccak.Midstate RATE) :
    obend_keccak.Midstate.Insts.CoreOpsDropDrop.drop m =
      .ok { lanes := Aeneas.Std.Array.repeat 25#usize 0#u64, suffix := 0#u8 } := by
  unfold obend_keccak.Midstate.Insts.CoreOpsDropDrop.drop
  rw [bind_eq_result_bind, zero_lanes_spec m.lanes, result_bind_ok]

/-! ## 5. Sponge Rate Guard, Typestate Refusals & Midstate Roundtrip -/

/-- Exact validity predicate for `KeccakSponge<RATE>` (`0 < RATE <= 200` and `8 | RATE`). -/
@[expose] def ValidRate (RATE : Std.Usize) : Prop :=
  0 < RATE.val ∧ RATE.val ≤ 200 ∧ RATE.val % 8 = 0

theorem valid_rate_iff (RATE : Std.Usize) :
    obend_keccak.KeccakSponge.VALID_RATE RATE = .ok () ↔ ValidRate RATE := by
  unfold obend_keccak.KeccakSponge.VALID_RATE ValidRate
  constructor
  · intro h
    by_cases hgt : RATE > 0#usize
    · have hgt' : 0 < RATE.val := by
        simpa only [GT.gt, UScalar.lt_iff_val, usize_ofNat_val 0 (by decide)] using hgt
      rw [massert_pos hgt, bind_eq_result_bind, result_bind_ok] at h
      by_cases hle : RATE ≤ 200#usize
      · have hle' : RATE.val ≤ 200 := by
          simpa only [UScalar.le_iff_val, usize_ofNat_val 200 (by decide)] using hle
        rw [massert_pos hle, bind_eq_result_bind, result_bind_ok] at h
        have hmod_ok : (RATE % 8#usize : Result Std.Usize) = .ok ⟨RATE.bv % (8#usize).bv⟩ := by
          simp [hMod_uscalar_eq, usize_ofNat_val 8 (by decide)]
        rw [hmod_ok, bind_eq_result_bind, result_bind_ok] at h
        by_cases hrem : (⟨RATE.bv % (8#usize).bv⟩ : Std.Usize) = 0#usize
        · have hrem' : RATE.val % 8 = 0 := by
            have hv := congrArg UScalar.val hrem
            change (RATE.bv % (8#usize).bv).toNat = 0 at hv
            rw [BitVec.toNat_umod] at hv
            exact hv
          exact ⟨hgt', hle', hrem'⟩
        · rw [massert_neg hrem] at h
          cases h
      · rw [massert_neg hle, bind_eq_result_bind] at h
        cases h
    · rw [massert_neg hgt, bind_eq_result_bind] at h
      cases h
  · rintro ⟨hgt', hle', hrem'⟩
    have hgt : RATE > 0#usize := by
      simpa only [GT.gt, UScalar.lt_iff_val, usize_ofNat_val 0 (by decide)] using hgt'
    have hle : RATE ≤ 200#usize := by
      simpa only [UScalar.le_iff_val, usize_ofNat_val 200 (by decide)] using hle'
    have hmod_ok : (RATE % 8#usize : Result Std.Usize) = .ok ⟨RATE.bv % (8#usize).bv⟩ := by
      simp [hMod_uscalar_eq, usize_ofNat_val 8 (by decide)]
    have hrem : (⟨RATE.bv % (8#usize).bv⟩ : Std.Usize) = 0#usize := by
      apply UScalar.eq_of_val_eq
      change (RATE.bv % (8#usize).bv).toNat = 0
      rw [BitVec.toNat_umod]
      exact hrem'
    rw [massert_pos hgt, bind_eq_result_bind, result_bind_ok,
        massert_pos hle, bind_eq_result_bind, result_bind_ok,
        hmod_ok, bind_eq_result_bind, result_bind_ok, massert_pos hrem]

/-- Concrete rate-guard refusal witnesses: `0`, `208 (> 200)`, and `137 (not a multiple of 8)` fail. -/
theorem valid_rate_refusal_witnesses :
    obend_keccak.KeccakSponge.VALID_RATE 0#usize = .fail .assertionFailure ∧
    obend_keccak.KeccakSponge.VALID_RATE 208#usize = .fail .assertionFailure ∧
    obend_keccak.KeccakSponge.VALID_RATE 137#usize = .fail .assertionFailure := by
  unfold obend_keccak.KeccakSponge.VALID_RATE
  exact ⟨rfl, rfl, rfl⟩

/-- Zero delimited suffix is refused by `KeccakSponge::new`. -/
theorem keccak_sponge_new_zero_suffix_fails :
    obend_keccak.KeccakSponge.new 136#usize 0#u8 = .fail .assertionFailure := by
  have hv : obend_keccak.KeccakSponge.VALID_RATE 136#usize = .ok () :=
    (valid_rate_iff 136#usize).mpr ⟨by decide, by decide, by decide⟩
  have hne0 : ¬ ((0#u8 != 0#u8) = true) := by
    rw [bne_iff_ne]
    intro h
    exact h rfl
  unfold obend_keccak.KeccakSponge.new
  rw [bind_eq_result_bind, hv, result_bind_ok, bind_eq_result_bind, massert_neg hne0]
  rfl

/-- **Phase Typestate Safety (`absorb` after `squeeze` fails)**: for any valid rate `RATE`, any
    sponge with `squeezing = true`, and any slice `data`, `KeccakSponge::absorb` fails with
    `.fail .assertionFailure`. -/
theorem keccak_sponge_absorb_after_squeeze_fails {RATE : Std.Usize}
    (hrate : ValidRate RATE) (sp : obend_keccak.KeccakSponge RATE)
    (hsq : sp.squeezing = true) (data : Slice Std.U8) :
    obend_keccak.KeccakSponge.absorb sp data = .fail .assertionFailure := by
  have hv := (valid_rate_iff RATE).mpr hrate
  unfold obend_keccak.KeccakSponge.absorb
  rw [bind_eq_result_bind, hv, result_bind_ok, bind_eq_result_bind, massert_not_of_eq_true hsq]
  rfl

/-- Late `Shake256::absorb`, `Cshake256::absorb`, and `Kmac256::absorb` after squeezing all fail. -/
theorem xof_absorb_after_squeeze_fails (sp : obend_keccak.KeccakSponge 136#usize)
    (hsq : sp.squeezing = true) (data : Slice Std.U8) :
    obend_keccak.Shake256.absorb sp data = .fail .assertionFailure ∧
    obend_keccak.Cshake256.absorb sp data = .fail .assertionFailure ∧
    obend_keccak.Kmac256.absorb sp data = .fail .assertionFailure := by
  have h136 : ValidRate 136#usize := ⟨by decide, by decide, by decide⟩
  have habs := keccak_sponge_absorb_after_squeeze_fails h136 sp hsq data
  refine ⟨?_, ?_, ?_⟩
  · unfold obend_keccak.Shake256.absorb; rw [bind_eq_result_bind, habs]; rfl
  · unfold obend_keccak.Cshake256.absorb; rw [bind_eq_result_bind, habs]; rfl
  · unfold obend_keccak.Kmac256.absorb; rw [bind_eq_result_bind, habs]; rfl

/-- Exact `KeccakSponge::midstate` characterization: returns `some ⟨lanes, suffix⟩` iff absorbing
    on a rate boundary (`squeezing = false` and `pos = 0`), and `none` otherwise. -/
theorem keccak_sponge_midstate_spec {RATE : Std.Usize}
    (sp : obend_keccak.KeccakSponge RATE) (hsuf : sp.suffix ≠ 0#u8) :
    obend_keccak.KeccakSponge.midstate sp =
      .ok (if !sp.squeezing && decide (sp.pos = 0#usize) then some ⟨sp.lanes, sp.suffix⟩ else none) := by
  unfold obend_keccak.KeccakSponge.midstate obend_keccak.Midstate.new
  have hsuf_bne : (sp.suffix != 0#u8) = true := bne_iff_ne.mpr hsuf
  cases hsq : sp.squeezing
  · by_cases hpos : sp.pos = 0#usize
    · simp only [hpos, Bool.not_false, Bool.true_and, decide_true, ite_true,
        bind_eq_result_bind, massert_pos hsuf_bne, result_bind_ok]
      rfl
    · simp [hpos]
  · simp

/-- Resuming via `KeccakSponge::from_midstate` from a captured rate-aligned `midstate` reconstructs
    the exact sponge state `sp`. -/
theorem keccak_sponge_from_midstate_roundtrip {RATE : Std.Usize}
    (hrate : ValidRate RATE) (sp : obend_keccak.KeccakSponge RATE)
    (habs : sp.squeezing = false) (hpos : sp.pos = 0#usize) (hsuf : sp.suffix ≠ 0#u8) :
    obend_keccak.KeccakSponge.midstate sp = .ok (some ⟨sp.lanes, sp.suffix⟩) ∧
    obend_keccak.KeccakSponge.from_midstate (RATE := RATE) ⟨sp.lanes, sp.suffix⟩ = .ok sp := by
  refine ⟨?_, ?_⟩
  · rw [keccak_sponge_midstate_spec sp hsuf]
    simp [habs, hpos]
  · unfold obend_keccak.KeccakSponge.from_midstate
    rw [bind_eq_result_bind, (valid_rate_iff RATE).mpr hrate, result_bind_ok]
    cases sp
    simp only at habs hpos
    subst habs hpos
    rfl

/-! ## 6. `bit_length` Overflow Guard Characterization -/

/-- `bit_length` succeeds and multiplies by `8` whenever `byte_length <= 2^61 - 1`, and fails with
    `.fail .assertionFailure` whenever `byte_length >= 2^61`. -/
theorem bit_length_spec (byte_length : Std.Usize) :
    obend_keccak.bit_length byte_length =
      if byte_length.val ≤ 2305843009213693951 then
        .ok ⟨BitVec.ofNat 64 (byte_length.val * 8)⟩
      else
        .fail .assertionFailure := by
  unfold obend_keccak.bit_length
  have hcast1 : (UScalar.cast .Usize (UScalar.cast .U64 byte_length)) = byte_length := by
    apply UScalar.ext
    change ((byte_length.bv.setWidth 64).setWidth 64) = byte_length.bv
    simp
  rw [bind_eq_result_bind, lift_eq_ok, result_bind_ok,
      bind_eq_result_bind, lift_eq_ok, result_bind_ok,
      bind_eq_result_bind, massert_pos hcast1, result_bind_ok]
  have hcast_val : (UScalar.cast .U64 byte_length).val = byte_length.val := by
    change (byte_length.bv.setWidth 64).toNat = byte_length.bv.toNat
    simp
  by_cases hle : byte_length.val ≤ 2305843009213693951
  · have hle_u : UScalar.cast .U64 byte_length ≤ 2305843009213693951#u64 := by
      rw [UScalar.le_iff_val, hcast_val]
      change byte_length.val ≤ 2305843009213693951
      exact hle
    have hmul_lt : (UScalar.cast .U64 byte_length).val * (8#u64).val < 2 ^ (UScalarTy.U64.numBits) := by
      rw [hcast_val]
      change byte_length.val * 8 < 2 ^ 64
      omega
    simp only [hle, ite_true]
    rw [bind_eq_result_bind, massert_pos hle_u, result_bind_ok]
    simp only [hMul_uscalar_eq, hmul_lt, ite_true]
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    change ((UScalar.cast .U64 byte_length).bv * (8#u64).bv).toNat =
      (BitVec.ofNat 64 (byte_length.val * 8)).toNat
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
    have hbv : (UScalar.cast .U64 byte_length).bv.toNat = byte_length.val := hcast_val
    rw [hbv, BitVec.toNat_ofNat]
    change (byte_length.val * (8 % 2 ^ 64)) % 2 ^ 64 = (byte_length.val * 8) % 2 ^ 64
    rfl
  · have hnot_le : ¬ (UScalar.cast .U64 byte_length ≤ 2305843009213693951#u64) := by
      rw [UScalar.le_iff_val, hcast_val]
      change ¬ (byte_length.val ≤ 2305843009213693951)
      exact hle
    simp only [hle, ite_false]
    rw [bind_eq_result_bind, massert_neg hnot_le]
    rfl

end ObendKeccak.MirProofs
