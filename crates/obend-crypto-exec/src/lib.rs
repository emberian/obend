//! `obend-crypto-exec`: High-performance `#![forbid(unsafe_code)]`, `no_std + alloc`-compatible
//! native Rust cryptographic execution engine for `Obend`'s repaired 2026 Dual-Track Crypto Spine
//! & RFC 8949 §4.2 Deterministic CBOR wire format.
//!
//! ## Architecture (`K5`–`K7`, Closing `G3` `F1`–`F11`)
//! - [`goldilocks`]: Branch-clean 64-bit `Goldilocks` ($p = 2^{64} - 2^{32} + 1$), strict
//!   `CanonicalLift` rejecting $[p, 2^{64})$ (`F4` / `0 vs p` alias), 128-bit `GoldilocksExt2`
//!   ($\mathbb{F}_p[u]/(u^2 - 7)$), in-place radix-2 NTT / iNTT, and $O(2^v)$ sumcheck.
//! - [`transcript`]: Exact NIST FIPS 202 / SP 800-185 `cSHAKE256` matching `Obend.Digest.Cshake256`
//!   and compile-time typestate `FenziTranscript<Phase>` (`Unbound -> RelationBound -> InstanceBound`)
//!   making premature challenge squeezes a Rust compile error (`Fenzi 2026/1838` + `F3`/`F5`).
//! - [`canopy`]: `Canopy` (`2026/2790`) Track H Reed–Solomon Tensor + Merkle PCS with `ifold` row
//!   folding and `iacc` shared-subtree pruning (`>= 30%` fewer hashes than independent Merkle paths).
//! - [`pikkufold`]: `PikkuFold` (`2026/1809`) + `Akita` (`2026/1983`) Track L Lattice-SIS over
//!   partially-splitting $R_{q_{\text{lat}}} = \mathbb{Z}_{q_{\text{lat}}}[X]/(X^{64} + 1)$
//!   ($q_{\text{lat}} = 2^{60} - 107 \equiv 5 \pmod 8$), 0-mul Kronecker ternary projection,
//!   constructive `extract_sis_collision`, and salted zero-knowledge `SameOpening` Dark Bazaar clearing (`K7`).
//! - [`det_cbor`]: Strict RFC 8949 §4.2 Deterministic CBOR codec & `DualPcsReceipt` wire format.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

#[cfg(any(test, feature = "std"))]
extern crate std;

pub mod amend_cli;
pub mod canopy;
pub mod det_cbor;
pub mod goldilocks;
pub mod pikkufold;
pub mod transcript;

use canopy::{CanopyError, CanopyHashCollision, CanopyOpenedColumn, extract_canopy_hash_collision_with};
use pikkufold::{LatticeError, LatticeParams, RingElem, SisCollisionWitness, extract_sis_collision};

/// Product witness returned constructively by `extract_dual_forgery` (`HashBreak × SisBreak`,
/// closing `F2` without `Classical` or pigeonhole `Prop` erasure!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DualBreakWitness {
    pub hash_break: CanopyHashCollision,
    pub sis_break: SisCollisionWitness,
}

/// Error returned when attempting constructive dual extraction on non-forged inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DualExtractError {
    Canopy(CanopyError),
    Lattice(LatticeError),
}

/// Constructive L0 witness-carrying dual extractor (`K6`): maps a simultaneous Track H + Track L
/// double-opening discrepancy directly to concrete `(CanopyHashCollision, SisCollisionWitness)` data.
#[allow(clippy::too_many_arguments)]
pub fn extract_dual_forgery_with<H>(
    hash_fn: H,
    codeword_cols: usize,
    col_idx: usize,
    col_a: &CanopyOpenedColumn,
    path_a: &[[u8; 32]],
    col_b: &CanopyOpenedColumn,
    path_b: &[[u8; 32]],
    lattice_params: &LatticeParams,
    w1: &[RingElem],
    w2: &[RingElem],
    per_witness_bound: u64,
) -> Result<DualBreakWitness, DualExtractError>
where
    H: Fn(&[u8]) -> [u8; 32],
{
    let hash_break = extract_canopy_hash_collision_with(
        hash_fn,
        codeword_cols,
        col_idx,
        col_a,
        path_a,
        col_b,
        path_b,
    )
    .map_err(DualExtractError::Canopy)?;
    let sis_break = extract_sis_collision(lattice_params, w1, w2, per_witness_bound)
        .map_err(DualExtractError::Lattice)?;
    Ok(DualBreakWitness {
        hash_break,
        sis_break,
    })
}

#[cfg(test)]
mod redteam_and_bench_tests {
    use super::*;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use std::println;
    use std::time::Instant;

    use crate::canopy::{
        CanopyCommitment, CanopyOpenedColumn, CanopyParams, DomainKind, ProximityRegime,
        canopy_column_leaf_preimage, canopy_commit, canopy_node_preimage, canopy_open,
        canopy_verify, prove_independent_merkle_baseline, verify_independent_merkle_baseline,
    };
    use crate::det_cbor::{
        CborValue, DetCborError, DualPcsReceipt, check_redaction_span_confinement, decode_det_cbor,
        encode_det_cbor, prove_dual_pcs_receipt, verify_dual_pcs_receipt,
    };
    use crate::goldilocks::{
        CanonicalLift, GOLDILOCKS_PRIME, Goldilocks, GoldilocksExt2, SoundChallengeField,
        intt_in_place, mle_eval_base_at_ext2, ntt_in_place, prove_multilinear_sumcheck_ext2,
        verify_sumcheck_ext2,
    };
    use crate::pikkufold::{
        DarkBazaarMarket, GADGET_LIMB_MAX, HALF_Q_LAT, LatticeError, LatticeParams,
        MAX_SAFE_SIS_NORM, OrderSalt, OrderSide, PrivateOrderWitness, RingElem, SmudgeBudgetConfig,
        TernaryTrit, commit_private_order, commit_ring_witness, fold_witness_2_to_1,
        kronecker_ternary_fold_0mul, pack_goldilocks_to_ring_witness,
        prove_dark_bazaar_same_opening, unpack_ring_witness_to_goldilocks,
        verify_dark_bazaar_same_opening,
    };
    use crate::transcript::FenziTranscript;

    fn to_bits_le(mut val: u64, bit_len: usize) -> Vec<bool> {
        let mut out = Vec::with_capacity(bit_len);
        for _ in 0..bit_len {
            out.push((val & 1) == 1);
            val >>= 1;
        }
        out
    }

    /// **Red-Team `F1`**: `ModuleSISHard` vacuity via truncating `dotInt` (`[0; n] ++ [1]`)
    /// and degenerate matrix dimensions.
    #[test]
    fn test_f1_forgery_sis_trailing_limb_truncation_and_ragged_matrix_rejected() {
        let params = LatticeParams::expand_from_seed([0x11u8; 32], 2, 4).unwrap();

        // Exact claude_2 F1 forgery vector: delta = [0, 0, 0, 0, 1] (trailing limb past `cols = 4`)
        let mut forged_trailing = vec![RingElem::zero(); params.cols];
        forged_trailing.push(RingElem::one());
        assert_eq!(
            commit_ring_witness(&params, &forged_trailing),
            Err(LatticeError::WitnessLengthMismatch {
                expected: 4,
                actual: 5
            })
        );

        // Short truncated vector also rejected
        let forged_short = vec![RingElem::one(); params.cols - 1];
        assert_eq!(
            commit_ring_witness(&params, &forged_short),
            Err(LatticeError::WitnessLengthMismatch {
                expected: 4,
                actual: 3
            })
        );

        // Degenerate / ragged matrices rejected at parameter construction
        assert!(LatticeParams::from_validated_matrix(0, 4, vec![]).is_err());
        assert!(LatticeParams::from_validated_matrix(2, 3, vec![RingElem::one(); 6]).is_err());
        assert!(LatticeParams::from_validated_matrix(2, 4, vec![RingElem::one(); 7]).is_err());
    }

    /// **Red-Team `F2`**: Constructive `DualBreakWitness` extractor returns concrete inspectable
    /// `(CanopyHashCollision, SisCollisionWitness)` data rather than erased `Prop` disjunctions.
    #[test]
    fn test_f2_constructive_dual_extractor_returns_concrete_hash_and_sis_breaks() {
        // 1. Toy 8-bit colliding hash oracle so two distinct columns collide at the parent node
        let toy_hash = |pre: &[u8]| -> [u8; 32] {
            // Deliberately ignore byte index 9+ so distinct column values collide at leaf!
            let mut acc = 0u8;
            for &b in pre.iter().take(2) {
                acc = acc.wrapping_add(b);
            }
            [acc; 32]
        };
        let col_a = CanopyOpenedColumn {
            col_idx: 0,
            values: vec![Goldilocks::ONE, Goldilocks::TWO],
            salt: None,
        };
        let col_b = CanopyOpenedColumn {
            col_idx: 0,
            values: vec![Goldilocks::NON_RESIDUE, Goldilocks::TWO],
            salt: None,
        };
        let sib = [0x5Au8; 32];
        let _root = toy_hash(&canopy_node_preimage(
            &toy_hash(&canopy_column_leaf_preimage(0, &col_a.values, None)),
            &sib,
        ));

        // 2. Toy 1x2 SIS matrix [1, -1]: w1 = [1, 0] and w2 = [0, -1]? Wait:
        // [1, -1] * [1, 1]^T = 0! So w1 = [2, 1] and w2 = [1, 0] both give syndrome [1]!
        let a_row = vec![RingElem::one(), RingElem::one().neg()];
        let sis_params = LatticeParams::from_validated_matrix(1, 2, a_row).unwrap();
        let w1 = vec![RingElem::constant(2), RingElem::constant(1)];
        let w2 = vec![RingElem::constant(1), RingElem::constant(0)];
        assert_eq!(
            commit_ring_witness(&sis_params, &w1).unwrap(),
            commit_ring_witness(&sis_params, &w2).unwrap()
        );

        let dual_break = extract_dual_forgery_with(
            toy_hash,
            2,
            0,
            &col_a,
            &[sib],
            &col_b,
            &[sib],
            &sis_params,
            &w1,
            &w2,
            5,
        )
        .expect("must extract concrete HashBreak x SisBreak");

        // Verify extracted HashBreak is genuine concrete collision data
        assert_ne!(dual_break.hash_break.preimage_a, dual_break.hash_break.preimage_b);
        assert_eq!(
            toy_hash(&dual_break.hash_break.preimage_a),
            dual_break.hash_break.shared_digest
        );
        assert_eq!(
            toy_hash(&dual_break.hash_break.preimage_b),
            dual_break.hash_break.shared_digest
        );

        // Verify extracted SisBreak is genuine fixed-length non-zero short kernel vector
        assert_eq!(dual_break.sis_break.delta.len(), sis_params.cols);
        assert!(!dual_break.sis_break.delta.iter().all(RingElem::is_zero));
        assert!(dual_break.sis_break.norm_inf <= dual_break.sis_break.declared_bound);
        let ker = commit_ring_witness(&sis_params, &dual_break.sis_break.delta).unwrap();
        assert!(ker.syndrome.iter().all(RingElem::is_zero));
    }

    /// **Red-Team `F3`**: Zero-grinding constant-table sumcheck forgery (`claude_2` F3 attack)
    /// defeated by mandatory `bind_instance(comm, claimed_sum, point)` prior to challenge 0.
    #[test]
    fn test_f3_forgery_zero_grinding_constant_table_sumcheck_swap_rejected() {
        let canopy_params = CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            16,
        )
        .unwrap();
        let lattice_params = LatticeParams::expand_from_seed([0x22u8; 32], 2, 4).unwrap();
        let num_vars = 4usize; // 16 elements
        let honest_table: Vec<Goldilocks> = (0..16u64).map(Goldilocks::from_u64_reduced).collect();

        let honest_receipt = prove_dual_pcs_receipt(
            "OBEND.F3.TEST/v1",
            [0xABu8; 32],
            b"f3-circuit",
            &canopy_params,
            &lattice_params,
            num_vars,
            &honest_table,
        )
        .unwrap();
        verify_dual_pcs_receipt(&canopy_params, &lattice_params, &honest_receipt).unwrap();

        // Forgery attempt A: mutate claimed_hypercube_sum and adjust round 0 polynomial so p0(0)+p0(1)=S_false
        let mut forged_a = honest_receipt.clone();
        let delta = GoldilocksExt2::from_base(Goldilocks::from_u64_reduced(100));
        forged_a.claimed_hypercube_sum += delta;
        // Adjust c0 by delta/2? Even simpler: c1 += delta so p0(0) + p0(1) = 2*c0 + c1 + delta = S_true + delta!
        forged_a.sumcheck_rounds[0].coeffs[1] += delta;
        assert!(
            verify_dual_pcs_receipt(&canopy_params, &lattice_params, &forged_a).is_err(),
            "F3 forgery A must fail because instance binding shifts all Fiat-Shamir challenges!"
        );

        // Forgery attempt B: constant-table post-hoc swap (`f ≡ e` after observing challenges)
        let mut forged_b = honest_receipt.clone();
        let const_table = vec![Goldilocks::from_u64_reduced(7); 16];
        let const_canopy = canopy_commit(&canopy_params, num_vars, &const_table, None).unwrap();
        let const_ring = pack_goldilocks_to_ring_witness(&const_table, lattice_params.cols).unwrap();
        let const_lat = commit_ring_witness(&lattice_params, &const_ring).unwrap();
        forged_b.canopy_commitment = const_canopy.commitment;
        forged_b.lattice_commitment = const_lat;
        assert!(
            verify_dual_pcs_receipt(&canopy_params, &lattice_params, &forged_b).is_err(),
            "F3 post-hoc constant-table commitment swap must be rejected!"
        );
    }

    /// **Red-Team `F4`**: `0` vs `p` Goldilocks representation alias & 64-bit challenge downgrade.
    #[test]
    fn test_f4_forgery_goldilocks_p_alias_and_64bit_challenge_downgrade_blocked() {
        fn assert_128bit_sound_challenge<F: SoundChallengeField>() -> u32 {
            F::CHALLENGE_SECURITY_BITS
        }
        assert!(assert_128bit_sound_challenge::<GoldilocksExt2>() >= 127);

        // `0` vs `GOLDILOCKS_PRIME` (`2^64 - 2^32 + 1`): CanonicalLift strictly rejects `p`..=`u64::MAX`
        assert!(CanonicalLift::try_new(0).is_ok());
        assert!(CanonicalLift::try_new(GOLDILOCKS_PRIME).is_err());
        assert!(CanonicalLift::try_new(u64::MAX).is_err());

        // Attempting to smuggle limbs reconstructing `GOLDILOCKS_PRIME` (l0=1, l1=0, l2=0xFFFF, l3=0xFFFF)
        // through the 16-bit Lattice-to-Goldilocks bridge MUST fail!
        let mut bad_ring = RingElem::zero();
        let mut raw = *bad_ring.coeffs();
        raw[0] = 1;
        raw[1] = 0;
        raw[2] = 0xFFFF;
        raw[3] = 0xFFFF;
        bad_ring = RingElem::from_coeffs(raw);
        assert!(matches!(
            unpack_ring_witness_to_goldilocks(&[bad_ring], 1),
            Err(LatticeError::NonCanonicalGoldilocks(_))
        ));

        // Attempting `max_bits = 64` in Dark Bazaar `commit_private_order` is rejected (`<= 63` enforced!)
        let cp = CanopyParams::default_128bit();
        let lp = LatticeParams::expand_from_seed([0x31u8; 32], 2, 4).unwrap();
        let wit = PrivateOrderWitness {
            qty_bits: to_bits_le(0, 64),
            total_bits: to_bits_le(0, 8),
            salt: OrderSalt::from_entropy([0x01u8; 32]),
        };
        assert_eq!(
            commit_private_order(&cp, &lp, 1, OrderSide::Bid, 64, &wit),
            Err(LatticeError::MaxBitsExceedsCanonical63(64))
        );
    }

    /// **Red-Team `F5`**: Omitted evaluation point in PCS transcript & binary-additive non-UDR guard.
    #[test]
    fn test_f5_forgery_omitted_eval_point_and_binary_non_udr_proximity_rejected() {
        // Binary additive outside UDR is rejected (`2026/2424`)
        assert!(CanopyParams::new(
            DomainKind::BinaryAdditive,
            ProximityRegime::JohnsonBound,
            4,
            32
        )
        .is_err());

        // Mutating evaluation point after opening is deterministically rejected by `canopy_verify`
        let params = CanopyParams::default_128bit();
        let v = 8usize;
        let tbl: Vec<Goldilocks> = (0..(1usize << v))
            .map(|i| Goldilocks::from_u64_reduced(i as u64 * 31 + 9))
            .collect();
        let pt: Vec<GoldilocksExt2> = (0..v)
            .map(|i| GoldilocksExt2::from_canonical_u64_pair(3 + i as u64, 5 + i as u64).unwrap())
            .collect();
        let val = mle_eval_base_at_ext2(&tbl, &pt).unwrap();
        let st = canopy_commit(&params, v, &tbl, None).unwrap();

        let mut p_tr = FenziTranscript::new(b"f5")
            .bind_relation("CANOPY.F5", &[0x55u8; 32], b"v=8")
            .bind_instance(&st.commitment.to_transcript_bytes(), val, &pt);
        let prf = canopy_open(&params, &st, &pt, &mut p_tr).unwrap();

        let mut wrong_pt = pt.clone();
        wrong_pt[0] += GoldilocksExt2::ONE;
        let wrong_val = mle_eval_base_at_ext2(&tbl, &wrong_pt).unwrap();
        let mut v_tr = FenziTranscript::new(b"f5")
            .bind_relation("CANOPY.F5", &[0x55u8; 32], b"v=8")
            .bind_instance(&st.commitment.to_transcript_bytes(), wrong_val, &wrong_pt);
        assert!(
            canopy_verify(&params, &st.commitment, &wrong_pt, wrong_val, &prf, &mut v_tr).is_err(),
            "proof bound to `pt` cannot verify at `wrong_pt`"
        );
    }

    /// **Red-Team `F6`**: Unsalted Dark Bazaar `2^16` dictionary & linear MITM attacks defeated
    /// by dual-track salted `commit_private_order` + end-to-end `SameOpening` verification (`K7`).
    #[test]
    fn test_f6_forgery_unsalted_dark_bazaar_order_dictionary_and_mitm_defeated() {
        let cp = CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            8,
        )
        .unwrap();
        let lp = LatticeParams::expand_from_seed([0x66u8; 32], 2, 4).unwrap();

        let wit_salt1 = PrivateOrderWitness {
            qty_bits: to_bits_le(10, 16),
            total_bits: to_bits_le(500, 16),
            salt: OrderSalt::from_entropy([0xA1u8; 32]),
        };
        let wit_salt2 = PrivateOrderWitness {
            qty_bits: to_bits_le(10, 16),
            total_bits: to_bits_le(500, 16),
            salt: OrderSalt::from_entropy([0xB2u8; 32]),
        };

        let ord1 = commit_private_order(&cp, &lp, 7, OrderSide::Bid, 16, &wit_salt1).unwrap();
        let ord1_re = commit_private_order(&cp, &lp, 7, OrderSide::Bid, 16, &wit_salt2).unwrap();

        // Identical `(account, side, qty, total)` under distinct salts produce completely distinct
        // commitments on BOTH Track H (Canopy Merkle) and Track L (PikkuFold Syndrome)!
        assert!(ord1.canopy_comm.salted);
        assert_ne!(ord1.canopy_comm.root, ord1_re.canopy_comm.root);
        assert_ne!(ord1.lattice_comm.syndrome, ord1_re.lattice_comm.syndrome);

        // End-to-end 2-order Dark Bazaar clearing batch:
        // Buyer (account 7): Bid qty=10, total=500 (limit price 50)
        // Seller (account 8): Ask qty=10, total=450 (limit price 45)
        // Uniform clearing price = 48: both cross, fill = [10, 10], slacks = [1, 1] => gap = 0!
        let ask_wit = PrivateOrderWitness {
            qty_bits: to_bits_le(10, 16),
            total_bits: to_bits_le(450, 16),
            salt: OrderSalt::from_entropy([0xC3u8; 32]),
        };
        let ord2 = commit_private_order(&cp, &lp, 8, OrderSide::Ask, 16, &ask_wit).unwrap();

        let market = DarkBazaarMarket {
            currency_asset: 1,
            goods_asset: 2,
        };
        let smudge = SmudgeBudgetConfig {
            noise_bound: 8,
            smudge_bound: 8u128 * 64 * 4 * (1u128 << 40),
            sec_bits: 40,
            num_releases: 4,
        };
        let vk = [0xD4u8; 32];
        let committed_orders = vec![ord1, ord2];
        let witnesses = vec![wit_salt1, ask_wit];

        let bazaar_prf = prove_dark_bazaar_same_opening(
            &vk,
            &cp,
            &lp,
            &market,
            &smudge,
            &committed_orders,
            &witnesses,
            48,
            vec![10, 10],
            vec![1, 1],
        )
        .unwrap();

        verify_dark_bazaar_same_opening(
            &vk,
            &cp,
            &lp,
            &market,
            &smudge,
            &committed_orders,
            &bazaar_prf,
        )
        .unwrap();

        // Tamper 1: corrupted salted Canopy binding limbs in opening -> rejected!
        let mut bad_salt_prf = bazaar_prf.clone();
        bad_salt_prf.order_openings[0].canopy_bind_limbs[0] = Goldilocks::from_u64_reduced(
            bad_salt_prf.order_openings[0].canopy_bind_limbs[0].to_canonical_u64() ^ 1,
        );
        assert!(verify_dark_bazaar_same_opening(
            &vk,
            &cp,
            &lp,
            &market,
            &smudge,
            &committed_orders,
            &bad_salt_prf
        )
        .is_err());

        // Tamper 2: non-zero primal-dual KKT gap (`fills = [5, 5]` or `[0, 0]`) -> rejected!
        assert!(matches!(
            prove_dark_bazaar_same_opening(
                &vk,
                &cp,
                &lp,
                &market,
                &smudge,
                &committed_orders,
                &witnesses,
                48,
                vec![5, 5],
                vec![1, 1],
            ),
            Err(LatticeError::NonZeroPrimalDualKktGap { .. })
        ));
        let mut subopt_prf = bazaar_prf;
        subopt_prf.order_fills = vec![5, 5];
        assert!(verify_dark_bazaar_same_opening(
            &vk,
            &cp,
            &lp,
            &market,
            &smudge,
            &committed_orders,
            &subopt_prf
        )
        .is_err());
    }

    /// **Red-Team `F7`**: `Choe–Kang–Stehlé (2026/2546)` unsmudged decryption, `< 40`-bit drowning,
    /// multi-release budget exhaustion, and decryption-margin wraparound all refused!
    #[test]
    fn test_f7_forgery_unsmudged_and_multiquery_ind_cpa_d_leakage_rejected() {
        // 1. Unsmudged (`smudge_bound = 0`)
        assert_eq!(
            (SmudgeBudgetConfig {
                noise_bound: 1,
                smudge_bound: 0,
                sec_bits: 40,
                num_releases: 1,
            })
            .validate(),
            Err(LatticeError::UnsmudgedOrInsufficientNoiseBudget)
        );
        // 2. Insufficient security bits (`39 < 40`)
        assert_eq!(
            (SmudgeBudgetConfig {
                noise_bound: 1,
                smudge_bound: 1u128 << 60,
                sec_bits: 39,
                num_releases: 1,
            })
            .validate(),
            Err(LatticeError::UnsmudgedOrInsufficientNoiseBudget)
        );
        // 3. Multi-query exhaustion: budget sized for 1 scalar fails when `num_releases = 10` over `d = 64`!
        assert_eq!(
            (SmudgeBudgetConfig {
                noise_bound: 4,
                smudge_bound: 4u128 * (1u128 << 40), // missing RING_DEGREE * num_releases factor!
                sec_bits: 40,
                num_releases: 10,
            })
            .validate(),
            Err(LatticeError::UnsmudgedOrInsufficientNoiseBudget)
        );
        // 4. Excessive smudge wrapping collective decryption correctness margin
        assert_eq!(
            (SmudgeBudgetConfig {
                noise_bound: 4,
                smudge_bound: 1u128 << 105,
                sec_bits: 40,
                num_releases: 1,
            })
            .validate(),
            Err(LatticeError::DecryptionMarginWrapped)
        );
    }

    /// **Red-Team `F8`**: `DetCbor` unread/smuggled fields & `Lsafe` backslash/CRLF delimiter smuggling.
    #[test]
    fn test_f8_forgery_cbor_canonicality_and_backslash_delimiter_smuggling_rejected() {
        // Part 1: Redaction confinement rejects byte 92 (`\`) quote-escape smuggling & CRLF injection!
        let ok_json = br#"{"user":"alice_token_123","role":"member"}"#;
        // Span covering `alice_token_123` (offset 9, len 15) passes cleanly
        assert!(check_redaction_span_confinement(ok_json, 9, 15).is_ok());

        // F8 Attack 1: redacted value ends with `\` (`92`) escaping the closing public `"`!
        let backslash_attack = br#"{"user":"alice\","role":"admin"}"#;
        assert!(check_redaction_span_confinement(backslash_attack, 9, 6).is_err());

        // F8 Attack 2: `\r\n` HTTP header injection inside redacted span
        let crlf_attack = b"X-Auth: secret\r\nX-Admin: true\r\n";
        assert!(check_redaction_span_confinement(crlf_attack, 8, 21).is_err());

        // F8 Attack 3: `,` / `:` / `[` / `]` JSON structural injection inside unquoted slot
        let comma_attack = br#"{"amount":100,"admin":true}"#;
        assert!(check_redaction_span_confinement(comma_attack, 10, 16).is_err());

        // Part 2: `DualPcsReceipt` `DetCbor` rejects smuggled extra fields & non-canonical scalars!
        let cp = CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::UniqueDecodingRadius,
            4,
            8,
        )
        .unwrap();
        let lp = LatticeParams::expand_from_seed([0x88u8; 32], 2, 4).unwrap();
        let tbl: Vec<Goldilocks> = (0..16u64).map(Goldilocks::from_u64_reduced).collect();
        let receipt = prove_dual_pcs_receipt(
            "OBEND.F8.RECEIPT/v1",
            [0x81u8; 32],
            b"f8",
            &cp,
            &lp,
            4,
            &tbl,
        )
        .unwrap();

        // Inject an unread shadow field `"zzz_smuggled"` into the CBOR map -> rejected!
        let mut cbor_ast = receipt.to_cbor_value();
        if let CborValue::Map(ref mut entries) = cbor_ast {
            entries.push((
                CborValue::Text(String::from("zzz_smuggled")),
                CborValue::Unsigned(999),
            ));
        }
        let smuggled_bytes = encode_det_cbor(&cbor_ast).unwrap();
        assert!(matches!(
            DualPcsReceipt::from_det_cbor_bytes(&smuggled_bytes),
            Err(DetCborError::UnexpectedFieldCount {
                expected: 14,
                actual: 15
            })
        ));

        // Inject non-canonical Goldilocks `GOLDILOCKS_PRIME` into `claimed_hypercube_sum` -> rejected!
        let mut bad_gl_ast = receipt.to_cbor_value();
        if let CborValue::Map(ref mut entries) = bad_gl_ast {
            for (k, v) in entries.iter_mut() {
                if k == &CborValue::Text(String::from("claimed_hypercube_sum")) {
                    *v = CborValue::Array(vec![
                        CborValue::Unsigned(GOLDILOCKS_PRIME),
                        CborValue::Unsigned(0),
                    ]);
                }
            }
        }
        let bad_gl_bytes = encode_det_cbor(&bad_gl_ast).unwrap();
        assert!(matches!(
            DualPcsReceipt::from_det_cbor_bytes(&bad_gl_bytes),
            Err(DetCborError::NonCanonicalGoldilocks(_))
        ));

        // Inject out-of-range lattice coefficient `HALF_Q_LAT + 1` -> rejected!
        let mut bad_lat_ast = receipt.to_cbor_value();
        if let CborValue::Map(ref mut entries) = bad_lat_ast {
            for (k, v) in entries.iter_mut() {
                if k == &CborValue::Text(String::from("lattice_proof"))
                    && let CborValue::Map(lp_entries) = v
                {
                    for (lk, lv) in lp_entries.iter_mut() {
                        if lk == &CborValue::Text(String::from("final_witness"))
                            && let CborValue::Array(coeffs) = lv
                        {
                            coeffs[0] = CborValue::from_i64(HALF_Q_LAT + 1);
                        }
                    }
                }
            }
        }
        let bad_lat_bytes = encode_det_cbor(&bad_lat_ast).unwrap();
        let _ = decode_det_cbor(&bad_lat_bytes).unwrap();
        assert!(matches!(
            DualPcsReceipt::from_det_cbor_bytes(&bad_lat_bytes),
            Err(DetCborError::NonCanonicalLatticeCoeff(_))
        ));
    }

    /// **Red-Team `F10` & `F11`**: Explicit per-round norm budget overflow refusal in 2-to-1 folding.
    #[test]
    fn test_f11_forgery_norm_budget_overflow_and_long_witness_rejected() {
        let lp = LatticeParams::expand_from_seed([0x99u8; 32], 2, 4).unwrap();
        let mut overlong = vec![RingElem::zero(); 4];
        overlong[0] = RingElem::constant(100_000);
        let comm = commit_ring_witness(&lp, &overlong).unwrap();

        // Witness exceeding declared bound 65535 is rejected immediately
        assert!(matches!(
            fold_witness_2_to_1(
                &lp,
                &overlong,
                &comm,
                &overlong,
                &comm,
                &RingElem::one(),
                GADGET_LIMB_MAX
            ),
            Err(LatticeError::WitnessNormExceeded {
                actual: 100_000,
                bound: 65535
            })
        ));

        // Folding whose output norm budget would exceed MAX_SAFE_SIS_NORM (< Q_LAT / 4) is rejected!
        let near_ceil = RingElem::constant((MAX_SAFE_SIS_NORM / 2 + 10) as i64);
        let w_near = vec![near_ceil; 4];
        let c_near = commit_ring_witness(&lp, &w_near).unwrap();
        assert!(matches!(
            fold_witness_2_to_1(
                &lp,
                &w_near,
                &c_near,
                &w_near,
                &c_near,
                &RingElem::one(),
                MAX_SAFE_SIS_NORM / 2 + 10
            ),
            Err(LatticeError::NormBudgetOverflow { .. })
        ));
    }

    /// Micro-benchmarks & telemetry assertions (run with `cargo test --release -- --nocapture`).
    #[test]
    fn bench_and_metrics_dual_track_crypto_exec() {
        // 1. Radix-2 Goldilocks NTT + iNTT on N = 2^14 = 16,384
        let n_ntt = 1usize << 14;
        let mut ntt_buf: Vec<Goldilocks> = (0..n_ntt as u64)
            .map(|i| Goldilocks::from_u64_reduced(i.wrapping_mul(0x9E37_79B9_7F4A_7C15) + 1))
            .collect();
        let t0 = Instant::now();
        let ntt_iters = 20u32;
        for _ in 0..ntt_iters {
            ntt_in_place(&mut ntt_buf).unwrap();
            intt_in_place(&mut ntt_buf).unwrap();
        }
        let ntt_elapsed = t0.elapsed();

        // 2. Linear-time Ext2 Sumcheck on v = 14 (16,384 hypercube points)
        let v_sc = 14usize;
        let sc_tbl: Vec<Goldilocks> = (0..(1usize << v_sc))
            .map(|i| Goldilocks::from_u64_reduced((i as u64) * 37 + 11))
            .collect();
        let mut sum_gl = Goldilocks::ZERO;
        for &x in &sc_tbl {
            sum_gl += x;
        }
        let sc_sum = GoldilocksExt2::from_base(sum_gl);
        let sc_base_tr = FenziTranscript::new(b"bench-sc")
            .bind_relation("OBEND.BENCH.SC/v1", &[0x12u8; 32], b"v=14")
            .bind_instance(b"bench-comm", sc_sum, &[]);
        let t_sc = Instant::now();
        let mut p_sc_tr = sc_base_tr.clone();
        let (sc_rounds, _) = prove_multilinear_sumcheck_ext2(&sc_tbl, &mut p_sc_tr).unwrap();
        let sc_prove_us = t_sc.elapsed().as_micros();
        let t_sc_v = Instant::now();
        let mut v_sc_tr = sc_base_tr;
        verify_sumcheck_ext2(1, v_sc, sc_sum, &sc_rounds, &mut v_sc_tr).unwrap();
        let sc_verify_us = t_sc_v.elapsed().as_micros();

        // 3. Canopy (`2026/2790`) Track H Hash-Savings & Timing on v = 12 (4096 evals, L = 256 cols, Q = 32)
        //    and v = 14 (16,384 evals, L = 512 cols, Q = 48)
        for &(v_can, queries) in &[(12usize, 32usize), (14usize, 48usize)] {
            let c_params = CanopyParams::new(
                DomainKind::PrimeField,
                ProximityRegime::UniqueDecodingRadius,
                4,
                queries,
            )
            .unwrap();
            let c_tbl = &sc_tbl[..(1usize << v_can)];
            let pt: Vec<GoldilocksExt2> = (0..v_can)
                .map(|i| {
                    GoldilocksExt2::from_canonical_u64_pair(19 + i as u64, 73 + 3 * i as u64)
                        .unwrap()
                })
                .collect();
            let val = mle_eval_base_at_ext2(c_tbl, &pt).unwrap();

            let t_com = Instant::now();
            let st = canopy_commit(&c_params, v_can, c_tbl, None).unwrap();
            let commit_ms = t_com.elapsed().as_secs_f64() * 1000.0;

            let base_tr = FenziTranscript::new(b"bench-canopy")
                .bind_relation("OBEND.BENCH.CANOPY/v1", &[0x34u8; 32], b"canopy")
                .bind_instance(&st.commitment.to_transcript_bytes(), val, &pt);

            let mut p_tr = base_tr.clone();
            let t_open = Instant::now();
            let prf = canopy_open(&c_params, &st, &pt, &mut p_tr).unwrap();
            let open_us = t_open.elapsed().as_micros();

            let mut v_tr = base_tr.clone();
            let t_ver = Instant::now();
            let canopy_stats =
                canopy_verify(&c_params, &st.commitment, &pt, val, &prf, &mut v_tr).unwrap();
            let verify_us = t_ver.elapsed().as_micros();

            let mut ip_tr = base_tr.clone();
            let iprf =
                prove_independent_merkle_baseline(&c_params, &st, &pt, &mut ip_tr).unwrap();
            let mut iv_tr = base_tr;
            let ind_stats = verify_independent_merkle_baseline(
                &c_params,
                &st.commitment,
                &pt,
                val,
                &iprf,
                &mut iv_tr,
            )
            .unwrap();

            let savings_pct = canopy_stats.savings_vs(&ind_stats) * 100.0;
            assert!(
                savings_pct >= 30.0,
                "Canopy v={v_can} Q={queries} must save >= 30% hashes, got {savings_pct:.2}%"
            );
            println!(
                "[METRICS][Canopy v={v_can} Q={queries}] commit={commit_ms:.2}ms open={open_us}us verify={verify_us}us | hashes: canopy={} (leaf={}, internal={}) vs independent={} => SAVINGS={savings_pct:.2}% | aux_siblings={} vs ind_siblings={}",
                canopy_stats.total_hashes,
                canopy_stats.leaf_hashes,
                canopy_stats.internal_hashes,
                ind_stats.total_hashes,
                prf.aux_siblings.len(),
                iprf.independent_paths.len() * iprf.independent_paths[0].len()
            );
        }

        // 4. PikkuFold 0-mul Kronecker fold (n = 256 RingElems = 16,384 Z_{q_lat} coeffs) + Akita (cols = 16)
        let kron_pairs = [
            [TernaryTrit::PosOne, TernaryTrit::NegOne],
            [TernaryTrit::PosOne, TernaryTrit::PosOne],
            [TernaryTrit::NegOne, TernaryTrit::PosOne],
            [TernaryTrit::PosOne, TernaryTrit::Zero],
            [TernaryTrit::PosOne, TernaryTrit::NegOne],
            [TernaryTrit::Zero, TernaryTrit::PosOne],
            [TernaryTrit::PosOne, TernaryTrit::PosOne],
            [TernaryTrit::NegOne, TernaryTrit::PosOne],
        ]; // 2^8 = 256
        let ring_vec: Vec<RingElem> = (0..256i64)
            .map(|i| {
                let mut coeffs = [0i64; 64];
                for (k, slot) in coeffs.iter_mut().enumerate() {
                    *slot = (i * 13 + (k as i64) * 7) % 1024 - 512;
                }
                RingElem::from_coeffs(coeffs)
            })
            .collect();
        let t_kron = Instant::now();
        let folded_kron = kronecker_ternary_fold_0mul(&ring_vec, &kron_pairs).unwrap();
        let kron_us = t_kron.elapsed().as_micros();
        assert!(!folded_kron.is_zero());

        // 5. End-to-end DualPcsReceipt + DetCbor on v = 10 (1024 Goldilocks = 4096 limbs = 64 RingElems)
        let v_dual = 10usize;
        let dual_cp = CanopyParams::default_128bit();
        let dual_lp = LatticeParams::expand_from_seed([0x7Au8; 32], 2, 64).unwrap();
        let dual_tbl = &sc_tbl[..(1usize << v_dual)];

        let t_dp = Instant::now();
        let receipt = prove_dual_pcs_receipt(
            "OBEND.BENCH.DUAL_PCS/v1",
            [0xFEu8; 32],
            b"dual-v10",
            &dual_cp,
            &dual_lp,
            v_dual,
            dual_tbl,
        )
        .unwrap();
        let dual_prove_ms = t_dp.elapsed().as_secs_f64() * 1000.0;

        let t_enc = Instant::now();
        let cbor_bytes = receipt.to_det_cbor_bytes().unwrap();
        let cbor_enc_us = t_enc.elapsed().as_micros();

        let t_dec = Instant::now();
        let decoded = DualPcsReceipt::from_det_cbor_bytes(&cbor_bytes).unwrap();
        let cbor_dec_us = t_dec.elapsed().as_micros();
        assert_eq!(decoded, receipt);

        let t_dv = Instant::now();
        let dual_hstats = verify_dual_pcs_receipt(&dual_cp, &dual_lp, &decoded).unwrap();
        let dual_ver_ms = t_dv.elapsed().as_secs_f64() * 1000.0;

        let _ = CanopyCommitment {
            num_vars: 0,
            salted: false,
            root: [0u8; 32],
        };

        println!(
            "[METRICS][Goldilocks NTT+iNTT N={n_ntt}] {ntt_iters} roundtrips in {:.2}ms ({:.1}us / NTT+iNTT pair)",
            ntt_elapsed.as_secs_f64() * 1000.0,
            ntt_elapsed.as_secs_f64() * 1_000_000.0 / (ntt_iters as f64)
        );
        println!(
            "[METRICS][Sumcheck Ext2 v={v_sc} (N=16384)] prove={sc_prove_us}us verify={sc_verify_us}us"
        );
        println!(
            "[METRICS][PikkuFold 0-mul Kronecker Fold 256xRing64] {kron_us}us"
        );
        println!(
            "[METRICS][DualPcsReceipt v={v_dual} (Canopy + Akita R_q64)] prove={dual_prove_ms:.2}ms verify={dual_ver_ms:.2}ms | DetCbor size={}B enc={cbor_enc_us}us dec={cbor_dec_us}us | canopy_hashes={}",
            cbor_bytes.len(),
            dual_hstats.total_hashes
        );
    }
}
