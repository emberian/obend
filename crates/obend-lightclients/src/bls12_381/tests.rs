//! BLS12-381 conformance and adversarial tests.
//!
//! Vector sources (converted by the swarm scratch script `convert.py` into compact data files):
//! * RFC 9380 App. J.10.1 and App. E.3 — <https://www.rfc-editor.org/rfc/rfc9380.txt>
//! * ethereum/bls12-381-tests v0.1.2 `bls_tests_json.tar.gz` —
//!   <https://github.com/ethereum/bls12-381-tests/releases/download/v0.1.2/bls_tests_json.tar.gz>
//!   (sha256 `0dc1dfabfa7b3e0f8e8029f9cb2bb8733597526fa085b18f160d2c4eb0b448bc`)

use super::*;
use crate::bigint::limbs_to_be;

const ETH: &str = include_str!("../../tests/vectors/bls/eth_bls12_381_tests_v0.1.2.txt");
const J10: &str = include_str!("../../tests/vectors/bls/rfc9380_j10_1.txt");
const E3: &str = include_str!("../../tests/vectors/bls/rfc9380_e3_iso3.txt");
const RFC_DST: &[u8] = b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    assert!(s.len().is_multiple_of(2), "odd hex length");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn list(s: &str) -> Vec<Vec<u8>> {
    if s == "-" {
        Vec::new()
    } else {
        s.split(',').map(unhex).collect()
    }
}

fn arr<const N: usize>(v: &[u8]) -> Option<[u8; N]> {
    v.try_into().ok()
}

fn data_rows(src: &'static str) -> impl Iterator<Item = Vec<&'static str>> {
    src.lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| l.split(' ').collect())
}

fn eth_rows(kind: &str) -> Vec<Vec<&'static str>> {
    data_rows(ETH).filter(|f| f[0] == kind).collect()
}

fn flag(s: &str) -> bool {
    match s {
        "1" => true,
        "0" => false,
        _ => panic!("bad expected flag {s}"),
    }
}

fn seeded_fp(i: u64) -> Fp {
    Fp::from_be_reduce(&crate::sha256(&i.to_be_bytes()))
}
fn seeded_fp2(i: u64) -> Fp2 {
    Fp2::new(seeded_fp(2 * i), seeded_fp(2 * i + 1))
}
fn seeded_fp6(i: u64) -> Fp6 {
    Fp6 {
        c0: seeded_fp2(3 * i),
        c1: seeded_fp2(3 * i + 1),
        c2: seeded_fp2(3 * i + 2),
    }
}
fn seeded_fp12(i: u64) -> Fp12 {
    Fp12 {
        c0: seeded_fp6(2 * i + 100),
        c1: seeded_fp6(2 * i + 101),
    }
}

// --- little-endian Vec<u64> big integers (test-only exponent bookkeeping) ---

fn trim(mut v: Vec<u64>) -> Vec<u64> {
    while v.last() == Some(&0) {
        v.pop();
    }
    v
}

fn big_mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut o = vec![0u64; a.len() + b.len() + 1];
    for (i, &ai) in a.iter().enumerate() {
        let mut c = 0u128;
        for (j, &bj) in b.iter().enumerate() {
            let t = u128::from(o[i + j]) + u128::from(ai) * u128::from(bj) + c;
            o[i + j] = t as u64;
            c = t >> 64;
        }
        let mut k = i + b.len();
        while c != 0 {
            let t = u128::from(o[k]) + c;
            o[k] = t as u64;
            c = t >> 64;
            k += 1;
        }
    }
    trim(o)
}

fn big_add_small(a: &[u64], s: u64) -> Vec<u64> {
    let mut o = a.to_vec();
    o.push(0);
    let mut c = u128::from(s);
    for x in o.iter_mut() {
        let t = u128::from(*x) + c;
        *x = t as u64;
        c = t >> 64;
    }
    trim(o)
}

fn big_sub_small(a: &[u64], s: u64) -> Vec<u64> {
    let mut o = a.to_vec();
    let mut borrow = s;
    for x in o.iter_mut() {
        let (d, b) = x.overflowing_sub(borrow);
        *x = d;
        borrow = u64::from(b);
        if borrow == 0 {
            break;
        }
    }
    assert_eq!(borrow, 0);
    trim(o)
}

fn big_pow(a: &[u64], e: u32) -> Vec<u64> {
    (0..e).fold(vec![1u64], |acc, _| big_mul(&acc, a))
}

#[test]
fn final_exponent_embedding_is_exact() {
    let p = ctx().fp.modulus().to_vec();
    let r = ctx().r.to_vec();
    let e = trim(ctx().e_hard.to_vec());
    let p6 = big_pow(&p, 6);
    let p12m1 = big_sub_small(&big_pow(&p, 12), 1);
    // (p^6 + 1) / r is exact, and the full exponent (p^6 - 1) * E_HARD satisfies * r == p^12 - 1.
    assert_eq!(big_mul(&e, &r), big_add_small(&p6, 1));
    assert_eq!(big_mul(&big_mul(&big_sub_small(&p6, 1), &e), &r), p12m1);
    // Frobenius sanity for the tower: f^(p^6) == conj(f).
    let mut p6l = [0u64; 36];
    p6l[..p6.len()].copy_from_slice(&p6);
    let f = seeded_fp12(7);
    assert_eq!(f.pow(&p6l), f.conj());
    // h_eff is the RFC 9380 §8.8.2 constant, and (p+1)/4, (p-1)/2 are what they claim.
    assert_eq!(limbs_bits(&ctx().h_eff), 636);
    assert_eq!(
        big_mul(&trim(ctx().p_plus1_div4.to_vec()), &[4]),
        big_add_small(&p, 1)
    );
    assert_eq!(
        big_add_small(&big_mul(&trim(ctx().p_minus1_div2.to_vec()), &[2]), 1),
        p
    );
}

#[test]
fn tower_field_laws() {
    for i in 0..4 {
        let a = seeded_fp(i);
        assert_eq!(a.mul(&a.inv()), Fp::one());
        let a2 = seeded_fp2(i);
        assert_eq!(a2.mul(&a2.inv()), Fp2::one());
        assert_eq!(a2.sqr(), a2.mul(&a2));
        let s = a2.sqr();
        assert_eq!(s.sqrt().expect("a square has a root").sqr(), s);
        assert!(s.mul_xi().sqrt().is_none(), "xi * square is a non-square");
        let a6 = seeded_fp6(i);
        assert_eq!(a6.mul(&a6.inv()), Fp6::one());
        let a12 = seeded_fp12(i);
        assert_eq!(a12.mul(&a12.inv()), Fp12::one());
        let b12 = seeded_fp12(i + 10);
        assert_eq!(a12.mul(&b12), b12.mul(&a12));
    }
    let u = Fp2::new(Fp::zero(), Fp::one());
    assert_eq!(u.sqr(), Fp2::one().neg());
    let v = Fp6 {
        c0: Fp2::zero(),
        c1: Fp2::one(),
        c2: Fp2::zero(),
    };
    assert_eq!(
        v.mul(&v).mul(&v),
        Fp6 {
            c0: Fp2::one().mul_xi(),
            c1: Fp2::zero(),
            c2: Fp2::zero()
        }
    );
    let w = Fp12 {
        c0: Fp6::zero(),
        c1: Fp6::one(),
    };
    assert_eq!(
        w.sqr(),
        Fp12 {
            c0: v,
            c1: Fp6::zero()
        }
    );
    assert!(Fp2::one().mul_xi().sqrt().is_none());
}

#[test]
fn generators_and_encodings() {
    let g1 = G1Affine::generator();
    assert!(g1.0.on_curve() && in_subgroup(&g1.0));
    assert_eq!(
        hex(&g1.to_compressed()),
        "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
    );
    assert_eq!(g1_from_compressed(&g1.to_compressed()).unwrap(), g1);
    let ng1 = G1Affine(g1.0.neg());
    assert_eq!(ng1.to_compressed()[0] ^ g1.to_compressed()[0], FLAG_SIGN);
    assert_eq!(g1_from_compressed(&ng1.to_compressed()).unwrap(), ng1);

    let g2 = G2Affine::generator();
    assert!(g2.0.on_curve() && in_subgroup(&g2.0));
    assert_eq!(
        hex(&g2.to_compressed()),
        "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e\
         024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"
    );
    assert_eq!(g2_from_compressed(&g2.to_compressed()).unwrap(), g2);
    let ng2 = G2Affine(g2.0.neg());
    assert_eq!(ng2.to_compressed()[0] ^ g2.to_compressed()[0], FLAG_SIGN);
    assert_eq!(g2_from_compressed(&ng2.to_compressed()).unwrap(), ng2);

    let i1 = G1Affine(Aff::identity()).to_compressed();
    assert_eq!(i1[0], 0xc0);
    assert!(g1_from_compressed(&i1).unwrap().is_identity());
    let i2 = G2Affine(Aff::identity()).to_compressed();
    assert_eq!(i2[0], 0xc0);
    assert!(g2_from_compressed(&i2).unwrap().is_identity());

    // Group law consistency: [3]G == G + G + G, [r-1]G == -G.
    let j = g1.0.to_jac();
    assert_eq!(
        j.mul_limbs(&[3u64]).to_affine(),
        j.add(&j).add(&j).to_affine()
    );
    let rm1 = crate::bigint::limbs_sub(&ctx().r, &[1, 0, 0, 0]).0;
    assert_eq!(j.mul_limbs(&rm1).to_affine(), g1.0.neg());
    let j2 = g2.0.to_jac();
    assert_eq!(j2.mul_limbs(&rm1).to_affine(), g2.0.neg());
}

#[test]
fn strict_encoding_rejections() {
    let p_bytes = limbs_to_be(ctx().fp.modulus(), 48).unwrap();
    let g = G1Affine::generator().to_compressed();
    let mut b = g;
    b[0] &= !FLAG_C;
    assert_eq!(g1_from_compressed(&b), Err(BlsError::NotCompressed));
    let mut b = [0u8; 48];
    b.copy_from_slice(&p_bytes);
    b[0] |= FLAG_C;
    assert_eq!(g1_from_compressed(&b), Err(BlsError::NonCanonicalField));
    let mut b = [0u8; 48];
    b[0] = FLAG_C | FLAG_INF | FLAG_SIGN;
    assert_eq!(g1_from_compressed(&b), Err(BlsError::NonCanonicalInfinity));
    b[0] = FLAG_C | FLAG_INF;
    b[47] = 1;
    assert_eq!(g1_from_compressed(&b), Err(BlsError::NonCanonicalInfinity));
    let mut b = [0u8; 48];
    b[0] = FLAG_INF;
    assert_eq!(g1_from_compressed(&b), Err(BlsError::NotCompressed));
    // Not on curve: smallest x with x^3 + 4 a non-square.
    let x = (1u64..).find(|&x| {
        let f = Fp::from_u64(x);
        f.sqr().mul(&f).add(&Fp::curve_b()).sqrt().is_none()
    });
    let mut b = Fp::from_u64(x.unwrap()).to_be48();
    b[0] |= FLAG_C;
    assert_eq!(g1_from_compressed(&b), Err(BlsError::NotOnCurve));

    let g2 = G2Affine::generator().to_compressed();
    let mut b = g2;
    b[48..].copy_from_slice(&p_bytes);
    assert_eq!(g2_from_compressed(&b), Err(BlsError::NonCanonicalField));
    let mut b = g2;
    b[..48].copy_from_slice(&p_bytes);
    b[0] |= FLAG_C;
    assert_eq!(g2_from_compressed(&b), Err(BlsError::NonCanonicalField));
    let mut b = g2;
    b[0] &= !FLAG_C;
    assert_eq!(g2_from_compressed(&b), Err(BlsError::NotCompressed));
    let mut b = [0u8; 96];
    b[0] = FLAG_C | FLAG_INF;
    b[60] = 1;
    assert_eq!(g2_from_compressed(&b), Err(BlsError::NonCanonicalInfinity));
}

#[test]
fn off_subgroup_points_are_refused() {
    // G1: an on-curve point outside the order-r subgroup.
    let p = (1u64..)
        .find_map(|x| {
            let xf = Fp::from_u64(x);
            let y = xf.sqr().mul(&xf).add(&Fp::curve_b()).sqrt()?;
            let p = Aff {
                x: xf,
                y,
                inf: false,
            };
            (!in_subgroup(&p)).then_some(p)
        })
        .unwrap();
    assert!(p.on_curve());
    let enc = encode_g1(&p);
    assert_eq!(
        decode_g1_unchecked(&enc).unwrap(),
        p,
        "well-formed on-curve encoding"
    );
    assert_eq!(g1_from_compressed(&enc), Err(BlsError::NotInSubgroup));
    assert_eq!(key_validate(&enc), Err(BlsError::NotInSubgroup));
    // Clearing the G1 cofactor h1 = (x - 1)^2 / 3 lands in G1 and is accepted (the check is not
    // refusing everything).
    let h1 = limbs_from_hex::<2>("396c8c005555e1568c00aaab0000aaab");
    let c = p.to_jac().mul_limbs(&h1).to_affine();
    assert!(!c.inf);
    assert_eq!(g1_from_compressed(&encode_g1(&c)).unwrap().0, c);

    // G2: same, with x = k + i.
    let q = (1u64..)
        .find_map(|k| {
            let xf = Fp2::new(Fp::from_u64(k), Fp::one());
            let y = xf.sqr().mul(&xf).add(&Fp2::curve_b()).sqrt()?;
            let q = Aff {
                x: xf,
                y,
                inf: false,
            };
            (!in_subgroup(&q)).then_some(q)
        })
        .unwrap();
    assert!(q.on_curve());
    let enc2 = encode_g2(&q);
    assert_eq!(decode_g2_unchecked(&enc2).unwrap(), q);
    assert_eq!(g2_from_compressed(&enc2), Err(BlsError::NotInSubgroup));
    let c2 = q.to_jac().mul_limbs(&ctx().h_eff).to_affine();
    assert!(!c2.inf);
    assert_eq!(g2_from_compressed(&encode_g2(&c2)).unwrap().0, c2);

    // A signature that is valid plus an off-subgroup component is refused by verification.
    let sk = crate::sha256(b"subgroup-attack");
    let pk = key_validate(&fixture_sk_to_pk(&sk)).unwrap();
    let sig = fixture_sign(&sk, b"m");
    assert!(verify(&pk, b"m", &sig));
    let s = g2_from_compressed(&sig).unwrap().0;
    let forged = encode_g2(&s.to_jac().add(&q.to_jac()).to_affine());
    assert!(!verify(&pk, b"m", &forged));
    assert!(!verify(&pk, b"m", &enc2));
}

#[test]
fn iso3_constants_match_rfc_extraction() {
    let rows: Vec<Vec<&str>> = data_rows(E3).collect();
    assert_eq!(rows.len(), 13);
    for (row, (i, j, c0, c1)) in rows.iter().zip(ISO3.iter()) {
        assert_eq!(
            (
                row[0].parse::<usize>().unwrap(),
                row[1].parse::<usize>().unwrap()
            ),
            (*i, *j)
        );
        assert_eq!((row[2], row[3]), (*c0, *c1));
    }
    // The isogeny maps E2' points onto E2.
    for i in 0..3 {
        let p = map_to_curve_g2(&seeded_fp2(i));
        assert!(p.on_curve());
        assert!(sswu_e2(&seeded_fp2(i)).inf || !p.inf);
    }
}

#[test]
fn rfc9380_j10_1_hash_to_g2() {
    let mut n = 0;
    for f in data_rows(J10) {
        assert_eq!(f.len(), 17);
        let msg = unhex(f[0]);
        let g = |k: usize| Fp2::from_hex(f[1 + 2 * k], f[2 + 2 * k]);
        let [u0, u1] = hash_to_field_fp2(&msg, RFC_DST);
        assert_eq!((u0, u1), (g(2), g(3)), "u for msg {}", f[0]);
        let q0 = map_to_curve_g2(&u0);
        let q1 = map_to_curve_g2(&u1);
        assert_eq!((q0.x, q0.y), (g(4), g(5)), "Q0");
        assert_eq!((q1.x, q1.y), (g(6), g(7)), "Q1");
        let p = hash_to_g2(&msg, RFC_DST);
        assert_eq!((p.0.x, p.0.y), (g(0), g(1)), "P");
        assert!(in_subgroup(&p.0));
        n += 1;
    }
    assert_eq!(n, 5);
}

fn eth_key(pk: &[u8]) -> Option<G1Affine> {
    key_validate(&arr::<48>(pk)?).ok()
}

fn eth_verify_one(pk: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    let (Some(pk), Some(sig)) = (eth_key(pk), arr::<96>(sig)) else {
        return false;
    };
    verify(&pk, msg, &sig)
}

#[test]
fn eth_deserialization_g1_g2() {
    let rows = eth_rows("deser_g1");
    assert_eq!(rows.len(), 13);
    for f in &rows {
        let b = unhex(f[2]);
        let got = arr::<48>(&b).map(|a| g1_from_compressed(&a));
        assert_eq!(
            got.as_ref().is_some_and(|r| r.is_ok()),
            flag(f[3]),
            "{}",
            f[1]
        );
        if f[1].contains("not_in_G1") {
            assert_eq!(got, Some(Err(BlsError::NotInSubgroup)));
        }
    }
    let rows = eth_rows("deser_g2");
    assert_eq!(rows.len(), 15);
    for f in &rows {
        let b = unhex(f[2]);
        let got = arr::<96>(&b).map(|a| g2_from_compressed(&a));
        assert_eq!(
            got.as_ref().is_some_and(|r| r.is_ok()),
            flag(f[3]),
            "{}",
            f[1]
        );
        if f[1].contains("not_in_G2") {
            assert_eq!(got, Some(Err(BlsError::NotInSubgroup)));
        }
    }
}

#[test]
fn eth_verify() {
    let rows = eth_rows("verify");
    assert_eq!(rows.len(), 29);
    for f in &rows {
        assert_eq!(
            eth_verify_one(&unhex(f[2]), &unhex(f[3]), &unhex(f[4])),
            flag(f[5]),
            "{}",
            f[1]
        );
    }
}

#[test]
fn eth_fast_aggregate_verify() {
    let rows = eth_rows("fav");
    assert_eq!(rows.len(), 12);
    for f in &rows {
        let pks: Option<Vec<G1Affine>> = list(f[2]).iter().map(|b| eth_key(b)).collect();
        let sig = arr::<96>(&unhex(f[4]));
        let got = match (pks, sig) {
            (Some(pks), Some(sig)) => fast_aggregate_verify(&pks, &unhex(f[3]), &sig),
            _ => false,
        };
        assert_eq!(got, flag(f[5]), "{}", f[1]);
    }
}

#[test]
fn eth_aggregate_verify_and_batch_verify() {
    let rows = eth_rows("agg_verify");
    assert_eq!(rows.len(), 5);
    for f in &rows {
        let (pks, msgs) = (list(f[2]), list(f[3]));
        let got = (|| {
            if pks.is_empty() || pks.len() != msgs.len() {
                return false;
            }
            let mut pairs = Vec::new();
            for (pk, m) in pks.iter().zip(msgs.iter()) {
                let Some(pk) = eth_key(pk) else { return false };
                pairs.push((pk, hash_to_g2(m, DST_POP)));
            }
            let Some(Ok(s)) = arr::<96>(&unhex(f[4])).map(|b| g2_from_compressed(&b)) else {
                return false;
            };
            pairs.push((G1Affine(g1_generator_aff().neg()), s));
            pairing_product_is_one(&pairs)
        })();
        assert_eq!(got, flag(f[5]), "{}", f[1]);
    }
    let rows = eth_rows("batch_verify");
    assert_eq!(rows.len(), 4);
    for f in &rows {
        let (pks, msgs, sigs) = (list(f[2]), list(f[3]), list(f[4]));
        let got = pks.len() == msgs.len()
            && pks.len() == sigs.len()
            && pks
                .iter()
                .zip(msgs.iter())
                .zip(sigs.iter())
                .all(|((pk, m), s)| eth_verify_one(pk, m, s));
        assert_eq!(got, flag(f[5]), "{}", f[1]);
    }
}

#[test]
fn eth_sign_aggregate_hash_to_g2() {
    let rows = eth_rows("sign");
    assert_eq!(rows.len(), 10);
    for f in &rows {
        let sk = arr::<32>(&unhex(f[2])).unwrap();
        let msg = unhex(f[3]);
        if f[4] == "!" {
            // Expected error (zero key): the fixture refuses by panicking.
            assert!(
                std::panic::catch_unwind(|| fixture_sign(&sk, &msg)).is_err(),
                "{}",
                f[1]
            );
            continue;
        }
        let sig = fixture_sign(&sk, &msg);
        assert_eq!(hex(&sig), f[4], "{}", f[1]);
        let pk = key_validate(&fixture_sk_to_pk(&sk)).unwrap();
        assert!(verify(&pk, &msg, &sig), "{}", f[1]);
    }
    let rows = eth_rows("aggregate");
    assert_eq!(rows.len(), 6);
    for f in &rows {
        let sigs: Vec<[u8; 96]> = list(f[2]).iter().map(|b| arr::<96>(b).unwrap()).collect();
        if f[3] == "!" {
            // Expected error for the empty set; the fixture documents identity for `[]` instead.
            assert!(sigs.is_empty(), "{}", f[1]);
            continue;
        }
        assert_eq!(hex(&fixture_aggregate_signatures(&sigs)), f[3], "{}", f[1]);
    }
    let rows = eth_rows("hash_to_g2");
    assert_eq!(rows.len(), 4);
    for f in &rows {
        let p = hash_to_g2(&unhex(f[2]), RFC_DST);
        assert_eq!(p.0.x, Fp2::from_hex(f[3], f[4]), "{}", f[1]);
        assert_eq!(p.0.y, Fp2::from_hex(f[5], f[6]), "{}", f[1]);
    }
}

#[test]
fn pairing_bilinearity_and_nondegeneracy() {
    let g1 = g1_generator_aff();
    let g2 = g2_generator_aff();
    let a: u64 = 0x1234_5678_9abc_def1;
    let b: u64 = 0x0fed_cba9_8765_4321;
    let ab = u128::from(a) * u128::from(b);
    let ab_limbs = [ab as u64, (ab >> 64) as u64];
    let ap = g1.to_jac().mul_be(&a.to_be_bytes()).to_affine();
    let bq = g2.to_jac().mul_be(&b.to_be_bytes()).to_affine();
    let abp = g1.to_jac().mul_limbs(&ab_limbs).to_affine();
    let abq = g2.to_jac().mul_limbs(&ab_limbs).to_affine();
    let e = |p: Aff<Fp>, q: Aff<Fp2>| pairing_product(&[(p, q)]);
    let e1 = e(g1, g2);
    assert_ne!(e1, Fp12::one(), "non-degenerate");
    assert_eq!(e1.pow(&ctx().r), Fp12::one(), "e(G1, G2) has order r");
    let e_ab = e(ap, bq);
    assert_eq!(e_ab, e(abp, g2));
    assert_eq!(e_ab, e(g1, abq));
    assert_eq!(e_ab, e1.pow(&ab_limbs));
    // Additivity in the first argument through the multi-Miller loop.
    let sum = ap.to_jac().add(&abp.to_jac()).to_affine();
    assert_eq!(e(sum, g2), pairing_product(&[(ap, g2), (abp, g2)]));
    // Public product API.
    assert!(pairing_product_is_one(&[
        (G1Affine(ap), G2Affine(bq)),
        (G1Affine(abp.neg()), G2Affine(g2)),
    ]));
    let ab1 = g1
        .to_jac()
        .mul_limbs(&[ab_limbs[0].wrapping_add(1), ab_limbs[1]])
        .to_affine();
    assert!(!pairing_product_is_one(&[
        (G1Affine(ap), G2Affine(bq)),
        (G1Affine(ab1.neg()), G2Affine(g2)),
    ]));
    assert!(pairing_product_is_one(&[]));
    assert!(pairing_product_is_one(&[(
        G1Affine(Aff::identity()),
        G2Affine(g2)
    )]));
}

#[test]
fn fixture_sign_verify_and_refusals() {
    let sks: Vec<[u8; 32]> = (1..=3u8).map(|i| crate::sha256(&[i])).collect();
    let pks: Vec<G1Affine> = sks
        .iter()
        .map(|sk| key_validate(&fixture_sk_to_pk(sk)).unwrap())
        .collect();
    let msg = b"obend light-client sync committee";
    let sig = fixture_sign(&sks[0], msg);
    assert!(verify(&pks[0], msg, &sig));
    assert!(!verify(&pks[0], b"another message", &sig), "wrong message");
    assert!(!verify(&pks[1], msg, &sig), "wrong key");
    for idx in [95usize, 60, 20] {
        let mut t = sig;
        t[idx] ^= 1;
        assert!(!verify(&pks[0], msg, &t), "tampered byte {idx}");
    }
    let mut t = sig;
    t[0] ^= FLAG_SIGN;
    assert!(!verify(&pks[0], msg, &t), "negated signature");

    let sigs: Vec<[u8; 96]> = sks.iter().map(|sk| fixture_sign(sk, msg)).collect();
    let agg = fixture_aggregate_signatures(&sigs);
    assert!(fast_aggregate_verify(&pks, msg, &agg));
    assert!(
        !fast_aggregate_verify(&pks[..2], msg, &agg),
        "missing signer"
    );
    assert!(!fast_aggregate_verify(&pks, b"x", &agg), "wrong message");
    assert!(!fast_aggregate_verify(&[], msg, &agg), "empty set");
    assert!(!fast_aggregate_verify(
        &pks,
        msg,
        &G2Affine(Aff::identity()).to_compressed()
    ));
    let inf = G1Affine(Aff::identity());
    assert_eq!(
        key_validate(&inf.to_compressed()),
        Err(BlsError::IdentityPublicKey)
    );
    assert!(!fast_aggregate_verify(&[pks[0].clone(), inf], msg, &sig));
    // Rogue cancellation: pk + (-pk) aggregates to the identity and is refused.
    assert!(!fast_aggregate_verify(
        &[pks[0].clone(), G1Affine(pks[0].0.neg())],
        msg,
        &sig
    ));
    assert!(aggregate_g1(&[pks[0].clone(), G1Affine(pks[0].0.neg())]).is_identity());
    // Secret keys are reduced mod r: r + 1 gives the generator.
    let mut r1 = [0u8; 32];
    r1.copy_from_slice(
        &limbs_to_be(&crate::bigint::limbs_add(&ctx().r, &[1, 0, 0, 0]).0, 32).unwrap(),
    );
    assert_eq!(fixture_sk_to_pk(&r1), G1Affine::generator().to_compressed());
}
