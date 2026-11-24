//! Pure-Integer `FHSDD001` & `FHQPB001` KKT Oracle Verifier (`0` floats, `0` external crates).
//!
//! Quarried and hardened from `breadstuffs/fhir/src/{compile.rs,qp_certificate.rs}` and
//! `breadstuffs/fhegg-solver/src/{qp_exact.rs,qp_strict.rs}`, aligned with
//! `minidregg/Theory/ExactKktClearingCert.lean`:
//!
//! - **Zero floating-point arithmetic (`0` `f32`/`f64`):** Every entry denotes the exact
//!   rational `v / 10^scale` over checked `i128` arithmetic. Overflow fails closed.
//! - **`O(|E|)` Sparse SDD-to-PSD Factor Witness ([`SddFactorWitness`]):** Verifies
//!   `Q = sum_e w_e (e_u - s_e e_v)(e_u - s_e e_v)^T + diag(d)` with `w_e >= 0, d_i >= 0`
//!   in linear `O(|E| + n)` integer operations (no square roots or floating-point eigenvalues).
//! - **Canonical `FHSDD001` Wire Verifier ([`ExactSddPsdCertificate`]):** Byte-compatible
//!   with `breadstuffs/fhir`, enforcing symmetry, non-negative diagonal, exact off-diagonal
//!   row radii, diagonal dominance, SHA-256 checksum, and exact-EOF canonical roundtrip.
//! - **Canonical `FHQPB001` KKT + Matrix-Pin Verifier ([`ExactQpCertificateBundle`]):**
//!   Enforces entry-for-entry Matrix-Pin (`admission.exact_entries() == kkt.p`, closing
//!   `tooth_matrix_pin_omitted_unsound`), exact primal/dual/normal-cone KKT residuals
//!   (catching wrong-sign dual forgery), complete public-problem `(P, q, A, l, u)` binding,
//!   and TEE attestation binding ([`verify_attested_solver_quote`]).

use crate::sha256::{ct_eq, Sha256};
use crate::tee::VerifiedTeeEvidence;

// ---------------------------------------------------------------------------
// Constants (byte-compatible with `breadstuffs/fhir`)
// ---------------------------------------------------------------------------

pub const QP_CERT_EXACT_SCALE: u32 = 9;
pub const MAX_QP_SCALE: u32 = 18;
/// `2^53` exact-entry magnitude bound matching `breadstuffs/fhir/src/compile.rs:154`.
pub const EXACT_ENTRY_BOUND: i128 = 9_007_199_254_740_992;

pub const FHSDD001_MAGIC: &[u8; 8] = b"FHSDD001";
const FHSDD001_VERSION: u8 = 1;
const FHSDD001_CHECKSUM_DOMAIN: &[u8] = b"fhir/exact-sdd-psd-certificate/v1";
const FHSDD001_HEADER_LEN: usize = 8 + 1 + 4 + 8 + 8 + 8;
const CHECKSUM_LEN: usize = 32;
pub const MAX_EXACT_SDD_DIMENSION: usize = 2048;
pub const MAX_EXACT_SDD_WIRE_BYTES: usize = FHSDD001_HEADER_LEN
    + 16 * (MAX_EXACT_SDD_DIMENSION * MAX_EXACT_SDD_DIMENSION + MAX_EXACT_SDD_DIMENSION)
    + CHECKSUM_LEN;

pub const FHQPB001_MAGIC: &[u8; 8] = b"FHQPB001";
const FHQPB001_VERSION: u8 = 1;
const FHQPB001_CHECKSUM_DOMAIN: &[u8] = b"fhir/exact-qp-certificate-bundle/v1";
const FHQPB001_PROGRAM_DIGEST_DOMAIN: &[u8] = b"fhir/exact-qp-public-program/v1";
const FHQPB001_HEADER_LEN: usize = 8 + 1 + 4 + 4 + 4 + 4;
pub const MAX_QP_BUNDLE_DIMENSION: usize = 1024;
pub const MAX_QP_BUNDLE_WIRE_BYTES: usize = 64 * 1024 * 1024;

// ---------------------------------------------------------------------------
// O(|E|) Sparse SDD-Laplacian Factor Witness (`sddFactor_implies_psd`)
// ---------------------------------------------------------------------------

/// One non-negative weighted rank-1 SDD factor edge:
/// `weight * (e_u - sign * e_v)(e_u - sign * e_v)^T` where `sign = if negative_offdiag { +1 } else { -1 }`.
/// - When `negative_offdiag = true`: contributes `+w` to `(u,u)` and `(v,v)` and `-w` to `(u,v)` and `(v,u)`.
/// - When `negative_offdiag = false`: contributes `+w` to `(u,u)` and `(v,v)` and `+w` to `(u,v)` and `(v,u)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SddFactorEdge {
    pub u: usize,
    pub v: usize,
    pub weight: i128,
    pub negative_offdiag: bool,
}

/// Sparse `O(|E| + n)` exact-integer witness that `Q = sum_e w_e b_e b_e^T + diag(d)` is PSD.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SddFactorWitness {
    pub dimension: usize,
    pub scale: u32,
    pub edges: Vec<SddFactorEdge>,
    pub diag_slack: Vec<i128>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SddFactorError {
    EmptyDimension,
    DimensionTooLarge { found: usize, maximum: usize },
    ScaleTooLarge { found: u32, maximum: u32 },
    DiagSlackLengthMismatch,
    NegativeDiagSlack { index: usize },
    NegativeEdgeWeight { edge_index: usize },
    SelfLoopEdge { edge_index: usize },
    VertexOutOfBounds { edge_index: usize },
    ArithmeticOverflow,
    EntryOutOfRange { index: usize },
    MatrixMismatch { index: usize },
}

/// Verify an `O(|E| + n)` SDD-Laplacian PSD factor witness in pure checked `i128` arithmetic.
pub fn verify_sdd_factor_witness(w: &SddFactorWitness) -> Result<(), SddFactorError> {
    if w.dimension == 0 {
        return Err(SddFactorError::EmptyDimension);
    }
    if w.dimension > MAX_EXACT_SDD_DIMENSION {
        return Err(SddFactorError::DimensionTooLarge {
            found: w.dimension,
            maximum: MAX_EXACT_SDD_DIMENSION,
        });
    }
    if w.scale > MAX_QP_SCALE {
        return Err(SddFactorError::ScaleTooLarge {
            found: w.scale,
            maximum: MAX_QP_SCALE,
        });
    }
    if w.diag_slack.len() != w.dimension {
        return Err(SddFactorError::DiagSlackLengthMismatch);
    }
    for (i, &d) in w.diag_slack.iter().enumerate() {
        if d < 0 {
            return Err(SddFactorError::NegativeDiagSlack { index: i });
        }
    }
    for (edge_index, e) in w.edges.iter().enumerate() {
        if e.u >= w.dimension || e.v >= w.dimension {
            return Err(SddFactorError::VertexOutOfBounds { edge_index });
        }
        if e.u == e.v {
            return Err(SddFactorError::SelfLoopEdge { edge_index });
        }
        if e.weight < 0 {
            return Err(SddFactorError::NegativeEdgeWeight { edge_index });
        }
    }
    Ok(())
}

impl SddFactorWitness {
    /// Materialize the exact dense symmetric SDD matrix `P` and row radii implied by this
    /// `O(|E| + n)` witness, then package it as a verified [`ExactSddPsdCertificate`].
    pub fn to_sdd_certificate(&self) -> Result<ExactSddPsdCertificate, SddFactorError> {
        verify_sdd_factor_witness(self)?;
        let n = self.dimension;
        let nn = n.checked_mul(n).ok_or(SddFactorError::ArithmeticOverflow)?;
        let mut p = vec![0i128; nn];
        for (i, &d) in self.diag_slack.iter().enumerate() {
            p[i * n + i] = d;
        }
        for e in &self.edges {
            let off = if e.negative_offdiag {
                e.weight
                    .checked_neg()
                    .ok_or(SddFactorError::ArithmeticOverflow)?
            } else {
                e.weight
            };
            p[e.u * n + e.u] = p[e.u * n + e.u]
                .checked_add(e.weight)
                .ok_or(SddFactorError::ArithmeticOverflow)?;
            p[e.v * n + e.v] = p[e.v * n + e.v]
                .checked_add(e.weight)
                .ok_or(SddFactorError::ArithmeticOverflow)?;
            p[e.u * n + e.v] = p[e.u * n + e.v]
                .checked_add(off)
                .ok_or(SddFactorError::ArithmeticOverflow)?;
            p[e.v * n + e.u] = p[e.v * n + e.u]
                .checked_add(off)
                .ok_or(SddFactorError::ArithmeticOverflow)?;
        }
        for (index, &v) in p.iter().enumerate() {
            if v.checked_abs()
                .ok_or(SddFactorError::EntryOutOfRange { index })?
                > EXACT_ENTRY_BOUND
            {
                return Err(SddFactorError::EntryOutOfRange { index });
            }
        }
        let mut row_radii = vec![0i128; n];
        for row in 0..n {
            let mut sum = 0i128;
            for col in 0..n {
                if col == row {
                    continue;
                }
                let a = p[row * n + col]
                    .checked_abs()
                    .ok_or(SddFactorError::ArithmeticOverflow)?;
                sum = sum
                    .checked_add(a)
                    .ok_or(SddFactorError::ArithmeticOverflow)?;
            }
            row_radii[row] = sum;
        }
        ExactSddPsdCertificate::from_exact_matrix(n, self.scale, p, row_radii)
            .map_err(|_| SddFactorError::ArithmeticOverflow)
    }

    /// Verify that this `O(|E| + n)` SDD factor witness expands entry-for-entry to `target_p`.
    pub fn verify_matches_dense(&self, target_p: &[i128]) -> Result<(), SddFactorError> {
        let cert = self.to_sdd_certificate()?;
        if cert.exact_entries().len() != target_p.len() {
            return Err(SddFactorError::MatrixMismatch { index: 0 });
        }
        for (index, (a, b)) in cert.exact_entries().iter().zip(target_p).enumerate() {
            if a != b {
                return Err(SddFactorError::MatrixMismatch { index });
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// FHSDD001 Canonical Wire Certificate
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSddPsdCertificate {
    version: u8,
    scale: u32,
    dimension: usize,
    exact_entries: Vec<i128>,
    row_radii: Vec<i128>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactSddPsdCertificateError {
    UnsupportedVersion { found: u8 },
    UnsupportedScale { found: u32 },
    EmptyDimension,
    DimensionOverflow,
    DimensionTooLarge { found: usize, maximum: usize },
    ExactEntryCount { actual: usize, expected: usize },
    RowRadiusCount { actual: usize, expected: usize },
    ExactEntryOutOfRange { index: usize },
    Asymmetric { row: usize, col: usize },
    NegativeDiagonal { row: usize },
    RowAbsoluteSumOverflow { row: usize },
    RowRadiusMismatch { row: usize },
    NotDiagonallyDominant { row: usize },
    MalformedWire,
    WireTooLarge { actual: usize, maximum: usize },
    ChecksumMismatch,
}

impl ExactSddPsdCertificate {
    /// Construct and verify an exact-integer `FHSDD001` certificate directly from integer entries
    /// (zero floating-point conversion).
    pub fn from_exact_matrix(
        dimension: usize,
        scale: u32,
        exact_entries: Vec<i128>,
        row_radii: Vec<i128>,
    ) -> Result<Self, ExactSddPsdCertificateError> {
        let cert = Self {
            version: FHSDD001_VERSION,
            scale,
            dimension,
            exact_entries,
            row_radii,
        };
        cert.verify_structure()?;
        Ok(cert)
    }

    pub fn version(&self) -> u8 {
        self.version
    }
    pub fn scale(&self) -> u32 {
        self.scale
    }
    pub fn dimension(&self) -> usize {
        self.dimension
    }
    pub fn exact_entries(&self) -> &[i128] {
        &self.exact_entries
    }
    pub fn row_radii(&self) -> &[i128] {
        &self.row_radii
    }

    pub fn verify_structure(&self) -> Result<usize, ExactSddPsdCertificateError> {
        if self.version != FHSDD001_VERSION {
            return Err(ExactSddPsdCertificateError::UnsupportedVersion {
                found: self.version,
            });
        }
        if self.scale > MAX_QP_SCALE {
            return Err(ExactSddPsdCertificateError::UnsupportedScale { found: self.scale });
        }
        if self.dimension == 0 {
            return Err(ExactSddPsdCertificateError::EmptyDimension);
        }
        if self.dimension > MAX_EXACT_SDD_DIMENSION {
            return Err(ExactSddPsdCertificateError::DimensionTooLarge {
                found: self.dimension,
                maximum: MAX_EXACT_SDD_DIMENSION,
            });
        }
        let expected_len = self
            .dimension
            .checked_mul(self.dimension)
            .ok_or(ExactSddPsdCertificateError::DimensionOverflow)?;
        if self.exact_entries.len() != expected_len {
            return Err(ExactSddPsdCertificateError::ExactEntryCount {
                actual: self.exact_entries.len(),
                expected: expected_len,
            });
        }
        if self.row_radii.len() != self.dimension {
            return Err(ExactSddPsdCertificateError::RowRadiusCount {
                actual: self.row_radii.len(),
                expected: self.dimension,
            });
        }
        for (index, entry) in self.exact_entries.iter().copied().enumerate() {
            let mag = entry
                .checked_abs()
                .ok_or(ExactSddPsdCertificateError::ExactEntryOutOfRange { index })?;
            if mag > EXACT_ENTRY_BOUND {
                return Err(ExactSddPsdCertificateError::ExactEntryOutOfRange { index });
            }
        }
        for row in 0..self.dimension {
            for col in 0..row {
                if self.exact_entries[row * self.dimension + col]
                    != self.exact_entries[col * self.dimension + row]
                {
                    return Err(ExactSddPsdCertificateError::Asymmetric { row, col });
                }
            }
            let diag = self.exact_entries[row * self.dimension + row];
            if diag < 0 {
                return Err(ExactSddPsdCertificateError::NegativeDiagonal { row });
            }
            let mut radius = 0i128;
            for col in 0..self.dimension {
                if col == row {
                    continue;
                }
                let mag = self.exact_entries[row * self.dimension + col]
                    .checked_abs()
                    .ok_or(ExactSddPsdCertificateError::RowAbsoluteSumOverflow { row })?;
                radius = radius
                    .checked_add(mag)
                    .ok_or(ExactSddPsdCertificateError::RowAbsoluteSumOverflow { row })?;
            }
            if self.row_radii[row] != radius {
                return Err(ExactSddPsdCertificateError::RowRadiusMismatch { row });
            }
            if diag < radius {
                return Err(ExactSddPsdCertificateError::NotDiagonallyDominant { row });
            }
        }
        Ok(expected_len)
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, ExactSddPsdCertificateError> {
        self.verify_structure()?;
        let wire_len = exact_sdd_wire_len(self.dimension)?;
        let mut out = Vec::with_capacity(wire_len);
        out.extend_from_slice(FHSDD001_MAGIC);
        out.push(self.version);
        out.extend_from_slice(&self.scale.to_be_bytes());
        out.extend_from_slice(&(self.dimension as u64).to_be_bytes());
        out.extend_from_slice(&(self.exact_entries.len() as u64).to_be_bytes());
        out.extend_from_slice(&(self.row_radii.len() as u64).to_be_bytes());
        for &entry in &self.exact_entries {
            out.extend_from_slice(&entry.to_be_bytes());
        }
        for &radius in &self.row_radii {
            out.extend_from_slice(&radius.to_be_bytes());
        }
        let checksum = domain_checksum(FHSDD001_CHECKSUM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, ExactSddPsdCertificateError> {
        if bytes.len() > MAX_EXACT_SDD_WIRE_BYTES {
            return Err(ExactSddPsdCertificateError::WireTooLarge {
                actual: bytes.len(),
                maximum: MAX_EXACT_SDD_WIRE_BYTES,
            });
        }
        if bytes.len() < FHSDD001_HEADER_LEN + CHECKSUM_LEN {
            return Err(ExactSddPsdCertificateError::MalformedWire);
        }
        let mut cur = ByteCursor::new(bytes);
        if cur
            .take::<8>()
            .ok_or(ExactSddPsdCertificateError::MalformedWire)?
            != *FHSDD001_MAGIC
        {
            return Err(ExactSddPsdCertificateError::MalformedWire);
        }
        let version = cur
            .take::<1>()
            .ok_or(ExactSddPsdCertificateError::MalformedWire)?[0];
        if version != FHSDD001_VERSION {
            return Err(ExactSddPsdCertificateError::UnsupportedVersion { found: version });
        }
        let scale = u32::from_be_bytes(
            cur.take::<4>()
                .ok_or(ExactSddPsdCertificateError::MalformedWire)?,
        );
        if scale > MAX_QP_SCALE {
            return Err(ExactSddPsdCertificateError::UnsupportedScale { found: scale });
        }
        let dimension = usize::try_from(u64::from_be_bytes(
            cur.take::<8>()
                .ok_or(ExactSddPsdCertificateError::MalformedWire)?,
        ))
        .map_err(|_| ExactSddPsdCertificateError::DimensionOverflow)?;
        if dimension == 0 {
            return Err(ExactSddPsdCertificateError::EmptyDimension);
        }
        if dimension > MAX_EXACT_SDD_DIMENSION {
            return Err(ExactSddPsdCertificateError::DimensionTooLarge {
                found: dimension,
                maximum: MAX_EXACT_SDD_DIMENSION,
            });
        }
        let expected_entries = dimension
            .checked_mul(dimension)
            .ok_or(ExactSddPsdCertificateError::DimensionOverflow)?;
        let entry_count = usize::try_from(u64::from_be_bytes(
            cur.take::<8>()
                .ok_or(ExactSddPsdCertificateError::MalformedWire)?,
        ))
        .map_err(|_| ExactSddPsdCertificateError::DimensionOverflow)?;
        let radius_count = usize::try_from(u64::from_be_bytes(
            cur.take::<8>()
                .ok_or(ExactSddPsdCertificateError::MalformedWire)?,
        ))
        .map_err(|_| ExactSddPsdCertificateError::DimensionOverflow)?;
        if entry_count != expected_entries {
            return Err(ExactSddPsdCertificateError::ExactEntryCount {
                actual: entry_count,
                expected: expected_entries,
            });
        }
        if radius_count != dimension {
            return Err(ExactSddPsdCertificateError::RowRadiusCount {
                actual: radius_count,
                expected: dimension,
            });
        }
        let expected_wire_len = exact_sdd_wire_len(dimension)?;
        if bytes.len() != expected_wire_len {
            return Err(ExactSddPsdCertificateError::MalformedWire);
        }
        let payload_len = expected_wire_len - CHECKSUM_LEN;
        let expected_checksum = domain_checksum(FHSDD001_CHECKSUM_DOMAIN, &bytes[..payload_len]);
        if !ct_eq(&bytes[payload_len..], &expected_checksum) {
            return Err(ExactSddPsdCertificateError::ChecksumMismatch);
        }
        let mut exact_entries = Vec::with_capacity(entry_count);
        for _ in 0..entry_count {
            exact_entries.push(i128::from_be_bytes(
                cur.take::<16>()
                    .ok_or(ExactSddPsdCertificateError::MalformedWire)?,
            ));
        }
        let mut row_radii = Vec::with_capacity(radius_count);
        for _ in 0..radius_count {
            row_radii.push(i128::from_be_bytes(
                cur.take::<16>()
                    .ok_or(ExactSddPsdCertificateError::MalformedWire)?,
            ));
        }
        let trailing_checksum = cur
            .take::<32>()
            .ok_or(ExactSddPsdCertificateError::MalformedWire)?;
        if !ct_eq(&trailing_checksum, &expected_checksum) || !cur.is_finished() {
            return Err(ExactSddPsdCertificateError::MalformedWire);
        }
        let cert = Self {
            version,
            scale,
            dimension,
            exact_entries,
            row_radii,
        };
        cert.verify_structure()?;
        if cert.to_wire_bytes()?.as_slice() != bytes {
            return Err(ExactSddPsdCertificateError::MalformedWire);
        }
        Ok(cert)
    }
}

fn exact_sdd_wire_len(dimension: usize) -> Result<usize, ExactSddPsdCertificateError> {
    if dimension == 0 {
        return Err(ExactSddPsdCertificateError::EmptyDimension);
    }
    if dimension > MAX_EXACT_SDD_DIMENSION {
        return Err(ExactSddPsdCertificateError::DimensionTooLarge {
            found: dimension,
            maximum: MAX_EXACT_SDD_DIMENSION,
        });
    }
    let entries = dimension
        .checked_mul(dimension)
        .ok_or(ExactSddPsdCertificateError::DimensionOverflow)?;
    entries
        .checked_add(dimension)
        .and_then(|c| c.checked_mul(16))
        .and_then(|b| b.checked_add(FHSDD001_HEADER_LEN))
        .and_then(|b| b.checked_add(CHECKSUM_LEN))
        .filter(|&len| len <= MAX_EXACT_SDD_WIRE_BYTES)
        .ok_or(ExactSddPsdCertificateError::DimensionOverflow)
}

// ---------------------------------------------------------------------------
// Exact Integer QP Problem, Primal-Dual KKT Checker & FHQPB001 Bundle
// ---------------------------------------------------------------------------

/// Pure-integer caller-authorized QP problem `(P, q, A, l, u)` at fixed-point scale `10^scale`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactQpProblem {
    pub n: usize,
    pub mc: usize,
    pub scale: u32,
    pub p: Vec<i128>,
    pub q: Vec<i128>,
    pub a: Vec<i128>,
    pub l: Vec<i128>,
    pub u: Vec<i128>,
}

impl ExactQpProblem {
    pub fn program_digest(&self) -> [u8; 32] {
        compute_qp_program_digest(
            self.n, self.mc, self.scale, &self.p, &self.q, &self.a, &self.l, &self.u,
        )
    }
}

/// Pure-integer KKT certificate matching `fhegg-solver/src/qp_exact.rs` (`0` floats).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactQpKktCert {
    pub n: usize,
    pub mc: usize,
    pub scale: u32,
    pub p: Vec<i128>,
    pub q: Vec<i128>,
    pub a: Vec<i128>,
    pub l: Vec<i128>,
    pub u: Vec<i128>,
    pub x: Vec<i128>,
    pub y: Vec<i128>,
    pub epsilon: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KktResidualReport {
    pub well_formed: bool,
    pub overflow: bool,
    pub primal_feasible: bool,
    pub dual_feasible: bool,
    pub normal_cone: bool,
    pub prim_res: Option<i128>,
    pub dual_res: Option<i128>,
    pub normal_res: Option<i128>,
    pub tol: Option<i128>,
    pub valid: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QpProblemBindingError {
    ScaleMismatch {
        certificate: u32,
        expected: u32,
    },
    DimensionMismatch {
        certificate_n: usize,
        certificate_mc: usize,
        program_n: usize,
        program_mc: usize,
    },
    FieldMismatch {
        field: &'static str,
        index: usize,
    },
}

fn row_dot(row: &[i128], v: &[i128]) -> Option<i128> {
    let mut acc = 0i128;
    for (&a, &b) in row.iter().zip(v.iter()) {
        acc = acc.checked_add(a.checked_mul(b)?)?;
    }
    Some(acc)
}

impl ExactQpKktCert {
    pub fn well_formed(&self) -> bool {
        self.n > 0
            && self.scale <= MAX_QP_SCALE
            && self.n.checked_mul(self.n) == Some(self.p.len())
            && self.mc.checked_mul(self.n) == Some(self.a.len())
            && self.q.len() == self.n
            && self.l.len() == self.mc
            && self.u.len() == self.mc
            && self.x.len() == self.n
            && self.y.len() == self.mc
            && self.epsilon >= 0
            && self.l.iter().zip(&self.u).all(|(l, u)| l <= u)
    }

    /// Recompute exact primal, dual, and normal-cone residuals at scale `S^2` using checked `i128`.
    /// Overflow fails closed (`overflow: true`, `valid: false`).
    pub fn check(&self) -> KktResidualReport {
        if !self.well_formed() {
            return KktResidualReport {
                well_formed: false,
                overflow: false,
                primal_feasible: false,
                dual_feasible: false,
                normal_cone: false,
                prim_res: None,
                dual_res: None,
                normal_res: None,
                tol: None,
                valid: false,
            };
        }
        match self.residuals() {
            None => KktResidualReport {
                well_formed: true,
                overflow: true,
                primal_feasible: false,
                dual_feasible: false,
                normal_cone: false,
                prim_res: None,
                dual_res: None,
                normal_res: None,
                tol: None,
                valid: false,
            },
            Some((prim, dual, normal, tol)) => {
                let primal_feasible = prim <= tol;
                let dual_feasible = dual <= tol;
                let normal_cone = normal <= tol;
                KktResidualReport {
                    well_formed: true,
                    overflow: false,
                    primal_feasible,
                    dual_feasible,
                    normal_cone,
                    prim_res: Some(prim),
                    dual_res: Some(dual),
                    normal_res: Some(normal),
                    tol: Some(tol),
                    valid: primal_feasible && dual_feasible && normal_cone,
                }
            }
        }
    }

    fn residuals(&self) -> Option<(i128, i128, i128, i128)> {
        let s = 10i128.checked_pow(self.scale)?;
        let (n, mc) = (self.n, self.mc);

        let mut prim = 0i128;
        let mut normal = 0i128;
        for i in 0..mc {
            let ax_i = row_dot(&self.a[i * n..(i + 1) * n], &self.x)?;
            let us = self.u[i].checked_mul(s)?;
            let ls = self.l[i].checked_mul(s)?;
            let over = ax_i.checked_sub(us)?.max(0);
            let under = ls.checked_sub(ax_i)?.max(0);
            prim = prim.max(over.checked_add(under)?);

            let shifted = ax_i.checked_add(self.y[i].checked_mul(s)?)?;
            let projected = shifted.clamp(ls, us);
            normal = normal.max(ax_i.checked_sub(projected)?.checked_abs()?);
        }

        let mut dual = 0i128;
        for j in 0..n {
            let px_j = row_dot(&self.p[j * n..(j + 1) * n], &self.x)?;
            let mut aty_j = 0i128;
            for i in 0..mc {
                aty_j = aty_j.checked_add(self.a[i * n + j].checked_mul(self.y[i])?)?;
            }
            let qs = self.q[j].checked_mul(s)?;
            let stat = px_j.checked_add(qs)?.checked_add(aty_j)?;
            dual = dual.max(stat.checked_abs()?);
        }

        let tol = self.epsilon.checked_mul(s)?;
        Some((prim, dual, normal, tol))
    }

    pub fn verify_problem_binding(
        &self,
        problem: &ExactQpProblem,
    ) -> Result<(), QpProblemBindingError> {
        if self.scale != problem.scale {
            return Err(QpProblemBindingError::ScaleMismatch {
                certificate: self.scale,
                expected: problem.scale,
            });
        }
        if self.n != problem.n || self.mc != problem.mc {
            return Err(QpProblemBindingError::DimensionMismatch {
                certificate_n: self.n,
                certificate_mc: self.mc,
                program_n: problem.n,
                program_mc: problem.mc,
            });
        }
        let check_slice =
            |field: &'static str, a: &[i128], b: &[i128]| -> Result<(), QpProblemBindingError> {
                if a.len() != b.len() {
                    return Err(QpProblemBindingError::FieldMismatch { field, index: 0 });
                }
                for (index, (x, y)) in a.iter().zip(b.iter()).enumerate() {
                    if x != y {
                        return Err(QpProblemBindingError::FieldMismatch { field, index });
                    }
                }
                Ok(())
            };
        check_slice("p", &self.p, &problem.p)?;
        check_slice("q", &self.q, &problem.q)?;
        check_slice("a", &self.a, &problem.a)?;
        check_slice("l", &self.l, &problem.l)?;
        check_slice("u", &self.u, &problem.u)?;
        Ok(())
    }

    pub fn program_digest(&self) -> [u8; 32] {
        compute_qp_program_digest(
            self.n, self.mc, self.scale, &self.p, &self.q, &self.a, &self.l, &self.u,
        )
    }
}

/// Exact representation of twice the QP objective: `(x^T P x + 2 S q^T x) / 10^(3*scale)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactQpObjectiveValue {
    twice_numerator: i128,
    scale_digits: u32,
}

impl ExactQpObjectiveValue {
    pub const fn twice_numerator(self) -> i128 {
        self.twice_numerator
    }
    pub const fn scale_digits(self) -> u32 {
        self.scale_digits
    }
}

fn compute_exact_objective(kkt: &ExactQpKktCert) -> Option<ExactQpObjectiveValue> {
    let s = 10i128.checked_pow(kkt.scale)?;
    let n = kkt.n;
    let mut quad = 0i128;
    for row in 0..n {
        for col in 0..n {
            let t = kkt.x[row]
                .checked_mul(kkt.p[row * n + col])?
                .checked_mul(kkt.x[col])?;
            quad = quad.checked_add(t)?;
        }
    }
    let mut lin = 0i128;
    for (&q, &x) in kkt.q.iter().zip(&kkt.x) {
        lin = lin.checked_add(q.checked_mul(x)?)?;
    }
    let twice_lin = lin.checked_mul(2)?.checked_mul(s)?;
    Some(ExactQpObjectiveValue {
        twice_numerator: quad.checked_add(twice_lin)?,
        scale_digits: kkt.scale.checked_mul(3)?,
    })
}

/// Self-contained `FHQPB001` bundle joining an `FHSDD001` PSD admission witness and an exact KKT
/// certificate with mandatory entry-for-entry Matrix-Pin (`admission.exact_entries() == kkt.p`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactQpCertificateBundle {
    admission: ExactSddPsdCertificate,
    kkt: ExactQpKktCert,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactQpCertificateBundleError {
    Admission(ExactSddPsdCertificateError),
    KktInvalid,
    KktOverflow,
    ScaleMismatch,
    DimensionMismatch,
    MatrixPinMismatch { index: usize },
    DimensionTooLarge { n: usize, mc: usize },
    ArithmeticOverflow,
    WireTooLarge { actual: usize, maximum: usize },
    MalformedWire,
    UnsupportedVersion { found: u8 },
    ChecksumMismatch,
    ProgramBinding(QpProblemBindingError),
    NonZeroTolerance { epsilon: i128 },
    NonZeroResidual,
    QuoteAttestationMismatch,
}

impl From<ExactSddPsdCertificateError> for ExactQpCertificateBundleError {
    fn from(e: ExactSddPsdCertificateError) -> Self {
        Self::Admission(e)
    }
}

impl From<QpProblemBindingError> for ExactQpCertificateBundleError {
    fn from(e: QpProblemBindingError) -> Self {
        Self::ProgramBinding(e)
    }
}

impl ExactQpCertificateBundle {
    /// Join an `FHSDD001` admission witness and an `ExactQpKktCert`, re-checking both AND
    /// enforcing the mandatory Matrix-Pin (`admission.exact_entries() == kkt.p`).
    pub fn new(
        admission: ExactSddPsdCertificate,
        kkt: ExactQpKktCert,
    ) -> Result<Self, ExactQpCertificateBundleError> {
        let bundle = Self { admission, kkt };
        bundle.verify()?;
        Ok(bundle)
    }

    pub fn admission(&self) -> &ExactSddPsdCertificate {
        &self.admission
    }
    pub fn kkt(&self) -> &ExactQpKktCert {
        &self.kkt
    }

    pub fn verify(&self) -> Result<KktResidualReport, ExactQpCertificateBundleError> {
        self.admission.verify_structure()?;
        if self.kkt.n == 0
            || self.kkt.n > MAX_QP_BUNDLE_DIMENSION
            || self.kkt.mc > MAX_QP_BUNDLE_DIMENSION
        {
            return Err(ExactQpCertificateBundleError::DimensionTooLarge {
                n: self.kkt.n,
                mc: self.kkt.mc,
            });
        }
        // Mandatory Matrix-Pin: scale, dimension, and entry-for-entry P agreement.
        if self.admission.scale() != self.kkt.scale {
            return Err(ExactQpCertificateBundleError::ScaleMismatch);
        }
        if self.admission.dimension() != self.kkt.n
            || self.admission.exact_entries().len() != self.kkt.p.len()
        {
            return Err(ExactQpCertificateBundleError::DimensionMismatch);
        }
        for (index, (admitted, used)) in self
            .admission
            .exact_entries()
            .iter()
            .zip(&self.kkt.p)
            .enumerate()
        {
            if admitted != used {
                return Err(ExactQpCertificateBundleError::MatrixPinMismatch { index });
            }
        }
        let report = self.kkt.check();
        if report.overflow {
            return Err(ExactQpCertificateBundleError::KktOverflow);
        }
        if !report.valid {
            return Err(ExactQpCertificateBundleError::KktInvalid);
        }
        let admission_len = self.admission.to_wire_bytes()?.len();
        exact_qp_wire_len(self.kkt.n, self.kkt.mc, admission_len)?;
        Ok(report)
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, ExactQpCertificateBundleError> {
        self.verify()?;
        self.to_wire_bytes_unchecked()
    }

    fn to_wire_bytes_unchecked(&self) -> Result<Vec<u8>, ExactQpCertificateBundleError> {
        let admission_bytes = self.admission.to_wire_bytes()?;
        let wire_len = exact_qp_wire_len(self.kkt.n, self.kkt.mc, admission_bytes.len())?;
        let mut out = Vec::with_capacity(wire_len);
        out.extend_from_slice(FHQPB001_MAGIC);
        out.push(FHQPB001_VERSION);
        out.extend_from_slice(&(admission_bytes.len() as u32).to_be_bytes());
        out.extend_from_slice(&(self.kkt.n as u32).to_be_bytes());
        out.extend_from_slice(&(self.kkt.mc as u32).to_be_bytes());
        out.extend_from_slice(&self.kkt.scale.to_be_bytes());
        out.extend_from_slice(&admission_bytes);
        push_i128s(&mut out, &self.kkt.p);
        push_i128s(&mut out, &self.kkt.q);
        push_i128s(&mut out, &self.kkt.a);
        push_i128s(&mut out, &self.kkt.l);
        push_i128s(&mut out, &self.kkt.u);
        push_i128s(&mut out, &self.kkt.x);
        push_i128s(&mut out, &self.kkt.y);
        out.extend_from_slice(&self.kkt.epsilon.to_be_bytes());
        let checksum = domain_checksum(FHQPB001_CHECKSUM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        Ok(out)
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, ExactQpCertificateBundleError> {
        if bytes.len() > MAX_QP_BUNDLE_WIRE_BYTES {
            return Err(ExactQpCertificateBundleError::WireTooLarge {
                actual: bytes.len(),
                maximum: MAX_QP_BUNDLE_WIRE_BYTES,
            });
        }
        if bytes.len() < FHQPB001_HEADER_LEN + CHECKSUM_LEN {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let payload_len = bytes.len() - CHECKSUM_LEN;
        let expected_checksum = domain_checksum(FHQPB001_CHECKSUM_DOMAIN, &bytes[..payload_len]);
        if !ct_eq(&bytes[payload_len..], &expected_checksum) {
            return Err(ExactQpCertificateBundleError::ChecksumMismatch);
        }
        let mut cur = ByteCursor::new(&bytes[..payload_len]);
        if cur
            .take::<8>()
            .ok_or(ExactQpCertificateBundleError::MalformedWire)?
            != *FHQPB001_MAGIC
        {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let version = cur
            .take::<1>()
            .ok_or(ExactQpCertificateBundleError::MalformedWire)?[0];
        if version != FHQPB001_VERSION {
            return Err(ExactQpCertificateBundleError::UnsupportedVersion { found: version });
        }
        let admission_len = u32::from_be_bytes(
            cur.take::<4>()
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
        ) as usize;
        let n = u32::from_be_bytes(
            cur.take::<4>()
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
        ) as usize;
        let mc = u32::from_be_bytes(
            cur.take::<4>()
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
        ) as usize;
        let scale = u32::from_be_bytes(
            cur.take::<4>()
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
        );
        if n == 0 || n > MAX_QP_BUNDLE_DIMENSION || mc > MAX_QP_BUNDLE_DIMENSION {
            return Err(ExactQpCertificateBundleError::DimensionTooLarge { n, mc });
        }
        let expected_wire_len = exact_qp_wire_len(n, mc, admission_len)?;
        if expected_wire_len != bytes.len() {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let admission_slice = cur
            .take_slice(admission_len)
            .ok_or(ExactQpCertificateBundleError::MalformedWire)?;
        let admission = ExactSddPsdCertificate::from_wire_bytes(admission_slice)?;
        let nn = n
            .checked_mul(n)
            .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
        let mn = mc
            .checked_mul(n)
            .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
        let kkt = ExactQpKktCert {
            n,
            mc,
            scale,
            p: cur
                .take_i128s(nn)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            q: cur
                .take_i128s(n)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            a: cur
                .take_i128s(mn)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            l: cur
                .take_i128s(mc)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            u: cur
                .take_i128s(mc)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            x: cur
                .take_i128s(n)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            y: cur
                .take_i128s(mc)
                .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            epsilon: i128::from_be_bytes(
                cur.take::<16>()
                    .ok_or(ExactQpCertificateBundleError::MalformedWire)?,
            ),
        };
        if !cur.is_finished() {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        let bundle = Self::new(admission, kkt)?;
        if bundle.to_wire_bytes_unchecked()?.as_slice() != bytes {
            return Err(ExactQpCertificateBundleError::MalformedWire);
        }
        Ok(bundle)
    }
}

// ---------------------------------------------------------------------------
// Sealed Verified Capabilities & Attested Off-Chain Solver Quote Gate
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedExactQpCertificate {
    bundle: ExactQpCertificateBundle,
    program_digest: [u8; 32],
    wire_checksum: [u8; 32],
    report: KktResidualReport,
}

impl VerifiedExactQpCertificate {
    pub fn bundle(&self) -> &ExactQpCertificateBundle {
        &self.bundle
    }
    pub fn program_digest(&self) -> [u8; 32] {
        self.program_digest
    }
    pub fn wire_checksum(&self) -> [u8; 32] {
        self.wire_checksum
    }
    pub fn report(&self) -> &KktResidualReport {
        &self.report
    }
    pub fn solution(&self) -> (&[i128], &[i128], u32) {
        (
            &self.bundle.kkt.x,
            &self.bundle.kkt.y,
            self.bundle.kkt.scale,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedZeroKktQpCertificate {
    certified: VerifiedExactQpCertificate,
    objective: ExactQpObjectiveValue,
}

impl VerifiedZeroKktQpCertificate {
    pub fn certified(&self) -> &VerifiedExactQpCertificate {
        &self.certified
    }
    pub fn program_digest(&self) -> [u8; 32] {
        self.certified.program_digest()
    }
    pub fn solution(&self) -> (&[i128], &[i128], u32) {
        self.certified.solution()
    }
    pub fn objective(&self) -> ExactQpObjectiveValue {
        self.objective
    }
}

/// Sealed off-chain solver quote combining a verified zero-KKT `FHQPB001` bundle with a
/// sealed [`VerifiedTeeEvidence`] attestation token bound via `report_data[0..32]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedSolverQuote {
    zero_kkt: VerifiedZeroKktQpCertificate,
    tee_evidence_digest: [u8; 32],
    quote_nonce: [u8; 32],
    quote_commitment: [u8; 32],
}

impl VerifiedSolverQuote {
    pub fn zero_kkt(&self) -> &VerifiedZeroKktQpCertificate {
        &self.zero_kkt
    }
    pub fn tee_evidence_digest(&self) -> [u8; 32] {
        self.tee_evidence_digest
    }
    pub fn quote_nonce(&self) -> [u8; 32] {
        self.quote_nonce
    }
    pub fn quote_commitment(&self) -> [u8; 32] {
        self.quote_commitment
    }
}

/// Verify an externally supplied `FHQPB001` wire artifact against an independently authorized
/// [`ExactQpProblem`]. Enforces `FHSDD001` PSD admission, entry-for-entry Matrix-Pin, exact
/// checked KKT residuals, and complete `(P, q, A, l, u)` problem binding.
pub fn verify_certified_qp(
    problem: &ExactQpProblem,
    wire: &[u8],
) -> Result<VerifiedExactQpCertificate, ExactQpCertificateBundleError> {
    let bundle = ExactQpCertificateBundle::from_wire_bytes(wire)?;
    let report = bundle.verify()?;
    bundle.kkt.verify_problem_binding(problem)?;
    let program_digest = bundle.kkt.program_digest();
    let mut wire_checksum = [0u8; 32];
    wire_checksum.copy_from_slice(&wire[wire.len() - CHECKSUM_LEN..]);
    Ok(VerifiedExactQpCertificate {
        bundle,
        program_digest,
        wire_checksum,
        report,
    })
}

/// Strict zero-tolerance KKT verification (`epsilon == 0`, `prim == dual == normal == 0`),
/// plus exact rational objective recomputation.
pub fn verify_zero_kkt_certified_qp(
    problem: &ExactQpProblem,
    wire: &[u8],
) -> Result<VerifiedZeroKktQpCertificate, ExactQpCertificateBundleError> {
    let certified = verify_certified_qp(problem, wire)?;
    if certified.bundle.kkt.epsilon != 0 {
        return Err(ExactQpCertificateBundleError::NonZeroTolerance {
            epsilon: certified.bundle.kkt.epsilon,
        });
    }
    let r = &certified.report;
    if r.prim_res != Some(0)
        || r.dual_res != Some(0)
        || r.normal_res != Some(0)
        || r.tol != Some(0)
        || !r.valid
    {
        return Err(ExactQpCertificateBundleError::NonZeroResidual);
    }
    let objective = compute_exact_objective(&certified.bundle.kkt)
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
    Ok(VerifiedZeroKktQpCertificate {
        certified,
        objective,
    })
}

/// Compute the canonical commitment expected in `tee.report_data()[0..32]` for an attested
/// `FHQPB001` off-chain solver quote.
pub fn solver_quote_commitment(
    program_digest: &[u8; 32],
    wire_checksum: &[u8; 32],
    quote_nonce: &[u8; 32],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"OBEND.FHQPB001.QUOTE/v1");
    h.update(program_digest);
    h.update(wire_checksum);
    h.update(quote_nonce);
    h.finalize()
}

/// Verify an attested off-chain solver quote: checks exact-zero `FHQPB001` (with Matrix-Pin +
/// full public problem binding) AND binds its commitment to `tee.report_data()[0..32]`.
pub fn verify_attested_solver_quote(
    tee: &VerifiedTeeEvidence,
    problem: &ExactQpProblem,
    wire: &[u8],
    quote_nonce: &[u8; 32],
) -> Result<VerifiedSolverQuote, ExactQpCertificateBundleError> {
    // Refuse GPU SPDM tokens: on NVIDIA GPUs `report_data[0..32]` is the requester's SPDM nonce,
    // not an enclave-computed solver commitment. Require a CPU TEE enclave.
    if matches!(tee.vendor(), crate::tee::TeeVendor::NvidiaGpu(_)) {
        return Err(ExactQpCertificateBundleError::QuoteAttestationMismatch);
    }
    let zero_kkt = verify_zero_kkt_certified_qp(problem, wire)?;
    let quote_commitment = solver_quote_commitment(
        &zero_kkt.program_digest(),
        &zero_kkt.certified().wire_checksum(),
        quote_nonce,
    );
    if !ct_eq(&tee.report_data_32(), &quote_commitment) {
        return Err(ExactQpCertificateBundleError::QuoteAttestationMismatch);
    }
    Ok(VerifiedSolverQuote {
        zero_kkt,
        tee_evidence_digest: tee.evidence_digest(),
        quote_nonce: *quote_nonce,
        quote_commitment,
    })
}

// ---------------------------------------------------------------------------
// Internal Serialization & Checksum Helpers
// ---------------------------------------------------------------------------

fn domain_checksum(domain: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(&(domain.len() as u64).to_be_bytes());
    h.update(domain);
    h.update(&(payload.len() as u64).to_be_bytes());
    h.update(payload);
    h.finalize()
}

#[allow(clippy::too_many_arguments)]
fn compute_qp_program_digest(
    n: usize,
    mc: usize,
    scale: u32,
    p: &[i128],
    q: &[i128],
    a: &[i128],
    l: &[i128],
    u: &[i128],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(&(FHQPB001_PROGRAM_DIGEST_DOMAIN.len() as u64).to_be_bytes());
    h.update(FHQPB001_PROGRAM_DIGEST_DOMAIN);
    h.update(&(n as u64).to_be_bytes());
    h.update(&(mc as u64).to_be_bytes());
    h.update(&scale.to_be_bytes());
    for slice in [p, q, a, l, u] {
        h.update(&(slice.len() as u64).to_be_bytes());
        for &v in slice {
            h.update(&v.to_be_bytes());
        }
    }
    h.finalize()
}

fn push_i128s(out: &mut Vec<u8>, values: &[i128]) {
    for &v in values {
        out.extend_from_slice(&v.to_be_bytes());
    }
}

fn exact_qp_wire_len(
    n: usize,
    mc: usize,
    admission_len: usize,
) -> Result<usize, ExactQpCertificateBundleError> {
    if n == 0 || n > MAX_QP_BUNDLE_DIMENSION || mc > MAX_QP_BUNDLE_DIMENSION {
        return Err(ExactQpCertificateBundleError::DimensionTooLarge { n, mc });
    }
    let nn = n
        .checked_mul(n)
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
    let mn = mc
        .checked_mul(n)
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
    let values = nn
        .checked_add(n)
        .and_then(|v| v.checked_add(mn))
        .and_then(|v| v.checked_add(mc.checked_mul(2)?))
        .and_then(|v| v.checked_add(n))
        .and_then(|v| v.checked_add(mc))
        .and_then(|v| v.checked_add(1))
        .ok_or(ExactQpCertificateBundleError::ArithmeticOverflow)?;
    FHQPB001_HEADER_LEN
        .checked_add(admission_len)
        .and_then(|v| v.checked_add(values.checked_mul(16)?))
        .and_then(|v| v.checked_add(CHECKSUM_LEN))
        .filter(|&len| len <= MAX_QP_BUNDLE_WIRE_BYTES)
        .ok_or(ExactQpCertificateBundleError::WireTooLarge {
            actual: usize::MAX,
            maximum: MAX_QP_BUNDLE_WIRE_BYTES,
        })
}

struct ByteCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ByteCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take_slice(N)?.try_into().ok()
    }

    fn take_slice(&mut self, len: usize) -> Option<&'a [u8]> {
        let end = self.offset.checked_add(len)?;
        if end > self.bytes.len() {
            return None;
        }
        let s = &self.bytes[self.offset..end];
        self.offset = end;
        Some(s)
    }

    fn take_i128s(&mut self, len: usize) -> Option<Vec<i128>> {
        let mut out = Vec::with_capacity(len);
        for _ in 0..len {
            out.push(i128::from_be_bytes(self.take::<16>()?));
        }
        Some(out)
    }

    fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
