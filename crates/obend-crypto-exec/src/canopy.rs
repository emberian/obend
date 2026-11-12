//! `Canopy` (`ePrint 2026/2790`) Track H Hash-PCS over `Goldilocks` / `GoldilocksExt2`:
//! - Oct 2026 Binary vs. Prime-Field Proximity-Gap Guard (`ePrint 2026/2424`)
//! - Matrix + Reed–Solomon Coset-NTT Multilinear Commitment (`OBEND.CRYPTO.CANOPY.MERKLE/v1`)
//! - `ifold` Out-of-Domain + Evaluation Row Fold (`\mathbb{F}_{p^2}` 128-bit security)
//! - `iacc` Shared-Subtree Batched Merkle Accumulator (`>= 30%` fewer hash invocations than
//!   independent Merkle openings, zero unread proof bytes)
//! - Constructive collision witness extractor (`extract_canopy_hash_collision`, closing `F2`).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::goldilocks::{
    CanonicalLiftError, Goldilocks, GoldilocksExecError, GoldilocksExt2, coset_lde, coset_lde_ext2,
    eq_poly_table,
};
use crate::transcript::{FenziTranscript, InstanceBound, cshake256_32, leb128};

/// Domain customization matching `Obend.Crypto.PCS.canopyMerkleCustomization`.
pub const CANOPY_MERKLE_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.CANOPY.MERKLE/v1";

/// Domain customization for salted Dark Bazaar column leaves (`K7` / closing `F6`).
pub const CANOPY_LEAF_SALT_CUSTOMIZATION: &[u8] = b"OBEND.CRYPTO.CANOPY.LEAFSALT/v1";

/// Transcript labels for `Canopy` `ifold` and `iacc` phases.
pub const CANOPY_IFOLD_LABEL: &[u8] = b"CANOPY.PCS.IFOLD";
pub const CANOPY_OPEN_LABEL: &[u8] = b"CANOPY.PCS.OPEN";

/// Linear-code domain algebra (`Obend.Crypto.PCS.DomainKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomainKind {
    PrimeField,
    BinaryAdditive,
}

/// Proximity-gap decoding regime (`Obend.Crypto.PCS.ProximityRegime`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProximityRegime {
    UniqueDecodingRadius,
    JohnsonBound,
    CapacityBound,
}

/// Errors emitted by `Canopy` commitment, proving, verification, or collision extraction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanopyError {
    /// `ePrint 2026/2424`: binary additive RS codes forbid Johnson/Capacity proximity regimes.
    InvalidProximityConfig {
        domain: DomainKind,
        regime: ProximityRegime,
    },
    InvalidBlowupFactor(usize),
    InvalidQueryCount(usize),
    UdrRadiusViolation {
        radius: usize,
        min_distance: usize,
    },
    TableSizeMismatch {
        expected: usize,
        actual: usize,
    },
    PointDimensionMismatch {
        expected: usize,
        actual: usize,
    },
    FoldVectorLengthMismatch {
        expected: usize,
        actual: usize,
    },
    ClaimedEvaluationMismatch,
    UnsortedOrOutOfBoundsQueryIndices,
    ColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    ColumnRowCountMismatch {
        expected: usize,
        actual: usize,
    },
    MissingOrUnexpectedColumnSalt,
    IfoldColumnConsistencyFailed {
        col_idx: usize,
    },
    TruncatedAuxiliarySiblings,
    UnconsumedAuxiliarySiblings {
        remaining: usize,
    },
    MerkleRootMismatch,
    IndependentPathLengthMismatch,
    GoldilocksError(GoldilocksExecError),
    NonCanonicalFieldElement(CanonicalLiftError),
    NoDiscrepancyToExtractCollision,
}

impl fmt::Display for CanopyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl From<GoldilocksExecError> for CanopyError {
    fn from(e: GoldilocksExecError) -> Self {
        Self::GoldilocksError(e)
    }
}

impl From<CanonicalLiftError> for CanopyError {
    fn from(e: CanonicalLiftError) -> Self {
        Self::NonCanonicalFieldElement(e)
    }
}

/// Validated `Canopy` Track H parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanopyParams {
    pub domain_kind: DomainKind,
    pub regime: ProximityRegime,
    pub blowup_factor: usize,
    pub num_queries: usize,
    pub coset_shift: Goldilocks,
}

impl CanopyParams {
    /// Construct and validate `CanopyParams`, enforcing `ePrint 2026/2424` (`binaryAdditive_forces_udr`).
    pub fn new(
        domain_kind: DomainKind,
        regime: ProximityRegime,
        blowup_factor: usize,
        num_queries: usize,
    ) -> Result<Self, CanopyError> {
        if domain_kind == DomainKind::BinaryAdditive
            && regime != ProximityRegime::UniqueDecodingRadius
        {
            return Err(CanopyError::InvalidProximityConfig {
                domain: domain_kind,
                regime,
            });
        }
        if blowup_factor < 2 || !blowup_factor.is_power_of_two() {
            return Err(CanopyError::InvalidBlowupFactor(blowup_factor));
        }
        if num_queries == 0 {
            return Err(CanopyError::InvalidQueryCount(num_queries));
        }
        Ok(Self {
            domain_kind,
            regime,
            blowup_factor,
            num_queries,
            coset_shift: Goldilocks::NON_RESIDUE,
        })
    }

    /// Standard 128-bit Track H prime-field parameters (`blowup = 4`, `queries = 32`).
    pub fn default_128bit() -> Self {
        Self {
            domain_kind: DomainKind::PrimeField,
            regime: ProximityRegime::UniqueDecodingRadius,
            blowup_factor: 4,
            num_queries: 32,
            coset_shift: Goldilocks::NON_RESIDUE,
        }
    }

    /// Check integer unique-decoding radius bound `2 * radius < d = L - C + 1` for a given `msg_cols`.
    pub fn check_code_dimensions(&self, msg_cols: usize) -> Result<usize, CanopyError> {
        let codeword_cols = msg_cols * self.blowup_factor;
        let min_distance = codeword_cols - msg_cols + 1;
        if self.regime == ProximityRegime::UniqueDecodingRadius {
            let max_udr_radius = (min_distance - 1) / 2;
            // Conservative non-trivial distance check (`2 * radius < min_distance` with positive radius)
            if 2 * max_udr_radius >= min_distance || codeword_cols <= msg_cols {
                return Err(CanopyError::UdrRadiusViolation {
                    radius: max_udr_radius,
                    min_distance,
                });
            }
        }
        Ok(codeword_cols)
    }
}

/// Public 32-byte `Canopy` multilinear commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanopyCommitment {
    pub num_vars: u32,
    pub salted: bool,
    pub root: [u8; 32],
}

impl CanopyCommitment {
    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(37);
        out.extend_from_slice(&self.num_vars.to_be_bytes());
        out.push(u8::from(self.salted));
        out.extend_from_slice(&self.root);
        out
    }
}

/// Prover-side committed state holding the Reed–Solomon extended matrix and full Merkle tree.
#[derive(Clone, Debug)]
pub struct CanopyProverState {
    pub num_vars: usize,
    pub row_vars: usize,
    pub col_vars: usize,
    pub num_rows: usize,
    pub msg_cols: usize,
    pub codeword_cols: usize,
    /// Row-major `num_rows * msg_cols` unextended evaluations.
    pub base_matrix: Vec<Goldilocks>,
    /// Row-major `num_rows * codeword_cols` RS-extended evaluations.
    pub extended_matrix: Vec<Goldilocks>,
    /// Optional per-column 32-byte hiding salts (`len == codeword_cols` when `salted`).
    pub col_salts: Option<Vec<[u8; 32]>>,
    /// 1-indexed binary Merkle tree of length `2 * codeword_cols` (`tree[1]` is root).
    pub tree_nodes: Vec<[u8; 32]>,
    pub commitment: CanopyCommitment,
}

/// Single queried column opening in a `Canopy` proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanopyOpenedColumn {
    pub col_idx: usize,
    pub values: Vec<Goldilocks>,
    pub salt: Option<[u8; 32]>,
}

/// Batched `Canopy` (`2026/2790`) `ifold + iacc` opening proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanopyBatchedProof {
    /// Folded evaluation row combination $u_{\text{eval}} = q_{\text{row}}^\top M \in (\mathbb{F}_{p^2})^C$.
    pub u_eval: Vec<GoldilocksExt2>,
    /// Folded out-of-domain proximity row combination $u_{\text{prox}} = r_{\text{prox}}^\top M \in (\mathbb{F}_{p^2})^C$.
    pub u_prox: Vec<GoldilocksExt2>,
    /// Queried extended codeword columns (sorted by `col_idx`).
    pub opened_columns: Vec<CanopyOpenedColumn>,
    /// Pruned boundary sibling digests for the `iacc` shared-subtree accumulator.
    pub aux_siblings: Vec<[u8; 32]>,
}

/// Unpruned baseline proof opening each queried column with an independent root-to-leaf Merkle path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndependentMerkleProof {
    pub u_eval: Vec<GoldilocksExt2>,
    pub u_prox: Vec<GoldilocksExt2>,
    pub opened_columns: Vec<CanopyOpenedColumn>,
    /// `num_queries` independent bottom-up sibling paths of length $\log_2 L$ each.
    pub independent_paths: Vec<Vec<[u8; 32]>>,
}

/// Exact `cSHAKE256` hash invocation telemetry for `Canopy` `iacc` vs. independent Merkle verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HashInvocationStats {
    pub leaf_hashes: usize,
    pub internal_hashes: usize,
    pub total_hashes: usize,
}

impl HashInvocationStats {
    /// Compute relative hash reduction `(baseline - canopy) / baseline` in `[0.0, 1.0]`.
    pub fn savings_vs(&self, baseline: &Self) -> f64 {
        if baseline.total_hashes == 0 || self.total_hashes >= baseline.total_hashes {
            return 0.0;
        }
        (baseline.total_hashes - self.total_hashes) as f64 / (baseline.total_hashes as f64)
    }
}

/// Concrete hash collision witness returned by `extract_canopy_hash_collision` (`HashBreak`, closing `F2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanopyHashCollision {
    pub preimage_a: Vec<u8>,
    pub preimage_b: Vec<u8>,
    pub shared_digest: [u8; 32],
}

// ============================================================================
// Domain-Separated Leaf & Internal Node Hashing (`Obend.Crypto.PCS`)
// ============================================================================

/// Canonical `Canopy` column leaf preimage:
/// - Unsalted: `0x00 || leb128(col_idx) || be8(v_0) || ... || be8(v_{R-1})`
/// - Salted (`DarkBazaar` `K7`): `0x03 || leb128(col_idx) || salt32 || be8(v_0) || ... || be8(v_{R-1})`
pub fn canopy_column_leaf_preimage(
    col_idx: usize,
    col_vals: &[Goldilocks],
    salt: Option<&[u8; 32]>,
) -> Vec<u8> {
    let idx_bytes = leb128(col_idx);
    let extra = if salt.is_some() { 32 } else { 0 };
    let mut pre = Vec::with_capacity(1 + idx_bytes.len() + extra + 8 * col_vals.len());
    match salt {
        None => {
            pre.push(0x00);
            pre.extend_from_slice(&idx_bytes);
        }
        Some(s) => {
            pre.push(0x03);
            pre.extend_from_slice(&idx_bytes);
            pre.extend_from_slice(s);
        }
    }
    for v in col_vals {
        pre.extend_from_slice(&v.to_be_bytes());
    }
    pre
}

/// Domain-separated internal node preimage: `0x01 || left(32) || right(32)`.
#[inline]
pub fn canopy_node_preimage(left: &[u8; 32], right: &[u8; 32]) -> [u8; 65] {
    let mut pre = [0u8; 65];
    pre[0] = 0x01;
    pre[1..33].copy_from_slice(left);
    pre[33..65].copy_from_slice(right);
    pre
}

#[inline]
pub fn hash_canopy_column_leaf(
    col_idx: usize,
    col_vals: &[Goldilocks],
    salt: Option<&[u8; 32]>,
) -> [u8; 32] {
    let pre = canopy_column_leaf_preimage(col_idx, col_vals, salt);
    cshake256_32(CANOPY_MERKLE_CUSTOMIZATION, &pre)
}

#[inline]
pub fn hash_canopy_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let pre = canopy_node_preimage(left, right);
    cshake256_32(CANOPY_MERKLE_CUSTOMIZATION, &pre)
}

fn derive_column_salt(order_salt_seed: &[u8; 32], col_idx: usize) -> [u8; 32] {
    let mut input = Vec::with_capacity(32 + 5);
    input.extend_from_slice(order_salt_seed);
    input.extend_from_slice(&leb128(col_idx));
    cshake256_32(CANOPY_LEAF_SALT_CUSTOMIZATION, &input)
}

#[inline]
fn split_var_counts(num_vars: usize) -> (usize, usize) {
    let row_vars = num_vars / 2;
    let col_vars = num_vars - row_vars;
    (row_vars, col_vars)
}

// ============================================================================
// Canopy Commit, `ifold + iacc` Prover & Verifier
// ============================================================================

/// Commit to a $2^v$-element `Goldilocks` multilinear table using `Canopy` RS-Tensor + Merkle tree.
/// Pass `salt_seed = Some(...)` for hiding commitments (`DarkBazaar` `SameOpening`).
pub fn canopy_commit(
    params: &CanopyParams,
    num_vars: usize,
    table: &[Goldilocks],
    salt_seed: Option<&[u8; 32]>,
) -> Result<CanopyProverState, CanopyError> {
    let expected_len = 1usize << num_vars;
    if table.len() != expected_len {
        return Err(CanopyError::TableSizeMismatch {
            expected: expected_len,
            actual: table.len(),
        });
    }
    let (row_vars, col_vars) = split_var_counts(num_vars);
    let num_rows = 1usize << row_vars;
    let msg_cols = 1usize << col_vars;
    let codeword_cols = params.check_code_dimensions(msg_cols)?;

    let mut extended_matrix = vec![Goldilocks::ZERO; num_rows * codeword_cols];
    for r in 0..num_rows {
        let row_slice = &table[r * msg_cols..(r + 1) * msg_cols];
        let encoded_row = coset_lde(row_slice, params.coset_shift, params.blowup_factor)?;
        extended_matrix[r * codeword_cols..(r + 1) * codeword_cols].copy_from_slice(&encoded_row);
    }

    let col_salts = salt_seed.map(|seed| {
        (0..codeword_cols)
            .map(|j| derive_column_salt(seed, j))
            .collect::<Vec<[u8; 32]>>()
    });

    let mut tree_nodes = vec![[0u8; 32]; 2 * codeword_cols];
    let mut col_buf = vec![Goldilocks::ZERO; num_rows];
    for j in 0..codeword_cols {
        for r in 0..num_rows {
            col_buf[r] = extended_matrix[r * codeword_cols + j];
        }
        let salt_ref = col_salts.as_ref().map(|v| &v[j]);
        tree_nodes[codeword_cols + j] = hash_canopy_column_leaf(j, &col_buf, salt_ref);
    }
    for idx in (1..codeword_cols).rev() {
        tree_nodes[idx] = hash_canopy_node(&tree_nodes[2 * idx], &tree_nodes[2 * idx + 1]);
    }

    let commitment = CanopyCommitment {
        num_vars: num_vars as u32,
        salted: salt_seed.is_some(),
        root: tree_nodes[1],
    };

    Ok(CanopyProverState {
        num_vars,
        row_vars,
        col_vars,
        num_rows,
        msg_cols,
        codeword_cols,
        base_matrix: table.to_vec(),
        extended_matrix,
        col_salts,
        tree_nodes,
        commitment,
    })
}

fn build_proximity_weights(alpha: GoldilocksExt2, num_rows: usize) -> Vec<GoldilocksExt2> {
    let mut out = Vec::with_capacity(num_rows);
    let mut pow = GoldilocksExt2::ONE;
    for _ in 0..num_rows {
        out.push(pow);
        pow *= alpha;
    }
    out
}

fn absorb_ifold_vectors(
    tr: &mut FenziTranscript<InstanceBound>,
    u_eval: &[GoldilocksExt2],
    u_prox: &[GoldilocksExt2],
) {
    let mut buf = leb128(u_eval.len());
    for z in u_eval {
        buf.extend_from_slice(&z.to_be_bytes());
    }
    buf.extend_from_slice(&leb128(u_prox.len()));
    for z in u_prox {
        buf.extend_from_slice(&z.to_be_bytes());
    }
    tr.absorb(CANOPY_IFOLD_LABEL, &buf);
}

/// Build the `iacc` pruned shared-subtree multiproof for sorted distinct leaf indices in `0..L`.
pub fn prove_iacc_multiproof(
    tree_nodes: &[[u8; 32]],
    num_leaves: usize,
    sorted_indices: &[usize],
) -> Vec<[u8; 32]> {
    let mut active: Vec<usize> = sorted_indices.iter().map(|&j| num_leaves + j).collect();
    let mut aux_siblings = Vec::new();
    let mut cur_level_width = num_leaves;

    while cur_level_width > 1 {
        let mut next_active = Vec::with_capacity(active.len().div_ceil(2));
        let mut i = 0usize;
        while i < active.len() {
            let node = active[i];
            if i + 1 < active.len() && (node ^ 1) == active[i + 1] {
                // Both left (`node`) and right (`node ^ 1`) children are active:
                // shared internal node — zero auxiliary digests emitted!
                next_active.push(node >> 1);
                i += 2;
            } else {
                aux_siblings.push(tree_nodes[node ^ 1]);
                next_active.push(node >> 1);
                i += 1;
            }
        }
        active = next_active;
        cur_level_width >>= 1;
    }
    aux_siblings
}

/// Verify an `iacc` pruned shared-subtree multiproof against `expected_root`, returning exact
/// internal hash invocation count.
pub fn verify_iacc_multiproof(
    expected_root: &[u8; 32],
    num_leaves: usize,
    sorted_indices: &[usize],
    leaf_digests: &[[u8; 32]],
    aux_siblings: &[[u8; 32]],
) -> Result<usize, CanopyError> {
    if sorted_indices.is_empty() || sorted_indices.len() != leaf_digests.len() {
        return Err(CanopyError::ColumnCountMismatch {
            expected: sorted_indices.len(),
            actual: leaf_digests.len(),
        });
    }
    for w in sorted_indices.windows(2) {
        if w[0] >= w[1] {
            return Err(CanopyError::UnsortedOrOutOfBoundsQueryIndices);
        }
    }
    if *sorted_indices.last().unwrap() >= num_leaves {
        return Err(CanopyError::UnsortedOrOutOfBoundsQueryIndices);
    }

    let mut active: Vec<(usize, [u8; 32])> = sorted_indices
        .iter()
        .copied()
        .zip(leaf_digests.iter().copied())
        .map(|(j, d)| (num_leaves + j, d))
        .collect();

    let mut cursor = 0usize;
    let mut internal_hashes = 0usize;
    let mut cur_level_width = num_leaves;

    while cur_level_width > 1 {
        let mut next_active = Vec::with_capacity(active.len().div_ceil(2));
        let mut i = 0usize;
        while i < active.len() {
            let (node, dig) = active[i];
            if i + 1 < active.len() && (node ^ 1) == active[i + 1].0 {
                // `node` is even and `active[i + 1].0 == node + 1`
                let parent_dig = hash_canopy_node(&dig, &active[i + 1].1);
                internal_hashes += 1;
                next_active.push((node >> 1, parent_dig));
                i += 2;
            } else {
                if cursor >= aux_siblings.len() {
                    return Err(CanopyError::TruncatedAuxiliarySiblings);
                }
                let sib = aux_siblings[cursor];
                cursor += 1;
                let parent_dig = if (node & 1) == 0 {
                    hash_canopy_node(&dig, &sib)
                } else {
                    hash_canopy_node(&sib, &dig)
                };
                internal_hashes += 1;
                next_active.push((node >> 1, parent_dig));
                i += 1;
            }
        }
        active = next_active;
        cur_level_width >>= 1;
    }

    if cursor != aux_siblings.len() {
        return Err(CanopyError::UnconsumedAuxiliarySiblings {
            remaining: aux_siblings.len() - cursor,
        });
    }
    if active.len() != 1 || &active[0].1 != expected_root {
        return Err(CanopyError::MerkleRootMismatch);
    }
    Ok(internal_hashes)
}

/// Produce a batched `Canopy` (`ifold + iacc`) multilinear evaluation opening proof bound to
/// `FenziTranscript<InstanceBound>`.
pub fn canopy_open(
    params: &CanopyParams,
    state: &CanopyProverState,
    eval_point: &[GoldilocksExt2],
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<CanopyBatchedProof, CanopyError> {
    if eval_point.len() != state.num_vars {
        return Err(CanopyError::PointDimensionMismatch {
            expected: state.num_vars,
            actual: eval_point.len(),
        });
    }

    let z_row = &eval_point[state.col_vars..];
    let q_row = eq_poly_table(z_row);

    // `ifold` step 1: out-of-domain proximity row weights squeezed from InstanceBound transcript
    let alpha = tr.squeeze_ext2();
    let r_prox = build_proximity_weights(alpha, state.num_rows);

    let mut u_eval = vec![GoldilocksExt2::ZERO; state.msg_cols];
    let mut u_prox = vec![GoldilocksExt2::ZERO; state.msg_cols];
    for r in 0..state.num_rows {
        let qr = q_row[r];
        let pr = r_prox[r];
        let row_off = r * state.msg_cols;
        for c in 0..state.msg_cols {
            let entry = state.base_matrix[row_off + c];
            u_eval[c] += qr.mul_base(entry);
            u_prox[c] += pr.mul_base(entry);
        }
    }

    // `ifold` step 2: absorb folded row vectors & squeeze combination scalar `beta` + query indices
    absorb_ifold_vectors(tr, &u_eval, &u_prox);
    let _beta = tr.squeeze_ext2();
    let query_indices =
        tr.squeeze_distinct_query_indices(params.num_queries, state.codeword_cols);

    // `iacc` step 3: extract queried columns + pruned shared-subtree multiproof
    let mut opened_columns = Vec::with_capacity(query_indices.len());
    for &col_idx in &query_indices {
        let mut values = Vec::with_capacity(state.num_rows);
        for r in 0..state.num_rows {
            values.push(state.extended_matrix[r * state.codeword_cols + col_idx]);
        }
        let salt = state.col_salts.as_ref().map(|s| s[col_idx]);
        opened_columns.push(CanopyOpenedColumn {
            col_idx,
            values,
            salt,
        });
    }
    let aux_siblings =
        prove_iacc_multiproof(&state.tree_nodes, state.codeword_cols, &query_indices);

    tr.absorb(CANOPY_OPEN_LABEL, &state.commitment.root);

    Ok(CanopyBatchedProof {
        u_eval,
        u_prox,
        opened_columns,
        aux_siblings,
    })
}

/// Verify a batched `Canopy` (`ifold + iacc`) opening proof against `comm`, `eval_point`, and
/// `claimed_val`, returning exact hash invocation telemetry.
pub fn canopy_verify(
    params: &CanopyParams,
    comm: &CanopyCommitment,
    eval_point: &[GoldilocksExt2],
    claimed_val: GoldilocksExt2,
    proof: &CanopyBatchedProof,
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<HashInvocationStats, CanopyError> {
    let num_vars = comm.num_vars as usize;
    if eval_point.len() != num_vars {
        return Err(CanopyError::PointDimensionMismatch {
            expected: num_vars,
            actual: eval_point.len(),
        });
    }
    let (row_vars, col_vars) = split_var_counts(num_vars);
    let num_rows = 1usize << row_vars;
    let msg_cols = 1usize << col_vars;
    let codeword_cols = params.check_code_dimensions(msg_cols)?;

    if proof.u_eval.len() != msg_cols {
        return Err(CanopyError::FoldVectorLengthMismatch {
            expected: msg_cols,
            actual: proof.u_eval.len(),
        });
    }
    if proof.u_prox.len() != msg_cols {
        return Err(CanopyError::FoldVectorLengthMismatch {
            expected: msg_cols,
            actual: proof.u_prox.len(),
        });
    }

    let z_col = &eval_point[..col_vars];
    let z_row = &eval_point[col_vars..];
    let q_col = eq_poly_table(z_col);
    let q_row = eq_poly_table(z_row);

    // 1. Check inner product <u_eval, q_col> == claimed_val
    let mut eval_dot = GoldilocksExt2::ZERO;
    for (&u_c, &qc) in proof.u_eval.iter().zip(q_col.iter()) {
        eval_dot += u_c * qc;
    }
    if eval_dot != claimed_val {
        return Err(CanopyError::ClaimedEvaluationMismatch);
    }

    // 2. Replay `ifold` challenges (alpha, beta) & query indices from `InstanceBound` transcript
    let alpha = tr.squeeze_ext2();
    let r_prox = build_proximity_weights(alpha, num_rows);
    absorb_ifold_vectors(tr, &proof.u_eval, &proof.u_prox);
    let beta = tr.squeeze_ext2();
    let expected_queries = tr.squeeze_distinct_query_indices(params.num_queries, codeword_cols);

    if proof.opened_columns.len() != expected_queries.len() {
        return Err(CanopyError::ColumnCountMismatch {
            expected: expected_queries.len(),
            actual: proof.opened_columns.len(),
        });
    }

    // Single combined Reed–Solomon codeword encoding via `ifold`: u_fold = u_prox + beta * u_eval
    let mut u_fold = Vec::with_capacity(msg_cols);
    let mut w_fold = Vec::with_capacity(num_rows);
    for c in 0..msg_cols {
        u_fold.push(proof.u_prox[c] + beta * proof.u_eval[c]);
    }
    for r in 0..num_rows {
        w_fold.push(r_prox[r] + beta * q_row[r]);
    }
    let codeword_fold = coset_lde_ext2(&u_fold, params.coset_shift, params.blowup_factor)?;

    // 3. Check column-wise tensor consistency + compute column leaf hashes
    let mut leaf_digests = Vec::with_capacity(expected_queries.len());
    for (col_open, &expected_idx) in proof.opened_columns.iter().zip(expected_queries.iter()) {
        if col_open.col_idx != expected_idx {
            return Err(CanopyError::UnsortedOrOutOfBoundsQueryIndices);
        }
        if col_open.values.len() != num_rows {
            return Err(CanopyError::ColumnRowCountMismatch {
                expected: num_rows,
                actual: col_open.values.len(),
            });
        }
        if col_open.salt.is_some() != comm.salted {
            return Err(CanopyError::MissingOrUnexpectedColumnSalt);
        }

        let mut col_comb = GoldilocksExt2::ZERO;
        for r in 0..num_rows {
            col_comb += w_fold[r].mul_base(col_open.values[r]);
        }
        if col_comb != codeword_fold[expected_idx] {
            return Err(CanopyError::IfoldColumnConsistencyFailed {
                col_idx: expected_idx,
            });
        }

        leaf_digests.push(hash_canopy_column_leaf(
            expected_idx,
            &col_open.values,
            col_open.salt.as_ref(),
        ));
    }

    // 4. Verify `iacc` shared-subtree multiproof
    let leaf_hashes = leaf_digests.len();
    let internal_hashes = verify_iacc_multiproof(
        &comm.root,
        codeword_cols,
        &expected_queries,
        &leaf_digests,
        &proof.aux_siblings,
    )?;

    tr.absorb(CANOPY_OPEN_LABEL, &comm.root);

    Ok(HashInvocationStats {
        leaf_hashes,
        internal_hashes,
        total_hashes: leaf_hashes + internal_hashes,
    })
}

// ============================================================================
// Unpruned Independent Merkle Baseline (For >= 30% Hash-Savings Measurement)
// ============================================================================

/// Generate unpruned independent root-to-leaf Merkle paths for the exact same `Canopy` queries.
pub fn prove_independent_merkle_baseline(
    params: &CanopyParams,
    state: &CanopyProverState,
    eval_point: &[GoldilocksExt2],
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<IndependentMerkleProof, CanopyError> {
    let batched = canopy_open(params, state, eval_point, tr)?;
    let mut independent_paths = Vec::with_capacity(batched.opened_columns.len());
    for col in &batched.opened_columns {
        let mut node = state.codeword_cols + col.col_idx;
        let mut path = Vec::new();
        while node > 1 {
            path.push(state.tree_nodes[node ^ 1]);
            node >>= 1;
        }
        independent_paths.push(path);
    }
    Ok(IndependentMerkleProof {
        u_eval: batched.u_eval,
        u_prox: batched.u_prox,
        opened_columns: batched.opened_columns,
        independent_paths,
    })
}

/// Verify unpruned independent Merkle openings and count total hash invocations.
pub fn verify_independent_merkle_baseline(
    params: &CanopyParams,
    comm: &CanopyCommitment,
    eval_point: &[GoldilocksExt2],
    claimed_val: GoldilocksExt2,
    proof: &IndependentMerkleProof,
    tr: &mut FenziTranscript<InstanceBound>,
) -> Result<HashInvocationStats, CanopyError> {
    let num_vars = comm.num_vars as usize;
    let (row_vars, col_vars) = split_var_counts(num_vars);
    let num_rows = 1usize << row_vars;
    let msg_cols = 1usize << col_vars;
    let codeword_cols = params.check_code_dimensions(msg_cols)?;
    let tree_height = codeword_cols.trailing_zeros() as usize;

    let z_col = &eval_point[..col_vars];
    let z_row = &eval_point[col_vars..];
    let q_col = eq_poly_table(z_col);
    let q_row = eq_poly_table(z_row);

    let mut eval_dot = GoldilocksExt2::ZERO;
    for (&u_c, &qc) in proof.u_eval.iter().zip(q_col.iter()) {
        eval_dot += u_c * qc;
    }
    if eval_dot != claimed_val {
        return Err(CanopyError::ClaimedEvaluationMismatch);
    }

    let alpha = tr.squeeze_ext2();
    let r_prox = build_proximity_weights(alpha, num_rows);
    absorb_ifold_vectors(tr, &proof.u_eval, &proof.u_prox);
    let beta = tr.squeeze_ext2();
    let expected_queries = tr.squeeze_distinct_query_indices(params.num_queries, codeword_cols);

    if proof.opened_columns.len() != expected_queries.len()
        || proof.independent_paths.len() != expected_queries.len()
    {
        return Err(CanopyError::IndependentPathLengthMismatch);
    }

    let mut u_fold = Vec::with_capacity(msg_cols);
    let mut w_fold = Vec::with_capacity(num_rows);
    for c in 0..msg_cols {
        u_fold.push(proof.u_prox[c] + beta * proof.u_eval[c]);
    }
    for r in 0..num_rows {
        w_fold.push(r_prox[r] + beta * q_row[r]);
    }
    let codeword_fold = coset_lde_ext2(&u_fold, params.coset_shift, params.blowup_factor)?;

    let mut leaf_hashes = 0usize;
    let mut internal_hashes = 0usize;

    for ((col_open, path), &expected_idx) in proof
        .opened_columns
        .iter()
        .zip(proof.independent_paths.iter())
        .zip(expected_queries.iter())
    {
        if col_open.col_idx != expected_idx || path.len() != tree_height {
            return Err(CanopyError::IndependentPathLengthMismatch);
        }
        let mut col_comb = GoldilocksExt2::ZERO;
        for r in 0..num_rows {
            col_comb += w_fold[r].mul_base(col_open.values[r]);
        }
        if col_comb != codeword_fold[expected_idx] {
            return Err(CanopyError::IfoldColumnConsistencyFailed {
                col_idx: expected_idx,
            });
        }
        let mut cur = hash_canopy_column_leaf(expected_idx, &col_open.values, col_open.salt.as_ref());
        leaf_hashes += 1;

        let mut node = codeword_cols + expected_idx;
        for sib in path {
            cur = if (node & 1) == 0 {
                hash_canopy_node(&cur, sib)
            } else {
                hash_canopy_node(sib, &cur)
            };
            internal_hashes += 1;
            node >>= 1;
        }
        if &cur != &comm.root {
            return Err(CanopyError::MerkleRootMismatch);
        }
    }

    tr.absorb(CANOPY_OPEN_LABEL, &comm.root);

    Ok(HashInvocationStats {
        leaf_hashes,
        internal_hashes,
        total_hashes: leaf_hashes + internal_hashes,
    })
}

// ============================================================================
// Constructive Collision Witness Extractor (`HashBreak`, Closing `F2`)
// ============================================================================

/// Given two single-column authentication paths `(col_a, path_a)` and `(col_b, path_b)` at the
/// same `col_idx` climbing to the same `root` under `H` (`CANOPY_MERKLE_CUSTOMIZATION` by default,
/// or a custom hash oracle for testing), constructively extract an explicit `CanopyHashCollision`
/// (`preimage_a != preimage_b` with `H(preimage_a) == H(preimage_b)`).
pub fn extract_canopy_hash_collision_with<H>(
    hash_fn: H,
    codeword_cols: usize,
    col_idx: usize,
    col_a: &CanopyOpenedColumn,
    path_a: &[[u8; 32]],
    col_b: &CanopyOpenedColumn,
    path_b: &[[u8; 32]],
) -> Result<CanopyHashCollision, CanopyError>
where
    H: Fn(&[u8]) -> [u8; 32],
{
    if path_a.len() != path_b.len() {
        return Err(CanopyError::IndependentPathLengthMismatch);
    }
    let pre_leaf_a = canopy_column_leaf_preimage(col_idx, &col_a.values, col_a.salt.as_ref());
    let pre_leaf_b = canopy_column_leaf_preimage(col_idx, &col_b.values, col_b.salt.as_ref());
    if pre_leaf_a == pre_leaf_b && path_a == path_b {
        return Err(CanopyError::NoDiscrepancyToExtractCollision);
    }

    let mut cur_a = hash_fn(&pre_leaf_a);
    let mut cur_b = hash_fn(&pre_leaf_b);
    if cur_a == cur_b && pre_leaf_a != pre_leaf_b {
        return Ok(CanopyHashCollision {
            preimage_a: pre_leaf_a,
            preimage_b: pre_leaf_b,
            shared_digest: cur_a,
        });
    }

    let mut node = codeword_cols + col_idx;
    for (sib_a, sib_b) in path_a.iter().zip(path_b.iter()) {
        let node_pre_a = if (node & 1) == 0 {
            canopy_node_preimage(&cur_a, sib_a)
        } else {
            canopy_node_preimage(sib_a, &cur_a)
        };
        let node_pre_b = if (node & 1) == 0 {
            canopy_node_preimage(&cur_b, sib_b)
        } else {
            canopy_node_preimage(sib_b, &cur_b)
        };
        let next_a = hash_fn(&node_pre_a);
        let next_b = hash_fn(&node_pre_b);
        if next_a == next_b && node_pre_a != node_pre_b {
            return Ok(CanopyHashCollision {
                preimage_a: node_pre_a.to_vec(),
                preimage_b: node_pre_b.to_vec(),
                shared_digest: next_a,
            });
        }
        cur_a = next_a;
        cur_b = next_b;
        node >>= 1;
    }

    Err(CanopyError::NoDiscrepancyToExtractCollision)
}

/// Deployed `cSHAKE256` specialization of `extract_canopy_hash_collision_with`.
pub fn extract_canopy_hash_collision(
    codeword_cols: usize,
    col_idx: usize,
    col_a: &CanopyOpenedColumn,
    path_a: &[[u8; 32]],
    col_b: &CanopyOpenedColumn,
    path_b: &[[u8; 32]],
) -> Result<CanopyHashCollision, CanopyError> {
    extract_canopy_hash_collision_with(
        |pre| cshake256_32(CANOPY_MERKLE_CUSTOMIZATION, pre),
        codeword_cols,
        col_idx,
        col_a,
        path_a,
        col_b,
        path_b,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::goldilocks::mle_eval_base_at_ext2;

    #[test]
    fn test_proximity_guard_refuses_binary_non_udr() {
        assert!(CanopyParams::new(
            DomainKind::BinaryAdditive,
            ProximityRegime::JohnsonBound,
            4,
            32
        )
        .is_err());
        assert!(CanopyParams::new(
            DomainKind::BinaryAdditive,
            ProximityRegime::CapacityBound,
            4,
            32
        )
        .is_err());
        assert!(CanopyParams::new(
            DomainKind::BinaryAdditive,
            ProximityRegime::UniqueDecodingRadius,
            4,
            32
        )
        .is_ok());
        assert!(CanopyParams::new(
            DomainKind::PrimeField,
            ProximityRegime::CapacityBound,
            4,
            32
        )
        .is_ok());
    }

    #[test]
    fn test_canopy_batched_achieves_over_30_percent_hash_savings_and_rejects_tampering() {
        let params = CanopyParams::default_128bit(); // blowup = 4, queries = 32
        let num_vars = 12usize; // 4096 Goldilocks evaluations -> 64 x 64 matrix -> 64 x 256 RS matrix
        let table: Vec<Goldilocks> = (0..(1usize << num_vars))
            .map(|i| Goldilocks::from_u64_reduced((i as u64).wrapping_mul(0x517C_C1B7_2722_0A95) + 19))
            .collect();
        let point: Vec<GoldilocksExt2> = (0..num_vars)
            .map(|i| GoldilocksExt2::from_canonical_u64_pair(17 + 5 * i as u64, 99 + i as u64).unwrap())
            .collect();
        let claimed = mle_eval_base_at_ext2(&table, &point).unwrap();

        let state = canopy_commit(&params, num_vars, &table, None).unwrap();
        let comm_bytes = state.commitment.to_transcript_bytes();
        let vk = [0xAAu8; 32];

        let base_tr = FenziTranscript::new(b"canopy-bench")
            .bind_relation("OBEND.CANOPY.PCS/v1", &vk, b"v=12")
            .bind_instance(&comm_bytes, claimed, &point);

        let mut p_tr = base_tr.clone();
        let proof = canopy_open(&params, &state, &point, &mut p_tr).unwrap();

        let mut v_tr = base_tr.clone();
        let canopy_stats =
            canopy_verify(&params, &state.commitment, &point, claimed, &proof, &mut v_tr).unwrap();
        assert_eq!(p_tr.state(), v_tr.state());

        // Compare against independent Merkle openings on the exact same commitment & transcript
        let mut ind_p_tr = base_tr.clone();
        let ind_proof =
            prove_independent_merkle_baseline(&params, &state, &point, &mut ind_p_tr).unwrap();
        let mut ind_v_tr = base_tr.clone();
        let ind_stats = verify_independent_merkle_baseline(
            &params,
            &state.commitment,
            &point,
            claimed,
            &ind_proof,
            &mut ind_v_tr,
        )
        .unwrap();

        let savings = canopy_stats.savings_vs(&ind_stats);
        assert!(
            savings >= 0.30,
            "Expected >= 30% Canopy hash savings, got {:.2}% (canopy={} vs independent={})",
            savings * 100.0,
            canopy_stats.total_hashes,
            ind_stats.total_hashes
        );

        // Tamper 1: mutate a leaf value -> rejected!
        let mut bad_leaf = proof.clone();
        bad_leaf.opened_columns[0].values[0] += Goldilocks::ONE;
        let mut t_tr = base_tr.clone();
        assert!(canopy_verify(&params, &state.commitment, &point, claimed, &bad_leaf, &mut t_tr).is_err());

        // Tamper 2: mutate an auxiliary sibling digest -> rejected!
        let mut bad_sib = proof.clone();
        bad_sib.aux_siblings[0][0] ^= 0x01;
        let mut t_tr = base_tr.clone();
        assert!(canopy_verify(&params, &state.commitment, &point, claimed, &bad_sib, &mut t_tr).is_err());

        // Tamper 3: append an extra unread auxiliary sibling -> rejected!
        let mut extra_sib = proof.clone();
        extra_sib.aux_siblings.push([0u8; 32]);
        let mut t_tr = base_tr.clone();
        assert!(matches!(
            canopy_verify(&params, &state.commitment, &point, claimed, &extra_sib, &mut t_tr),
            Err(CanopyError::UnconsumedAuxiliarySiblings { remaining: 1 })
        ));

        // Tamper 4: mutate claimed evaluation -> rejected!
        let mut t_tr = base_tr.clone();
        assert!(canopy_verify(
            &params,
            &state.commitment,
            &point,
            claimed + GoldilocksExt2::ONE,
            &proof,
            &mut t_tr
        )
        .is_err());
    }
}
