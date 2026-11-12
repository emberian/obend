//! The relation of a state-advancing DeOS turn, checked on the stack.
//!
//! `DeosTurnRelationVerifier` implements `RelationVerifier` over a receipt that carries
//! a `ZkBiscuit` attenuation chain, a `Seat` settlement and a `Canopy` + `PikkuFold`
//! proof. Four public inputs pin what the receipt may say: `cap_root` the root grant,
//! `revoked_root` the nullifier window, `turn_hash` the turn descriptor, and
//! `post_state_root` the `Canopy` commitment. `check` names the clause a refused
//! receipt violates. The six-field wire envelope matches `Sel4MicrokitKernel`;
//! typed lineage/settlement fields retain their explicitly fixed-width encodings.

use super::*;

/// Canonical six-field DeOS envelope, shared with Sel4MicrokitKernel:
/// version 1, then six (u32 big-endian byte length, bytes) fields in this order.
/// The typed relation still validates the contents; this layer never casts repr(C).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeosTurnWire<'a> {
    pub challenge: &'a [u8],
    pub grant: &'a [u8],
    pub hops: &'a [u8],
    pub nullifier: &'a [u8],
    pub legs: &'a [u8],
    pub proof: &'a [u8],
}
impl<'a> DeosTurnWire<'a> {
    fn fields(self) -> [&'a [u8]; 6] {
        [
            self.challenge,
            self.grant,
            self.hops,
            self.nullifier,
            self.legs,
            self.proof,
        ]
    }
}
/// Returns the exact encoded prefix. An undersized buffer or unrepresentable length fails.
pub fn encode_turn_wire<'a>(turn: DeosTurnWire<'_>, out: &'a mut [u8]) -> Option<&'a [u8]> {
    let fields = turn.fields();
    let mut size = 1usize;
    for field in fields {
        u32::try_from(field.len()).ok()?;
        size = size.checked_add(4)?.checked_add(field.len())?;
    }
    let out = out.get_mut(..size)?;
    out[0] = 1;
    let mut offset = 1usize;
    for field in fields {
        let end = offset.checked_add(4)?;
        out.get_mut(offset..end)?
            .copy_from_slice(&u32::try_from(field.len()).ok()?.to_be_bytes());
        offset = end;
        let end = offset.checked_add(field.len())?;
        out.get_mut(offset..end)?.copy_from_slice(field);
        offset = end;
    }
    Some(out)
}
/// Exact consumption: rejects every truncated field/header and every trailing byte.
pub fn decode_turn_wire(bytes: &[u8]) -> Option<DeosTurnWire<'_>> {
    if bytes.first() != Some(&1) {
        return None;
    }
    let mut offset = 1usize;
    let mut fields: [&[u8]; 6] = [&[]; 6];
    for field in &mut fields {
        let end = offset.checked_add(4)?;
        let n =
            usize::try_from(u32::from_be_bytes(bytes.get(offset..end)?.try_into().ok()?)).ok()?;
        offset = end;
        let end = offset.checked_add(n)?;
        *field = bytes.get(offset..end)?;
        offset = end;
    }
    if offset != bytes.len() {
        return None;
    }
    Some(DeosTurnWire {
        challenge: fields[0],
        grant: fields[1],
        hops: fields[2],
        nullifier: fields[3],
        legs: fields[4],
        proof: fields[5],
    })
}

/// One block of a `ZkBiscuit` attenuation chain, in fixed width: the holder and the
/// channel are 32-byte digests here, not the byte strings of the Lean encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct BiscuitHop {
    pub rights: u64,
    pub holder: Digest,
    pub channel: Digest,
}
/// One leg of a `Seat` settlement: a balance and its signed change.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct SeatLeg {
    pub pre: i64,
    pub delta: i64,
}
/// The provenance digest of a grant and its hops. `None` if a hop carries a right
/// its parent lacks.
pub fn deos_lineage(grant: &BiscuitHop, hops: &[BiscuitHop]) -> Option<Digest> {
    let step = |tag: &[u8], prev: &Digest, h: &BiscuitHop| {
        let mut s = customized(tag);
        s.absorb(prev);
        s.absorb(&h.rights.to_be_bytes());
        s.absorb(&h.holder);
        s.absorb(&h.channel);
        s.digest()
    };
    let mut lineage = step(b"obend.deos.lineage.root.v1", &[0; 32], grant);
    let mut rights = grant.rights;
    for h in hops {
        if h.rights & !rights != 0 {
            return None;
        }
        lineage = step(b"obend.deos.lineage.hop.v1", &lineage, h);
        rights = h.rights;
    }
    Some(lineage)
}
pub fn deos_nullifier(lineage: &Digest) -> Digest {
    hash(b"obend.deos.nullifier.v1", lineage)
}
/// The turn descriptor `turn_hash` pins: the lineage, its nullifier and every leg.
pub fn deos_turn_digest(lineage: &Digest, nullifier: &Digest, legs: &[SeatLeg]) -> Digest {
    let mut s = customized(b"obend.deos.turn.v1");
    s.absorb(lineage);
    s.absorb(nullifier);
    s.left(legs.len() as u64);
    for l in legs {
        s.absorb(&l.pre.to_be_bytes());
        s.absorb(&l.delta.to_be_bytes());
    }
    s.digest()
}
/// No balance starts or ends negative, no sum overflows, and the changes cancel.
pub fn seat_conserved(legs: &[SeatLeg]) -> bool {
    let mut net = 0i64;
    for l in legs {
        match (l.pre.checked_add(l.delta), net.checked_add(l.delta)) {
            (Some(post), Some(n)) if l.pre >= 0 && post >= 0 => net = n,
            _ => return false,
        }
    }
    net == 0
}
/// The transcript of a DeOS turn: the outer challenge `verify_cipherclerk` compares,
/// then `(vk_digest, pre_state_root, post_state_root, turn_descriptor_digest)`
/// absorbed, then challenge 0 of the relation. Every later challenge follows it.
pub fn deos_transcript(
    pi: &FullPinnedPublicInputs,
    vk_digest: &Digest,
) -> (Transcript<RelationBound>, Digest, Digest) {
    let mut tr = pi.transcript();
    let outer = tr.squeeze();
    tr.absorb(b"deos.vk", vk_digest);
    tr.absorb(b"deos.pre", &pi.pre_state_root);
    tr.absorb(b"deos.post", &pi.post_state_root);
    tr.absorb(b"deos.turn", &pi.turn_hash);
    let challenge0 = tr.squeeze();
    (tr, outer, challenge0)
}
/// A fixed-capacity window of spent 32-byte nullifiers, held on the stack.
/// `revoked_root` pins `root()`, so a turn is checked against the window it names.
#[derive(Clone, Copy)]
pub struct NullifierWindow<const N: usize> {
    spent: [Digest; N],
    len: usize,
}
impl<const N: usize> Default for NullifierWindow<N> {
    fn default() -> Self {
        Self::new()
    }
}
impl<const N: usize> NullifierWindow<N> {
    pub const fn new() -> Self {
        Self {
            spent: [[0; 32]; N],
            len: 0,
        }
    }
    /// Scans every occupied slot, whether or not an earlier one matched.
    pub fn contains(&self, n: &Digest) -> bool {
        self.spent[..self.len]
            .iter()
            .fold(false, |hit, s| hit | (s == n))
    }
    /// Refuses a nullifier already present, and any nullifier once the window is full.
    pub fn insert(&mut self, n: Digest) -> bool {
        if self.len == N || self.contains(&n) {
            return false;
        }
        self.spent[self.len] = n;
        self.len = self
            .len
            .checked_add(1)
            .expect("window insertion is capacity checked");
        true
    }
    pub fn root(&self) -> Digest {
        let mut s = customized(b"obend.deos.nullifier-window.v1");
        s.left(self.len as u64);
        for d in &self.spent[..self.len] {
            s.absorb(d);
        }
        s.digest()
    }
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct DeosTurnReceipt<const HOPS: usize, const LEGS: usize, P: Copy> {
    pub fs_challenge0: Digest,
    pub grant: BiscuitHop,
    pub hops: [BiscuitHop; HOPS],
    pub nullifier: Digest,
    pub legs: [SeatLeg; LEGS],
    pub proof: P,
}
/// Serialize the actual typed receipt into the shared six-field envelope. Proof bytes
/// belong to the proof codec; this function frames them exactly and never casts a struct.
pub fn encode_turn_receipt<'a, const H: usize, const L: usize, P: Copy>(
    r: &DeosTurnReceipt<H, L, P>,
    proof: &[u8],
    out: &'a mut [u8],
) -> Option<&'a [u8]> {
    let hops_len = H.checked_mul(72)?;
    let legs_len = L.checked_mul(16)?;
    let sizes = [32, 72, hops_len, 32, legs_len, proof.len()];
    let mut total = 1usize;
    for n in sizes {
        u32::try_from(n).ok()?;
        total = total.checked_add(4)?.checked_add(n)?;
    }
    let out = out.get_mut(..total)?;
    let mut pos = 0usize;
    let mut put = |bytes: &[u8]| -> Option<()> {
        let end = pos.checked_add(bytes.len())?;
        out.get_mut(pos..end)?.copy_from_slice(bytes);
        pos = end;
        Some(())
    };
    put(&[1])?;
    put(&32u32.to_be_bytes())?;
    put(&r.fs_challenge0)?;
    put(&72u32.to_be_bytes())?;
    put(&r.grant.rights.to_be_bytes())?;
    put(&r.grant.holder)?;
    put(&r.grant.channel)?;
    put(&u32::try_from(hops_len).ok()?.to_be_bytes())?;
    for hop in r.hops {
        put(&hop.rights.to_be_bytes())?;
        put(&hop.holder)?;
        put(&hop.channel)?;
    }
    put(&32u32.to_be_bytes())?;
    put(&r.nullifier)?;
    put(&u32::try_from(legs_len).ok()?.to_be_bytes())?;
    for leg in r.legs {
        put(&leg.pre.to_be_bytes())?;
        put(&leg.delta.to_be_bytes())?;
    }
    put(&u32::try_from(proof.len()).ok()?.to_be_bytes())?;
    put(proof)?;
    Some(out)
}

/// Decode every descriptor field, refusing partial hops/legs and wrong digest widths.
/// `proof` must validate/consume its entire supplied slice; framing never discards a suffix.
pub fn decode_turn_receipt<const H: usize, const L: usize, P: Copy>(
    bytes: &[u8],
    proof: impl FnOnce(&[u8]) -> Option<P>,
) -> Option<DeosTurnReceipt<H, L, P>> {
    fn hop(b: &[u8]) -> Option<BiscuitHop> {
        if b.len() != 72 {
            return None;
        }
        Some(BiscuitHop {
            rights: u64::from_be_bytes(b.get(..8)?.try_into().ok()?),
            holder: b.get(8..40)?.try_into().ok()?,
            channel: b.get(40..72)?.try_into().ok()?,
        })
    }
    let w = decode_turn_wire(bytes)?;
    if w.hops.len() != H.checked_mul(72)? || w.legs.len() != L.checked_mul(16)? {
        return None;
    }
    let grant = hop(w.grant)?;
    let mut hops = [grant; H];
    for (i, h) in hops.iter_mut().enumerate() {
        let start = i.checked_mul(72)?;
        *h = hop(w.hops.get(start..start.checked_add(72)?)?)?;
    }
    let mut legs = [SeatLeg { pre: 0, delta: 0 }; L];
    for (i, leg) in legs.iter_mut().enumerate() {
        let start = i.checked_mul(16)?;
        let middle = start.checked_add(8)?;
        leg.pre = i64::from_be_bytes(w.legs.get(start..middle)?.try_into().ok()?);
        leg.delta = i64::from_be_bytes(
            w.legs
                .get(middle..start.checked_add(16)?)?
                .try_into()
                .ok()?,
        );
    }
    Some(DeosTurnReceipt {
        fs_challenge0: w.challenge.try_into().ok()?,
        grant,
        hops,
        nullifier: w.nullifier.try_into().ok()?,
        legs,
        proof: proof(w.proof)?,
    })
}

/// The clause of the DeOS turn relation a receipt violates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeosRefusal {
    Instance,
    UnboundTranscript,
    Lineage,
    ReplayedNullifier,
    UnbalancedSeat,
    CanopyOpening,
    PikkuFold,
    ClaimMismatch,
}
/// The relation of a state-advancing DeOS turn, checked without a heap. `cap_root`
/// pins the root grant, `revoked_root` the nullifier window, `turn_hash` the turn
/// descriptor, and `post_state_root` the `Canopy` commitment.
pub struct DeosTurnRelationVerifier<
    const COLS: usize,
    const DEG: usize,
    const LAYERS: usize,
    const W: usize,
    const N: usize,
> {
    pub vk_digest: Digest,
    pub proofs: CanopyPikkuRelation<COLS, DEG, LAYERS, W>,
    pub spent: NullifierWindow<N>,
}
type DeosProof<
    const CAP: usize,
    const Q: usize,
    const BOT: usize,
    const COLS: usize,
    const W: usize,
> = CanopyPikkuReceipt<CAP, Q, BOT, COLS, W>;
impl<const COLS: usize, const DEG: usize, const LAYERS: usize, const W: usize, const N: usize>
    DeosTurnRelationVerifier<COLS, DEG, LAYERS, W, N>
{
    pub fn check<
        const CAP: usize,
        const Q: usize,
        const BOT: usize,
        const HOPS: usize,
        const LEGS: usize,
    >(
        &self,
        pi: &FullPinnedPublicInputs,
        challenge: &Digest,
        r: &DeosTurnReceipt<HOPS, LEGS, DeosProof<CAP, Q, BOT, COLS, W>>,
    ) -> Result<(), DeosRefusal> {
        use DeosRefusal::*;
        let p = &r.proof;
        if pi.circuit_desc_digest != self.proofs.circuit
            || pi.actor_vk_digest != self.vk_digest
            || pi.revoked_root != self.spent.root()
            || COLS == 0
            || W == 0
            || W != Q
        {
            return Err(Instance);
        }
        let (mut tr, outer, challenge0) = deos_transcript(pi, &self.vk_digest);
        if outer != *challenge || challenge0 != r.fs_challenge0 {
            return Err(UnboundTranscript);
        }
        let lineage = deos_lineage(&r.grant, &r.hops).ok_or(Lineage)?;
        if Some(pi.cap_root) != deos_lineage(&r.grant, &[])
            || r.nullifier != deos_nullifier(&lineage)
            || pi.turn_hash != deos_turn_digest(&lineage, &r.nullifier, &r.legs)
        {
            return Err(Lineage);
        }
        if self.spent.contains(&r.nullifier) {
            return Err(ReplayedNullifier);
        }
        if !seat_conserved(&r.legs) {
            return Err(UnbalancedSeat);
        }
        if !self.proofs.canopy(&mut tr, &pi.post_state_root, p) {
            return Err(CanopyOpening);
        }
        // Cross-binding: PikkuFold folds exactly the column Canopy opened, under a
        // challenge that depends on the Canopy claim, and projects to the claimed value.
        tr.absorb(b"deos.canopy.iacc", &p.iacc.0.to_be_bytes());
        if !verify_pikku(&mut tr, &p.w1, &p.w2, &p.folded, self.proofs.beta) {
            return Err(PikkuFold);
        }
        if (0..W).any(|i| p.w1[i] != p.queries[i].row[0]) || !self.proofs.projects(p) {
            return Err(ClaimMismatch);
        }
        Ok(())
    }
}
impl<
        const CAP: usize,
        const Q: usize,
        const BOT: usize,
        const COLS: usize,
        const DEG: usize,
        const LAYERS: usize,
        const W: usize,
        const N: usize,
        const HOPS: usize,
        const LEGS: usize,
    > RelationVerifier<DeosTurnReceipt<HOPS, LEGS, DeosProof<CAP, Q, BOT, COLS, W>>>
    for DeosTurnRelationVerifier<COLS, DEG, LAYERS, W, N>
{
    fn commit_turn(
        &mut self,
        _pi: &FullPinnedPublicInputs,
        r: &DeosTurnReceipt<HOPS, LEGS, DeosProof<CAP, Q, BOT, COLS, W>>,
    ) -> bool {
        self.spent.insert(r.nullifier)
    }
    fn verify_relation(
        &self,
        pi: &FullPinnedPublicInputs,
        challenge: &Digest,
        r: &DeosTurnReceipt<HOPS, LEGS, DeosProof<CAP, Q, BOT, COLS, W>>,
    ) -> bool {
        self.check(pi, challenge, r).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use DeosRefusal::*;

    type Proof = CanopyPikkuReceipt<4, 3, 1, 1, 3>;
    type Receipt = DeosTurnReceipt<1, 2, Proof>;
    type Verifier = DeosTurnRelationVerifier<1, 2, 1, 3, 4>;

    fn leg(pre: i64, delta: i64) -> SeatLeg {
        SeatLeg { pre, delta }
    }
    const LEGS: [SeatLeg; 2] = [
        SeatLeg {
            pre: 100,
            delta: -40,
        },
        SeatLeg { pre: 5, delta: 40 },
    ];

    /// An honest prover for a turn with these legs, one hop carrying `hop_rights`
    /// under a grant of rights `0b111`, against a window holding `spent`. `skew`
    /// shifts the folded witness away from the opened Canopy column; everything
    /// downstream of it (challenge, fold, projection) is still computed honestly.
    fn prove(
        legs: [SeatLeg; 2],
        hop_rights: u64,
        spent: &[Digest],
        skew: u64,
    ) -> (Verifier, SovereignTurnBundle<Receipt>) {
        prove_at(legs, hop_rights, spent, skew, None)
    }
    fn prove_at(
        legs: [SeatLeg; 2],
        hop_rights: u64,
        spent: &[Digest],
        skew: u64,
        previous: Option<&FullPinnedPublicInputs>,
    ) -> (Verifier, SovereignTurnBundle<Receipt>) {
        let coeff = [Goldilocks::new(11), Goldilocks::new(5)];
        let rows: [[Goldilocks; 1]; 8] =
            core::array::from_fn(|i| [eval(&coeff, Goldilocks::new(i as u64))]);
        let leaves: [Digest; 8] = core::array::from_fn(|i| canopy_leaf(&rows[i]));
        let cap: [Digest; 4] =
            core::array::from_fn(|i| canopy_parent(&leaves[2 * i], &leaves[2 * i + 1]));
        let grant = BiscuitHop {
            rights: 0b111,
            holder: [7; 32],
            channel: [8; 32],
        };
        let hops = [BiscuitHop {
            rights: hop_rights,
            holder: [9; 32],
            channel: [10; 32],
        }];
        let lineage = deos_lineage(&grant, &hops).unwrap_or([0; 32]);
        let nullifier = deos_nullifier(&lineage);
        let mut window = NullifierWindow::new();
        for s in spent {
            assert!(window.insert(*s));
        }
        let p = FullPinnedPublicInputs {
            circuit_desc_digest: [0x11; 32],
            actor_vk_digest: [0x22; 32],
            pre_state_root: previous.map_or([0x33; 32], |p| p.post_state_root),
            post_state_root: canopy_root(3, 2, &cap),
            cap_root: deos_lineage(&grant, &[]).unwrap(),
            revoked_root: window.root(),
            height: previous.map_or(1, |p| p.height.checked_add(1).unwrap()),
            turn_hash: deos_turn_digest(&lineage, &nullifier, &legs),
        };
        let v = Verifier {
            vk_digest: p.actor_vk_digest,
            proofs: CanopyPikkuRelation {
                circuit: p.circuit_desc_digest,
                polynomials: [coeff],
                kronecker_factors: [[1, -1, 1]],
                beta: Goldilocks::P / 2,
            },
            spent: window,
        };
        let (mut tr, challenge0, fs_challenge0) = deos_transcript(&p, &v.vk_digest);
        tr.absorb(b"canopy.root", &p.post_state_root);
        let _alpha = tr.goldilocks();
        let rho = tr.goldilocks();
        let idx: [usize; 3] = core::array::from_fn(|_| {
            u64::from_be_bytes(tr.squeeze()[..8].try_into().unwrap()) as usize & 7
        });
        let queries = core::array::from_fn(|i| CanopyPikkuQuery {
            index: idx[i],
            row: rows[idx[i]],
            path: [leaves[idx[i] ^ 1]],
        });
        let iacc = (0..3)
            .rev()
            .fold(Goldilocks::ZERO, |acc, i| acc * rho + rows[idx[i]][0]);
        tr.absorb(b"deos.canopy.iacc", &iacc.0.to_be_bytes());
        let w1: [Goldilocks; 3] = core::array::from_fn(|i| rows[idx[i]][0] + Goldilocks::new(skew));
        let w2 = [Goldilocks::new(3), Goldilocks::new(1), Goldilocks::new(2)];
        let c = pikku_challenge(&mut tr, &w1, &w2);
        let folded: [Goldilocks; 3] = core::array::from_fn(|i| w1[i] + c * w2[i]);
        let mut scratch = folded;
        let claimed_proj = kronecker_ternary(&mut scratch, &v.proofs.kronecker_factors).unwrap();
        let proof = CanopyPikkuReceipt {
            depth: 3,
            cap_height: 2,
            cap,
            queries,
            iacc,
            w1,
            w2,
            folded,
            claimed_proj,
        };
        let receipt = DeosTurnReceipt {
            fs_challenge0,
            grant,
            hops,
            nullifier,
            legs,
            proof,
        };
        let bundle = SovereignTurnBundle {
            public_inputs: p,
            challenge0,
            effect_vk_digest: p.actor_vk_digest,
            last_row_gate_ok: true,
            receipt,
        };
        (v, bundle)
    }
    fn verdict(v: &Verifier, b: &SovereignTurnBundle<Receipt>) -> Result<(), DeosRefusal> {
        let r = v.check(&b.public_inputs, &b.challenge0, &b.receipt);
        assert_eq!(verify_cipherclerk(v, b), r.is_ok());
        r
    }

    #[test]
    fn honest_turn_is_accepted_and_settles_through_the_pd() {
        let (v, b) = prove(LEGS, 0b011, &[], 0);
        assert_eq!(verdict(&v, &b), Ok(()));
        let mut inbound = IpcRing::<_, 2>::new();
        let mut outbound = IpcRing::<SettlementVerdict, 2>::new();
        let (mut tx, mut rx) = inbound.split();
        let (mut otx, mut orx) = outbound.split();
        assert!(tx.push(b).is_ok());
        let mut pd = VerifierPd::new(v, b.public_inputs.pre_state_root, 0);
        assert_eq!(pd.drain(&mut rx, &mut otx), 1);
        let settled = orx.pop().unwrap();
        assert!(settled.accepted);
        assert_eq!(settled.committed_root, b.public_inputs.post_state_root);
        // The PD spends the nullifier; the window's root moves with it.
        let before = b.public_inputs.revoked_root;
        assert!(pd.verifier.spent.contains(&b.receipt.nullifier));
        assert!(!pd.verifier.spent.insert(b.receipt.nullifier));
        assert_ne!(pd.verifier.spent.root(), before);
        assert_eq!(
            pd.verifier
                .check(&b.public_inputs, &b.challenge0, &b.receipt),
            Err(Instance)
        );
    }

    #[test]
    fn lean_deos_wire_vector_and_all_truncations() {
        let vector: &[u8] = &[
            1, 0, 0, 0, 2, 0x12, 0x34, 0, 0, 0, 1, 0xff, 0, 0, 0, 0, 0, 0, 0, 1, 0xab, 0, 0, 0, 0,
            0, 0, 0, 2, 0x56, 0x78,
        ];
        let turn = DeosTurnWire {
            challenge: &[0x12, 0x34],
            grant: &[0xff],
            hops: &[],
            nullifier: &[0xab],
            legs: &[],
            proof: &[0x56, 0x78],
        };
        let mut out = [0u8; 64];
        assert_eq!(encode_turn_wire(turn, &mut out), Some(vector));
        assert_eq!(decode_turn_wire(vector), Some(turn));
        for end in 0..vector.len() {
            assert_eq!(decode_turn_wire(&vector[..end]), None);
        }
        let mut trailing = std::vec::Vec::from(vector);
        trailing.push(0);
        assert_eq!(decode_turn_wire(&trailing), None);
        let mut bad_len = std::vec::Vec::from(vector);
        bad_len[1..5].fill(0xff);
        assert_eq!(decode_turn_wire(&bad_len), None);
        assert!(encode_turn_wire(turn, &mut [0; 4]).is_none());
    }

    #[test]
    fn lean_typed_deos_signed_seat_vector() {
        let receipt = DeosTurnReceipt {
            fs_challenge0: [0x12; 32],
            grant: BiscuitHop {
                rights: 7,
                holder: [7; 32],
                channel: [8; 32],
            },
            hops: [],
            nullifier: [0xab; 32],
            legs: LEGS,
            proof: (0x56u8, 0x78u8),
        };
        let expected: &[u8] = &[
            1, 0, 0, 0, 32, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18,
            18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0,
            0, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
            7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
            8, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0, 0, 0, 0, 0, 32, 171, 171, 171, 171, 171, 171, 171,
            171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
            171, 171, 171, 171, 171, 171, 171, 171, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 100, 255,
            255, 255, 255, 255, 255, 255, 216, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 40, 0,
            0, 0, 2, 86, 120,
        ];
        let mut out = [0; 256];
        assert_eq!(
            encode_turn_receipt(&receipt, &[0x56, 0x78], &mut out),
            Some(expected)
        );
        let decoded = decode_turn_receipt::<0, 2, _>(expected, |p| {
            if let [a, b] = p {
                Some((*a, *b))
            } else {
                None
            }
        })
        .unwrap();
        assert_eq!(decoded.legs, LEGS);
        assert_eq!(decoded.grant, receipt.grant);
        assert_eq!(decoded.proof, receipt.proof);
    }

    #[test]
    fn typed_wire_roundtrip_rejects_partial_hops_and_legs() {
        let (_, b) = prove(LEGS, 0b011, &[], 0);
        let r = DeosTurnReceipt {
            fs_challenge0: b.receipt.fs_challenge0,
            grant: b.receipt.grant,
            hops: b.receipt.hops,
            nullifier: b.receipt.nullifier,
            legs: b.receipt.legs,
            proof: 42u8,
        };
        let mut out = [0; 512];
        let bytes = encode_turn_receipt(&r, &[42], &mut out).unwrap();
        let proof = |bs: &[u8]| if let [v] = bs { Some(*v) } else { None };
        let decoded = decode_turn_receipt::<1, 2, _>(bytes, proof).unwrap();
        assert_eq!(decoded.fs_challenge0, r.fs_challenge0);
        assert_eq!(decoded.grant, r.grant);
        assert_eq!(decoded.hops, r.hops);
        assert_eq!(decoded.nullifier, r.nullifier);
        assert_eq!(decoded.legs, r.legs);
        assert_eq!(decoded.proof, r.proof);
        let w = decode_turn_wire(bytes).unwrap();
        for bad in [
            DeosTurnWire {
                hops: &w.hops[..71],
                ..w
            },
            DeosTurnWire {
                legs: &w.legs[..31],
                ..w
            },
            DeosTurnWire {
                nullifier: &w.nullifier[..31],
                ..w
            },
        ] {
            let mut bad_bytes = [0; 512];
            let encoded = encode_turn_wire(bad, &mut bad_bytes).unwrap();
            assert!(decode_turn_receipt::<1, 2, _>(encoded, proof).is_none());
        }
    }

    #[test]
    fn same_drain_replay_is_quarantined() {
        let (v, first) = prove(LEGS, 0b011, &[], 0);
        // Valid height, pre-root and cryptographic transcript; stale revocation root.
        // Without commit_turn both independently valid relations would be accepted.
        let (_, second) = prove_at(LEGS, 0b011, &[], 0, Some(&first.public_inputs));
        assert!(verify_cipherclerk(&v, &second));
        let mut input = IpcRing::<_, 4>::new();
        let mut output = IpcRing::<SettlementVerdict, 4>::new();
        let (mut tx, mut rx) = input.split();
        let (mut otx, mut orx) = output.split();
        assert!(tx.push(first).is_ok() && tx.push(second).is_ok());
        let mut pd = VerifierPd::new(v, first.public_inputs.pre_state_root, 0);
        assert_eq!(pd.drain(&mut rx, &mut otx), 2);
        assert!(orx.pop().unwrap().accepted);
        assert!(!orx.pop().unwrap().accepted);
        assert!(pd.quarantined && pd.verifier.spent.contains(&first.receipt.nullifier));
        assert_eq!(pd.height, 1);
    }

    #[test]
    fn distinct_turns_advance_spent_state_through_backpressure() {
        let (v, first) = prove(LEGS, 0b011, &[], 0);
        let (_, second) = prove_at(
            LEGS,
            0b001,
            &[first.receipt.nullifier],
            0,
            Some(&first.public_inputs),
        );
        assert_ne!(first.receipt.nullifier, second.receipt.nullifier);
        let mut input = IpcRing::<_, 4>::new();
        let mut output = IpcRing::<SettlementVerdict, 1>::new();
        let (mut tx, mut rx) = input.split();
        let (mut otx, mut orx) = output.split();
        assert!(tx.push(first).is_ok() && tx.push(second).is_ok());
        let mut pd = VerifierPd::new(v, first.public_inputs.pre_state_root, 0);
        assert_eq!(pd.drain(&mut rx, &mut otx), 2);
        assert!(orx.pop().unwrap().accepted);
        assert_eq!(pd.drain(&mut rx, &mut otx), 0);
        assert!(orx.pop().unwrap().accepted);
        assert!(!pd.quarantined);
        assert_eq!(pd.height, 2);
        assert!(pd.verifier.spent.contains(&first.receipt.nullifier));
        assert!(pd.verifier.spent.contains(&second.receipt.nullifier));
    }

    #[test]
    fn full_window_quarantines_before_state_commit() {
        let (v, b) = prove(LEGS, 0b011, &[[1; 32], [2; 32], [3; 32], [4; 32]], 0);
        assert!(verify_cipherclerk(&v, &b));
        let mut input = IpcRing::<_, 2>::new();
        let mut output = IpcRing::<SettlementVerdict, 2>::new();
        let (mut tx, mut rx) = input.split();
        let (mut otx, mut orx) = output.split();
        assert!(tx.push(b).is_ok());
        let mut pd = VerifierPd::new(v, b.public_inputs.pre_state_root, 0);
        assert_eq!(pd.drain(&mut rx, &mut otx), 1);
        assert!(!orx.pop().unwrap().accepted);
        assert!(pd.quarantined);
        assert_eq!(pd.committed_root, b.public_inputs.pre_state_root);
        assert_eq!(pd.height, 0);
    }

    #[test]
    fn replayed_nullifier_is_refused() {
        let (_, honest) = prove(LEGS, 0b011, &[], 0);
        // The prover rebuilds everything against the window that already holds its nullifier.
        let (v, b) = prove(LEGS, 0b011, &[[1; 32], honest.receipt.nullifier], 0);
        assert_eq!(b.receipt.nullifier, honest.receipt.nullifier);
        assert_eq!(verdict(&v, &b), Err(ReplayedNullifier));
        // An unrelated spent nullifier does not refuse the turn.
        let (v, b) = prove(LEGS, 0b011, &[[1; 32], [2; 32]], 0);
        assert_eq!(verdict(&v, &b), Ok(()));
        // A full window refuses to grow, and a stale window is not the instance's.
        let mut full = NullifierWindow::<2>::new();
        assert!(full.insert([1; 32]) && full.insert([2; 32]) && !full.insert([3; 32]));
        let (mut v, b) = prove(LEGS, 0b011, &[[1; 32]], 0);
        v.spent = NullifierWindow::new();
        assert_eq!(verdict(&v, &b), Err(Instance));
    }

    #[test]
    fn unbalanced_seat_is_refused() {
        for legs in [
            [leg(100, -40), leg(5, 41)],          // net mint
            [leg(100, -41), leg(5, 40)],          // net burn
            [leg(10, -11), leg(0, 11)],           // negative post-balance
            [leg(-1, 1), leg(1, -1)],             // negative pre-balance
            [leg(i64::MAX, 1), leg(5, -1)],       // balance overflow
            [leg(0, i64::MAX), leg(0, i64::MAX)], // net overflow
        ] {
            assert!(!seat_conserved(&legs));
            let (v, b) = prove(legs, 0b011, &[], 0);
            assert_eq!(verdict(&v, &b), Err(UnbalancedSeat));
        }
        assert!(seat_conserved(&[leg(i64::MAX, 0), leg(0, 0)]) && seat_conserved(&[]));
        // Legs swapped after proving no longer hash to the pinned turn descriptor.
        let (v, mut b) = prove(LEGS, 0b011, &[], 0);
        b.receipt.legs = [leg(100, -40), leg(5, 41)];
        assert_eq!(verdict(&v, &b), Err(Lineage));
    }

    #[test]
    fn unbound_transcript_is_refused() {
        let (v, b) = prove(LEGS, 0b011, &[], 0);
        // Challenge 0 taken before the statement was absorbed.
        let mut early = b;
        early.receipt.fs_challenge0 = b.challenge0;
        assert_eq!(verdict(&v, &early), Err(UnboundTranscript));
        // The same receipt presented for another instance: each absorbed field moves challenge 0.
        for field in 0..3 {
            let mut other = b;
            match field {
                0 => other.public_inputs.pre_state_root[0] ^= 1,
                1 => other.public_inputs.height += 1,
                _ => other.public_inputs.cap_root[0] ^= 1,
            }
            other.challenge0 = other.public_inputs.transcript().squeeze();
            assert_eq!(verdict(&v, &other), Err(UnboundTranscript));
        }
        // A wrong outer challenge never reaches the relation at all.
        let mut stale = b;
        stale.challenge0[0] ^= 1;
        assert!(!verify_cipherclerk(&v, &stale));
        assert_eq!(
            v.check(&stale.public_inputs, &stale.challenge0, &stale.receipt),
            Err(UnboundTranscript)
        );
        // Another verification key is another instance.
        let mut rekeyed = Verifier { ..v };
        rekeyed.vk_digest[0] ^= 1;
        assert_eq!(verdict(&rekeyed, &b), Err(Instance));
    }

    #[test]
    fn mismatched_canopy_pikkufold_claim_is_refused() {
        // A fold of some other witness, with its challenge, fold and projection all honest.
        let (v, b) = prove(LEGS, 0b011, &[], 1);
        assert_eq!(verdict(&v, &b), Err(ClaimMismatch));
        let (v, b) = prove(LEGS, 0b011, &[], 0);
        // A projection claim the folded witness does not have.
        let mut lie = b;
        lie.receipt.proof.claimed_proj = b.receipt.proof.claimed_proj + Goldilocks::ONE;
        assert_eq!(verdict(&v, &lie), Err(ClaimMismatch));
        // A Canopy claim changed after the fold challenge was drawn.
        let mut lie = b;
        lie.receipt.proof.iacc = b.receipt.proof.iacc + Goldilocks::ONE;
        assert_eq!(verdict(&v, &lie), Err(CanopyOpening));
        // A fold that is not `w1 + c * w2`.
        let mut lie = b;
        lie.receipt.proof.folded[0] = b.receipt.proof.folded[0] + Goldilocks::ONE;
        assert_eq!(verdict(&v, &lie), Err(PikkuFold));
    }

    #[test]
    fn lineage_must_attenuate_and_match_the_pinned_grant() {
        // A hop that widens the grant's rights.
        let (v, b) = prove(LEGS, 0b1111, &[], 0);
        assert_eq!(verdict(&v, &b), Err(Lineage));
        assert_eq!(deos_lineage(&b.receipt.grant, &b.receipt.hops), None);
        let (v, b) = prove(LEGS, 0b011, &[], 0);
        // Another root grant than the one `cap_root` pins.
        let mut forged = b;
        forged.receipt.grant.holder = [0x55; 32];
        assert_eq!(verdict(&v, &forged), Err(Lineage));
        // A hop edited after the nullifier was derived, and a nullifier chosen freely.
        let mut forged = b;
        forged.receipt.hops[0].channel = [0x56; 32];
        assert_eq!(verdict(&v, &forged), Err(Lineage));
        let mut forged = b;
        forged.receipt.nullifier = [0x57; 32];
        assert_eq!(verdict(&v, &forged), Err(Lineage));
        // Holder and channel are separate fields of the lineage.
        let hop = |holder, channel| BiscuitHop {
            rights: 1,
            holder,
            channel,
        };
        assert_ne!(
            deos_lineage(&hop([1; 32], [2; 32]), &[]),
            deos_lineage(&hop([2; 32], [1; 32]), &[])
        );
    }
}
