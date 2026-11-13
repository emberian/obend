//! The relation of a state-advancing DeOS turn, checked on the stack.
//!
//! `DeosTurnRelationVerifier` implements `RelationVerifier` over a receipt that carries
//! a `ZkBiscuit` attenuation chain, a Merkle-authenticated `Seat` settlement, and a
//! `Canopy` + `PikkuFold` proof. Public inputs pin every component: `cap_root` pins the
//! root grant, `revoked_root` pins the nullifier window, `turn_hash` pins the turn
//! descriptor (including every leg's `seat_id`, `pre`, and `delta`), and `pre_state_root`
//! / `post_state_root` pin the 256-bit composite `(seat_merkle_root, canopy_root)` state
//! transition. `check` names the exact clause a refused receipt violates. The six-field
//! wire envelope matches `Sel4MicrokitKernel`; typed lineage/settlement fields retain
//! their explicitly fixed-width big-endian encodings.

use super::*;

/// Depth of the fixed-width 256-bit `Seat` balance Merkle tree (`2^8 = 256` seats).
pub const SEAT_MERKLE_DEPTH: usize = 8;
/// Number of distinct addressable seats in the `Seat` Merkle tree.
pub const SEAT_TABLE_LEN: usize = 1 << SEAT_MERKLE_DEPTH;
/// Wire width of one `SeatLeg`: `seat_id (8) + pre (8) + delta (8) + merkle_path (8 * 32) = 280`.
pub const SEAT_LEG_WIRE_LEN: usize = 24 + SEAT_MERKLE_DEPTH * 32;
/// Wire header of the `legs` field carrying `(pre_seat_root, pre_canopy_root, post_canopy_root)`.
pub const SEAT_STATE_ROOTS_WIRE_LEN: usize = 96;

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
/// One leg of a Merkle-authenticated `Seat` settlement: the seat index, its committed
/// pre-turn balance, its signed balance change, and the sibling authentication path in
/// the sequential 256-bit `Seat` Merkle tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct SeatLeg {
    pub seat_id: u64,
    pub pre: i64,
    pub delta: i64,
    pub merkle_path: [Digest; SEAT_MERKLE_DEPTH],
}
impl SeatLeg {
    pub const ZERO: Self = Self {
        seat_id: 0,
        pre: 0,
        delta: 0,
        merkle_path: [[0; 32]; SEAT_MERKLE_DEPTH],
    };
}

/// Domain-separated 256-bit leaf digest for `(seat_id, balance)` in the `Seat` Merkle tree.
pub fn deos_seat_leaf(seat_id: u64, balance: i64) -> Digest {
    let mut s = customized(b"obend.deos.seat.leaf.v1");
    s.absorb(&seat_id.to_be_bytes());
    s.absorb(&balance.to_be_bytes());
    s.digest()
}

/// Domain-separated, level-pinned 256-bit internal node digest in the `Seat` Merkle tree.
pub fn deos_seat_parent(level: u8, left: &Digest, right: &Digest) -> Digest {
    let mut s = customized(b"obend.deos.seat.node.v1");
    s.absorb(&[level]);
    s.absorb(left);
    s.absorb(right);
    s.digest()
}

/// Domain-separated 256-bit composite DeOS state root binding both the `Seat` balance
/// Merkle root and the `Canopy` polynomial commitment root.
pub fn deos_state_root(seat_root: &Digest, canopy_root: &Digest) -> Digest {
    let mut s = customized(b"obend.deos.state.root.v1");
    s.absorb(seat_root);
    s.absorb(canopy_root);
    s.digest()
}

/// Recompute the 256-bit `Seat` Merkle root implied by `(seat_id, balance)` and `path`.
/// Returns `None` if `seat_id` exceeds `SEAT_TABLE_LEN - 1`.
pub fn compute_seat_merkle_root(
    seat_id: u64,
    balance: i64,
    path: &[Digest; SEAT_MERKLE_DEPTH],
) -> Option<Digest> {
    if seat_id >= SEAT_TABLE_LEN as u64 {
        return None;
    }
    let mut cur = deos_seat_leaf(seat_id, balance);
    for (lvl, sibling) in path.iter().enumerate() {
        let bit = (seat_id >> lvl) & 1;
        cur = if bit == 0 {
            deos_seat_parent(lvl as u8, &cur, sibling)
        } else {
            deos_seat_parent(lvl as u8, sibling, &cur)
        };
    }
    Some(cur)
}

/// Every leg addresses a valid, pairwise-distinct seat index in `0..SEAT_TABLE_LEN`.
pub fn seats_distinct_and_valid(legs: &[SeatLeg]) -> bool {
    for (i, a) in legs.iter().enumerate() {
        if a.seat_id >= SEAT_TABLE_LEN as u64 {
            return false;
        }
        for b in &legs[i + 1..] {
            if a.seat_id == b.seat_id {
                return false;
            }
        }
    }
    true
}

/// Verify every leg's pre-state Merkle inclusion against the running `Seat` Merkle root
/// and advance the root to each leg's post-balance along the same authenticated sibling path.
pub fn apply_seat_legs_merkle(pre_seat_root: &Digest, legs: &[SeatLeg]) -> Option<Digest> {
    if !seats_distinct_and_valid(legs) || !seat_conserved(legs) {
        return None;
    }
    let mut cur_root = *pre_seat_root;
    for leg in legs {
        let opened_pre = compute_seat_merkle_root(leg.seat_id, leg.pre, &leg.merkle_path)?;
        if opened_pre != cur_root {
            return None;
        }
        let post_balance = leg.pre.checked_add(leg.delta)?;
        if post_balance < 0 {
            return None;
        }
        cur_root = compute_seat_merkle_root(leg.seat_id, post_balance, &leg.merkle_path)?;
    }
    Some(cur_root)
}

/// Stack-resident 256-seat balance table for constructing authenticated `SeatLeg`s without `alloc`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SeatMerkleTree {
    balances: [i64; SEAT_TABLE_LEN],
}
impl Default for SeatMerkleTree {
    fn default() -> Self {
        Self::new()
    }
}
impl SeatMerkleTree {
    pub const fn new() -> Self {
        Self {
            balances: [0; SEAT_TABLE_LEN],
        }
    }

    pub fn balance(&self, seat_id: u64) -> Option<i64> {
        let idx = usize::try_from(seat_id).ok()?;
        self.balances.get(idx).copied()
    }

    pub fn set_balance(&mut self, seat_id: u64, balance: i64) -> bool {
        let Ok(idx) = usize::try_from(seat_id) else {
            return false;
        };
        if balance < 0 || idx >= SEAT_TABLE_LEN {
            return false;
        }
        self.balances[idx] = balance;
        true
    }

    pub fn root(&self) -> Digest {
        let mut nodes: [Digest; SEAT_TABLE_LEN] =
            core::array::from_fn(|i| deos_seat_leaf(i as u64, self.balances[i]));
        let mut width = SEAT_TABLE_LEN;
        for lvl in 0..SEAT_MERKLE_DEPTH {
            let half = width / 2;
            for i in 0..half {
                nodes[i] = deos_seat_parent(lvl as u8, &nodes[2 * i], &nodes[2 * i + 1]);
            }
            width = half;
        }
        nodes[0]
    }

    pub fn open(&self, seat_id: u64) -> Option<[Digest; SEAT_MERKLE_DEPTH]> {
        let mut idx = usize::try_from(seat_id).ok()?;
        if idx >= SEAT_TABLE_LEN {
            return None;
        }
        let mut nodes: [Digest; SEAT_TABLE_LEN] =
            core::array::from_fn(|i| deos_seat_leaf(i as u64, self.balances[i]));
        let mut path = [[0u8; 32]; SEAT_MERKLE_DEPTH];
        let mut width = SEAT_TABLE_LEN;
        for (lvl, slot) in path.iter_mut().enumerate() {
            *slot = nodes[idx ^ 1];
            let half = width / 2;
            for i in 0..half {
                nodes[i] = deos_seat_parent(lvl as u8, &nodes[2 * i], &nodes[2 * i + 1]);
            }
            idx >>= 1;
            width = half;
        }
        Some(path)
    }

    /// Apply `L` distinct signed deltas sequentially, returning `(pre_seat_root, legs, post_seat_root)`.
    /// Leaves `self` unchanged if any `seat_id` is out of range, duplicated, or produces a negative/overflowing balance.
    pub fn apply_settlement<const L: usize>(
        &mut self,
        deltas: [(u64, i64); L],
    ) -> Option<(Digest, [SeatLeg; L], Digest)> {
        for i in 0..L {
            if deltas[i].0 >= SEAT_TABLE_LEN as u64 {
                return None;
            }
            for j in (i + 1)..L {
                if deltas[i].0 == deltas[j].0 {
                    return None;
                }
            }
        }
        let mut staged = *self;
        let pre_root = staged.root();
        let mut legs = [SeatLeg::ZERO; L];
        let mut net = 0i64;
        for (i, (seat_id, delta)) in deltas.into_iter().enumerate() {
            let pre = staged.balance(seat_id)?;
            let post = pre.checked_add(delta)?;
            net = net.checked_add(delta)?;
            if pre < 0 || post < 0 {
                return None;
            }
            let merkle_path = staged.open(seat_id)?;
            legs[i] = SeatLeg {
                seat_id,
                pre,
                delta,
                merkle_path,
            };
            if !staged.set_balance(seat_id, post) {
                return None;
            }
        }
        if net != 0 {
            return None;
        }
        let post_root = staged.root();
        *self = staged;
        Some((pre_root, legs, post_root))
    }
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
/// The turn descriptor `turn_hash` pins: the lineage, its nullifier, and every leg's `(seat_id, pre, delta)`.
pub fn deos_turn_digest(lineage: &Digest, nullifier: &Digest, legs: &[SeatLeg]) -> Digest {
    let mut s = customized(b"obend.deos.turn.v1");
    s.absorb(lineage);
    s.absorb(nullifier);
    s.left(legs.len() as u64);
    for l in legs {
        s.absorb(&l.seat_id.to_be_bytes());
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
    pub pre_seat_root: Digest,
    pub pre_canopy_root: Digest,
    pub post_canopy_root: Digest,
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
    let legs_len = SEAT_STATE_ROOTS_WIRE_LEN.checked_add(L.checked_mul(SEAT_LEG_WIRE_LEN)?)?;
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
    put(&r.pre_seat_root)?;
    put(&r.pre_canopy_root)?;
    put(&r.post_canopy_root)?;
    for leg in r.legs {
        put(&leg.seat_id.to_be_bytes())?;
        put(&leg.pre.to_be_bytes())?;
        put(&leg.delta.to_be_bytes())?;
        for node in leg.merkle_path {
            put(&node)?;
        }
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
    let expected_legs_len =
        SEAT_STATE_ROOTS_WIRE_LEN.checked_add(L.checked_mul(SEAT_LEG_WIRE_LEN)?)?;
    if w.hops.len() != H.checked_mul(72)? || w.legs.len() != expected_legs_len {
        return None;
    }
    let grant = hop(w.grant)?;
    let mut hops = [grant; H];
    for (i, h) in hops.iter_mut().enumerate() {
        let start = i.checked_mul(72)?;
        *h = hop(w.hops.get(start..start.checked_add(72)?)?)?;
    }
    let pre_seat_root: Digest = w.legs.get(0..32)?.try_into().ok()?;
    let pre_canopy_root: Digest = w.legs.get(32..64)?.try_into().ok()?;
    let post_canopy_root: Digest = w.legs.get(64..96)?.try_into().ok()?;
    let legs_body = w.legs.get(SEAT_STATE_ROOTS_WIRE_LEN..)?;
    let mut legs = [SeatLeg::ZERO; L];
    for (i, leg) in legs.iter_mut().enumerate() {
        let start = i.checked_mul(SEAT_LEG_WIRE_LEN)?;
        let chunk = legs_body.get(start..start.checked_add(SEAT_LEG_WIRE_LEN)?)?;
        leg.seat_id = u64::from_be_bytes(chunk.get(0..8)?.try_into().ok()?);
        leg.pre = i64::from_be_bytes(chunk.get(8..16)?.try_into().ok()?);
        leg.delta = i64::from_be_bytes(chunk.get(16..24)?.try_into().ok()?);
        for (lvl, node) in leg.merkle_path.iter_mut().enumerate() {
            let off = 24 + lvl * 32;
            *node = chunk.get(off..off + 32)?.try_into().ok()?;
        }
    }
    Some(DeosTurnReceipt {
        fs_challenge0: w.challenge.try_into().ok()?,
        grant,
        hops,
        nullifier: w.nullifier.try_into().ok()?,
        pre_seat_root,
        pre_canopy_root,
        post_canopy_root,
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
    SeatStateRoot,
    CanopyOpening,
    PikkuFold,
    ClaimMismatch,
}
/// The relation of a state-advancing DeOS turn, checked without a heap. `cap_root`
/// pins the root grant, `revoked_root` pins the nullifier window, `turn_hash` pins the
/// turn descriptor, and `pre_state_root` / `post_state_root` pin the 256-bit composite
/// `(seat_merkle_root, canopy_root)` transition across authenticated `SeatLeg`s.
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
        if !seats_distinct_and_valid(&r.legs) {
            return Err(SeatStateRoot);
        }
        if deos_state_root(&r.pre_seat_root, &r.pre_canopy_root) != pi.pre_state_root {
            return Err(SeatStateRoot);
        }
        let post_seat_root = apply_seat_legs_merkle(&r.pre_seat_root, &r.legs).ok_or(SeatStateRoot)?;
        if deos_state_root(&post_seat_root, &r.post_canopy_root) != pi.post_state_root {
            return Err(SeatStateRoot);
        }
        tr.absorb(b"deos.pre_seat", &r.pre_seat_root);
        tr.absorb(b"deos.pre_canopy", &r.pre_canopy_root);
        tr.absorb(b"deos.post_seat", &post_seat_root);
        if !self.proofs.canopy(&mut tr, &r.post_canopy_root, p) {
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

    fn raw_leg(seat_id: u64, pre: i64, delta: i64) -> SeatLeg {
        SeatLeg {
            seat_id,
            pre,
            delta,
            merkle_path: [[0; 32]; SEAT_MERKLE_DEPTH],
        }
    }

    fn default_tree() -> SeatMerkleTree {
        let mut tree = SeatMerkleTree::new();
        assert!(tree.set_balance(0, 100));
        assert!(tree.set_balance(1, 5));
        assert!(tree.set_balance(2, 50));
        tree
    }

    const DEFAULT_DELTAS: [(u64, i64); 2] = [(0, -40), (1, 40)];

    type CanopyFixture = (
        [Goldilocks; 2],
        [[Goldilocks; 1]; 8],
        [Digest; 8],
        [Digest; 4],
        Digest,
    );

    fn canopy_fixture() -> CanopyFixture {
        let coeff = [Goldilocks::new(11), Goldilocks::new(5)];
        let rows: [[Goldilocks; 1]; 8] =
            core::array::from_fn(|i| [eval(&coeff, Goldilocks::new(i as u64))]);
        let leaves: [Digest; 8] = core::array::from_fn(|i| canopy_leaf(&rows[i]));
        let cap: [Digest; 4] =
            core::array::from_fn(|i| canopy_parent(&leaves[2 * i], &leaves[2 * i + 1]));
        let root = canopy_root(3, 2, &cap);
        (coeff, rows, leaves, cap, root)
    }

    /// Honest prover over a `SeatMerkleTree`, advancing `deltas` sequentially.
    fn prove_from_tree(
        tree: &mut SeatMerkleTree,
        deltas: [(u64, i64); 2],
        hop_rights: u64,
        spent: &[Digest],
        skew: u64,
        previous: Option<&FullPinnedPublicInputs>,
        pre_canopy_root: Digest,
    ) -> (Verifier, SovereignTurnBundle<Receipt>) {
        let (pre_seat_root, legs, post_seat_root) = tree
            .apply_settlement(deltas)
            .expect("honest test deltas must conserve and address distinct seats");
        prove_raw(
            pre_seat_root,
            post_seat_root,
            pre_canopy_root,
            legs,
            hop_rights,
            spent,
            skew,
            previous,
        )
    }

    /// Low-level prover allowing adversarial tests to supply arbitrary `(pre_seat_root, post_seat_root, legs)`
    /// while computing the Fiat-Shamir transcript, Canopy opening, and PikkuFold witness honestly.
    #[allow(clippy::too_many_arguments)]
    fn prove_raw(
        pre_seat_root: Digest,
        post_seat_root: Digest,
        pre_canopy_root: Digest,
        legs: [SeatLeg; 2],
        hop_rights: u64,
        spent: &[Digest],
        skew: u64,
        previous: Option<&FullPinnedPublicInputs>,
    ) -> (Verifier, SovereignTurnBundle<Receipt>) {
        let (coeff, rows, leaves, cap, post_canopy_root) = canopy_fixture();
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
        let computed_pre_state = deos_state_root(&pre_seat_root, &pre_canopy_root);
        let computed_post_state = deos_state_root(&post_seat_root, &post_canopy_root);
        let p = FullPinnedPublicInputs {
            circuit_desc_digest: [0x11; 32],
            actor_vk_digest: [0x22; 32],
            pre_state_root: previous.map_or(computed_pre_state, |prev| prev.post_state_root),
            post_state_root: computed_post_state,
            cap_root: deos_lineage(&grant, &[]).unwrap(),
            revoked_root: window.root(),
            height: previous.map_or(1, |prev| prev.height.checked_add(1).unwrap()),
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
        tr.absorb(b"deos.pre_seat", &pre_seat_root);
        tr.absorb(b"deos.pre_canopy", &pre_canopy_root);
        tr.absorb(b"deos.post_seat", &post_seat_root);
        tr.absorb(b"canopy.root", &post_canopy_root);
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
            pre_seat_root,
            pre_canopy_root,
            post_canopy_root,
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

    fn prove(
        deltas: [(u64, i64); 2],
        hop_rights: u64,
        spent: &[Digest],
        skew: u64,
    ) -> (Verifier, SovereignTurnBundle<Receipt>) {
        let mut tree = default_tree();
        prove_from_tree(&mut tree, deltas, hop_rights, spent, skew, None, [0x33; 32])
    }

    fn verdict(v: &Verifier, b: &SovereignTurnBundle<Receipt>) -> Result<(), DeosRefusal> {
        let r = v.check(&b.public_inputs, &b.challenge0, &b.receipt);
        assert_eq!(verify_cipherclerk(v, b), r.is_ok());
        r
    }

    #[test]
    fn honest_turn_is_accepted_and_settles_through_the_pd() {
        let (v, b) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
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
    fn fabricated_sum_zero_legs_and_duplicate_or_tampered_merkle_legs_are_refused() {
        // Setup committed tree: seat 0 = 100, seat 1 = 5, seat 2 = 50, seat 9 = 0, seat 10 = 0.
        let tree = default_tree();
        let pre_seat_root = tree.root();

        // 1. Adversarial sum-zero legs claiming seat 9 has 10_000_000 and transfers 40 to seat 10
        //    (passes `seat_conserved`, valid transcript, valid Canopy+PikkuFold, valid lineage).
        let forged_legs = [
            SeatLeg {
                seat_id: 9,
                pre: 10_000_000,
                delta: -40,
                merkle_path: tree.open(9).unwrap(),
            },
            SeatLeg {
                seat_id: 10,
                pre: 0,
                delta: 40,
                merkle_path: tree.open(10).unwrap(),
            },
        ];
        assert!(seat_conserved(&forged_legs));
        let fake_post_seat =
            compute_seat_merkle_root(10, 40, &forged_legs[1].merkle_path).unwrap();
        let (v, forged_bundle) = prove_raw(
            pre_seat_root,
            fake_post_seat,
            [0x33; 32],
            forged_legs,
            0b011,
            &[],
            0,
            None,
        );
        assert_eq!(verdict(&v, &forged_bundle), Err(SeatStateRoot));

        // 2. Honest pre-state openings, but post_seat_root left unchanged (omitting balance debit!).
        let mut t2 = default_tree();
        let (_, honest_legs, _honest_post) = t2.apply_settlement(DEFAULT_DELTAS).unwrap();
        let (v_stale_post, stale_post_bundle) = prove_raw(
            pre_seat_root,
            pre_seat_root,
            [0x33; 32],
            honest_legs,
            0b011,
            &[],
            0,
            None,
        );
        assert_eq!(verdict(&v_stale_post, &stale_post_bundle), Err(SeatStateRoot));

        // 3. Duplicate `seat_id` in the same turn (seat 0 listed twice with delta 0, 0).
        let dup_path = tree.open(0).unwrap();
        let dup_legs = [
            SeatLeg {
                seat_id: 0,
                pre: 100,
                delta: 0,
                merkle_path: dup_path,
            },
            SeatLeg {
                seat_id: 0,
                pre: 100,
                delta: 0,
                merkle_path: dup_path,
            },
        ];
        assert!(seat_conserved(&dup_legs));
        let (v_dup, dup_bundle) = prove_raw(
            pre_seat_root,
            pre_seat_root,
            [0x33; 32],
            dup_legs,
            0b011,
            &[],
            0,
            None,
        );
        assert_eq!(verdict(&v_dup, &dup_bundle), Err(SeatStateRoot));

        // 4. Out-of-range `seat_id >= SEAT_TABLE_LEN`.
        let mut oob_legs = honest_legs;
        oob_legs[1].seat_id = SEAT_TABLE_LEN as u64;
        oob_legs[0].delta = 0;
        oob_legs[1].delta = 0;
        let (v_oob, oob_bundle) = prove_raw(
            pre_seat_root,
            pre_seat_root,
            [0x33; 32],
            oob_legs,
            0b011,
            &[],
            0,
            None,
        );
        assert_eq!(verdict(&v_oob, &oob_bundle), Err(SeatStateRoot));

        // 5. Leg 1 uses pre-turn Merkle sibling instead of sequential post-leg-0 Merkle sibling!
        let non_seq_legs = [
            SeatLeg {
                seat_id: 0,
                pre: 100,
                delta: -40,
                merkle_path: tree.open(0).unwrap(),
            },
            SeatLeg {
                seat_id: 1,
                pre: 5,
                delta: 40,
                // Stale sibling leaf (seat 0 = 100 instead of updated seat 0 = 60)!
                merkle_path: tree.open(1).unwrap(),
            },
        ];
        let (_, _, honest_post_root) = default_tree().apply_settlement(DEFAULT_DELTAS).unwrap();
        let (v_nonseq, nonseq_bundle) = prove_raw(
            pre_seat_root,
            honest_post_root,
            [0x33; 32],
            non_seq_legs,
            0b011,
            &[],
            0,
            None,
        );
        assert_eq!(verdict(&v_nonseq, &nonseq_bundle), Err(SeatStateRoot));
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
    fn lean_typed_deos_wire_envelope_and_merkle_seat_roundtrip() {
        // Exact six-field wire vector from Sel4MicrokitKernelTest.lean (`typedWireVector`).
        let expected_wire: &[u8] = &[
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
        let parsed_wire = decode_turn_wire(expected_wire).unwrap();
        let mut wire_out = [0u8; 256];
        assert_eq!(encode_turn_wire(parsed_wire, &mut wire_out), Some(expected_wire));

        // Full Merkle-authenticated `DeosTurnReceipt` roundtrip.
        let mut tree = default_tree();
        let (pre_seat_root, legs, _post_seat_root) = tree.apply_settlement(DEFAULT_DELTAS).unwrap();
        let receipt = DeosTurnReceipt {
            fs_challenge0: [0x12; 32],
            grant: BiscuitHop {
                rights: 7,
                holder: [7; 32],
                channel: [8; 32],
            },
            hops: [],
            nullifier: [0xab; 32],
            pre_seat_root,
            pre_canopy_root: [0x33; 32],
            post_canopy_root: [0x44; 32],
            legs,
            proof: (0x56u8, 0x78u8),
        };
        let mut out = [0; 1024];
        let encoded = encode_turn_receipt(&receipt, &[0x56, 0x78], &mut out).unwrap();
        let decoded = decode_turn_receipt::<0, 2, _>(encoded, |p| {
            if let [a, b] = p {
                Some((*a, *b))
            } else {
                None
            }
        })
        .unwrap();
        assert_eq!(decoded.pre_seat_root, receipt.pre_seat_root);
        assert_eq!(decoded.pre_canopy_root, receipt.pre_canopy_root);
        assert_eq!(decoded.post_canopy_root, receipt.post_canopy_root);
        assert_eq!(decoded.legs, legs);
        assert_eq!(decoded.grant, receipt.grant);
        assert_eq!(decoded.proof, receipt.proof);
    }

    #[test]
    fn typed_wire_roundtrip_rejects_partial_hops_and_legs() {
        let (_, b) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
        let r = DeosTurnReceipt {
            fs_challenge0: b.receipt.fs_challenge0,
            grant: b.receipt.grant,
            hops: b.receipt.hops,
            nullifier: b.receipt.nullifier,
            pre_seat_root: b.receipt.pre_seat_root,
            pre_canopy_root: b.receipt.pre_canopy_root,
            post_canopy_root: b.receipt.post_canopy_root,
            legs: b.receipt.legs,
            proof: 42u8,
        };
        let mut out = [0; 1024];
        let bytes = encode_turn_receipt(&r, &[42], &mut out).unwrap();
        let proof = |bs: &[u8]| if let [v] = bs { Some(*v) } else { None };
        let decoded = decode_turn_receipt::<1, 2, _>(bytes, proof).unwrap();
        assert_eq!(decoded.fs_challenge0, r.fs_challenge0);
        assert_eq!(decoded.grant, r.grant);
        assert_eq!(decoded.hops, r.hops);
        assert_eq!(decoded.nullifier, r.nullifier);
        assert_eq!(decoded.pre_seat_root, r.pre_seat_root);
        assert_eq!(decoded.pre_canopy_root, r.pre_canopy_root);
        assert_eq!(decoded.post_canopy_root, r.post_canopy_root);
        assert_eq!(decoded.legs, r.legs);
        assert_eq!(decoded.proof, r.proof);
        let w = decode_turn_wire(bytes).unwrap();
        for bad in [
            DeosTurnWire {
                hops: &w.hops[..71],
                ..w
            },
            DeosTurnWire {
                legs: &w.legs[..w.legs.len() - 1],
                ..w
            },
            DeosTurnWire {
                legs: &w.legs[..95],
                ..w
            },
            DeosTurnWire {
                nullifier: &w.nullifier[..31],
                ..w
            },
        ] {
            let mut bad_bytes = [0; 1024];
            let encoded = encode_turn_wire(bad, &mut bad_bytes).unwrap();
            assert!(decode_turn_receipt::<1, 2, _>(encoded, proof).is_none());
        }
    }

    #[test]
    fn same_drain_replay_is_quarantined() {
        let mut tree = default_tree();
        let (v, first) =
            prove_from_tree(&mut tree, DEFAULT_DELTAS, 0b011, &[], 0, None, [0x33; 32]);
        // Valid height, updated Merkle seat tree, and cryptographic transcript; stale revocation root & replayed hop.
        // Without commit_turn both independently valid relations against `v` would be accepted.
        let (_, second) = prove_from_tree(
            &mut tree,
            [(0, -20), (1, 20)],
            0b011,
            &[],
            0,
            Some(&first.public_inputs),
            first.receipt.post_canopy_root,
        );
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
        let mut tree = default_tree();
        let (v, first) =
            prove_from_tree(&mut tree, DEFAULT_DELTAS, 0b011, &[], 0, None, [0x33; 32]);
        // Turn 2 starts from Turn 1's updated balances (seat 0 = 60, seat 1 = 45, seat 2 = 50)
        // and Turn 1's post_canopy_root.
        let (_, second) = prove_from_tree(
            &mut tree,
            [(0, -15), (2, 15)],
            0b001,
            &[first.receipt.nullifier],
            0,
            Some(&first.public_inputs),
            first.receipt.post_canopy_root,
        );
        assert_eq!(tree.balance(0), Some(45));
        assert_eq!(tree.balance(1), Some(45));
        assert_eq!(tree.balance(2), Some(65));
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
        assert_eq!(pd.committed_root, second.public_inputs.post_state_root);
        assert!(pd.verifier.spent.contains(&first.receipt.nullifier));
        assert!(pd.verifier.spent.contains(&second.receipt.nullifier));
    }

    #[test]
    fn full_window_quarantines_before_state_commit() {
        let (v, b) = prove(
            DEFAULT_DELTAS,
            0b011,
            &[[1; 32], [2; 32], [3; 32], [4; 32]],
            0,
        );
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
        let (_, honest) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
        // The prover rebuilds everything against the window that already holds its nullifier.
        let (v, b) = prove(
            DEFAULT_DELTAS,
            0b011,
            &[[1; 32], honest.receipt.nullifier],
            0,
        );
        assert_eq!(b.receipt.nullifier, honest.receipt.nullifier);
        assert_eq!(verdict(&v, &b), Err(ReplayedNullifier));
        // An unrelated spent nullifier does not refuse the turn.
        let (v, b) = prove(DEFAULT_DELTAS, 0b011, &[[1; 32], [2; 32]], 0);
        assert_eq!(verdict(&v, &b), Ok(()));
        // A full window refuses to grow, and a stale window is not the instance's.
        let mut full = NullifierWindow::<2>::new();
        assert!(full.insert([1; 32]) && full.insert([2; 32]) && !full.insert([3; 32]));
        let (mut v, b) = prove(DEFAULT_DELTAS, 0b011, &[[1; 32]], 0);
        v.spent = NullifierWindow::new();
        assert_eq!(verdict(&v, &b), Err(Instance));
    }

    #[test]
    fn unbalanced_seat_is_refused() {
        let root = default_tree().root();
        for legs in [
            [raw_leg(0, 100, -40), raw_leg(1, 5, 41)],          // net mint
            [raw_leg(0, 100, -41), raw_leg(1, 5, 40)],          // net burn
            [raw_leg(0, 10, -11), raw_leg(1, 0, 11)],           // negative post-balance
            [raw_leg(0, -1, 1), raw_leg(1, 1, -1)],             // negative pre-balance
            [raw_leg(0, i64::MAX, 1), raw_leg(1, 5, -1)],       // balance overflow
            [raw_leg(0, 0, i64::MAX), raw_leg(1, 0, i64::MAX)], // net overflow
        ] {
            assert!(!seat_conserved(&legs));
            let (v, b) = prove_raw(root, root, [0x33; 32], legs, 0b011, &[], 0, None);
            assert_eq!(verdict(&v, &b), Err(UnbalancedSeat));
        }
        assert!(seat_conserved(&[raw_leg(0, i64::MAX, 0), raw_leg(1, 0, 0)]) && seat_conserved(&[]));
        // Legs edited after proving no longer hash to the pinned turn descriptor.
        let (v, mut b) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
        b.receipt.legs[1].delta = 41;
        assert_eq!(verdict(&v, &b), Err(Lineage));
    }

    #[test]
    fn unbound_transcript_is_refused() {
        let (v, b) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
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
        let (v, b) = prove(DEFAULT_DELTAS, 0b011, &[], 1);
        assert_eq!(verdict(&v, &b), Err(ClaimMismatch));
        let (v, b) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
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
        let (v, b) = prove(DEFAULT_DELTAS, 0b1111, &[], 0);
        assert_eq!(verdict(&v, &b), Err(Lineage));
        assert_eq!(deos_lineage(&b.receipt.grant, &b.receipt.hops), None);
        let (v, b) = prove(DEFAULT_DELTAS, 0b011, &[], 0);
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
