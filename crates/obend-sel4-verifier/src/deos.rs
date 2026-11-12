//! The relation of a state-advancing DeOS turn, checked on the stack.
//!
//! `DeosTurnRelationVerifier` implements `RelationVerifier` over a receipt that carries
//! a `ZkBiscuit` attenuation chain, a `Seat` settlement and a `Canopy` + `PikkuFold`
//! proof. Four public inputs pin what the receipt may say: `cap_root` the root grant,
//! `revoked_root` the nullifier window, `turn_hash` the turn descriptor, and
//! `post_state_root` the `Canopy` commitment. `check` names the clause a refused
//! receipt violates. The encodings here are fixed-width and are this crate's own;
//! they are not the byte encodings of the Lean `ZkBiscuit` and `Seat` modules.

use super::*;

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
        self.len += 1;
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
            pre_state_root: [0x33; 32],
            post_state_root: canopy_root(3, 2, &cap),
            cap_root: deos_lineage(&grant, &[]).unwrap(),
            revoked_root: window.root(),
            height: 1,
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
        let before = pd.verifier.spent.root();
        assert!(pd.verifier.spent.insert(b.receipt.nullifier));
        assert!(!pd.verifier.spent.insert(b.receipt.nullifier));
        assert_ne!(pd.verifier.spent.root(), before);
        assert_eq!(
            pd.verifier
                .check(&b.public_inputs, &b.challenge0, &b.receipt),
            Err(Instance)
        );
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
