#![no_std]
#![forbid(unsafe_op_in_unsafe_fn)]
//! Stack-only verifier components and a transport-independent Microkit PD loop.
//!
//! Canopy shared-cap openings and PikkuFold projection/fold arithmetic are subprotocols,
//! not a complete PCS, lattice commitment scheme, or arbitrary-computation SNARK.
//! `RelationVerifier` is the explicit application-proof boundary, with three
//! implementations: `IdentityRelation` (canonical no-op transitions only),
//! `CanopyPikkuRelation` (the two subprotocols over one transcript), and
//! `DeosTurnRelationVerifier` (module `deos`), which adds what a state-advancing
//! DeOS turn needs: instance-bound Fiat-Shamir, a `ZkBiscuit` attenuation lineage
//! with a nullifier checked against a fixed window, signed `Seat` conservation, and
//! the binding of the Canopy opening to the PikkuFold claim. It checks those
//! relations over the receipt it is given; it is not a succinct argument for hidden
//! state. Do not install an unchecked implementation for private turns. No
//! binary-size or seL4 deployment claim follows from host tests of this library.

#[cfg(test)]
extern crate std;

use core::sync::atomic::{AtomicUsize, Ordering};
use core::{cell::UnsafeCell, marker::PhantomData, mem::MaybeUninit};

mod deos;
pub use deos::*;

pub type Digest = [u8; 32];
const RATE: usize = 136;
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
const ROT: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

pub fn keccak_f1600(a: &mut [u64; 25]) {
    for rc in RC {
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        }
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                a[x + 5 * y] ^= d;
            }
        }
        let mut b = [0u64; 25];
        for y in 0..5 {
            for x in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = a[x + 5 * y].rotate_left(ROT[x + 5 * y]);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= rc;
    }
}

pub fn left_encode(value: u64, out: &mut [u8; 9]) -> usize {
    let n = ((64 - value.leading_zeros()).max(1) as usize + 7) / 8;
    out[0] = n as u8;
    for i in 0..n {
        out[i + 1] = (value >> (8 * (n - i - 1))) as u8;
    }
    n + 1
}

struct Sponge {
    lanes: [u64; 25],
    pos: usize,
}
impl Sponge {
    fn new() -> Self {
        Self {
            lanes: [0; 25],
            pos: 0,
        }
    }
    fn absorb(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.lanes[self.pos / 8] ^= (b as u64) << (8 * (self.pos % 8));
            self.pos += 1;
            if self.pos == RATE {
                keccak_f1600(&mut self.lanes);
                self.pos = 0;
            }
        }
    }
    fn left(&mut self, n: u64) {
        let mut bytes = [0; 9];
        let len = left_encode(n, &mut bytes);
        self.absorb(&bytes[..len]);
    }
    fn encode_string(&mut self, s: &[u8]) {
        // A Rust slice cannot have a length exceeding isize::MAX; guard the bit conversion.
        self.left(
            u64::try_from(s.len())
                .expect("slice length")
                .checked_mul(8)
                .expect("bit length"),
        );
        self.absorb(s);
    }
    fn finish(mut self, suffix: u8, out: &mut [u8]) {
        self.lanes[self.pos / 8] ^= (suffix as u64) << (8 * (self.pos % 8));
        self.lanes[(RATE - 1) / 8] ^= 0x80u64 << (8 * ((RATE - 1) % 8));
        keccak_f1600(&mut self.lanes);
        self.pos = 0;
        for b in out {
            if self.pos == RATE {
                keccak_f1600(&mut self.lanes);
                self.pos = 0;
            }
            *b = (self.lanes[self.pos / 8] >> (8 * (self.pos % 8))) as u8;
            self.pos += 1;
        }
    }
    fn digest(self) -> Digest {
        let mut out = [0; 32];
        self.finish(4, &mut out);
        out
    }
}
fn customized(custom: &[u8]) -> Sponge {
    let mut s = Sponge::new();
    if !custom.is_empty() {
        s.left(RATE as u64);
        s.encode_string(&[]);
        s.encode_string(custom);
        while s.pos != 0 {
            s.absorb(&[0]);
        }
    }
    s
}
pub fn cshake256(custom: &[u8], input: &[u8], out: &mut [u8]) {
    let mut s = customized(custom);
    s.absorb(input);
    s.finish(if custom.is_empty() { 0x1f } else { 0x04 }, out);
}
fn hash(custom: &[u8], input: &[u8]) -> Digest {
    let mut out = [0; 32];
    cshake256(custom, input, &mut out);
    out
}
fn leb(mut n: u64, out: &mut [u8; 10]) -> usize {
    let mut i = 0;
    loop {
        out[i] = (n & 127) as u8;
        n >>= 7;
        if n != 0 {
            out[i] |= 128;
        }
        i += 1;
        if n == 0 {
            return i;
        }
    }
}
fn field(s: &mut Sponge, bytes: &[u8]) {
    let mut len = [0; 10];
    let n = leb(bytes.len() as u64, &mut len);
    s.absorb(&len[..n]);
    s.absorb(bytes);
}

pub enum Unseeded {}
pub enum RelationBound {}
pub struct Transcript<P> {
    state: Digest,
    step: u64,
    phase: PhantomData<P>,
}
impl Transcript<Unseeded> {
    pub fn new(seed: &[u8]) -> Self {
        Self {
            state: hash(b"OBEND.CRYPTO.FS.SEED/v1", seed),
            step: 0,
            phase: PhantomData,
        }
    }
    /// ASCII protocol identifiers match Lean's scalar-value LEB128 encoding.
    /// Non-ASCII identifiers are refused rather than silently encoded as UTF-8.
    pub fn bind_relation(
        self,
        protocol: &[u8],
        relation: &[u8],
        io: &[u8],
    ) -> Option<Transcript<RelationBound>> {
        if !protocol.is_ascii() {
            return None;
        }
        let mut s = customized(b"OBEND.CRYPTO.FS.BIND/v1");
        field(&mut s, &self.state);
        field(&mut s, protocol);
        field(&mut s, relation);
        field(&mut s, io);
        let mut state = [0; 32];
        s.finish(4, &mut state);
        Some(Transcript {
            state,
            step: 1,
            phase: PhantomData,
        })
    }
}
impl Transcript<RelationBound> {
    pub fn absorb(&mut self, label: &[u8], msg: &[u8]) {
        let mut s = customized(b"OBEND.CRYPTO.FS.ABSORB/v1");
        field(&mut s, &self.state);
        field(&mut s, label);
        let mut counter = [0; 10];
        let n = leb(self.step, &mut counter);
        let mut len = [0; 10];
        let l = leb((n + msg.len()) as u64, &mut len);
        s.absorb(&len[..l]);
        s.absorb(&counter[..n]);
        s.absorb(msg);
        s.finish(4, &mut self.state);
        self.step = self.step.checked_add(1).expect("transcript exhausted");
    }
    pub fn squeeze(&mut self) -> Digest {
        let mut s = customized(b"OBEND.CRYPTO.FS.SQUEEZE/v1");
        field(&mut s, &self.state);
        let mut counter = [0; 10];
        let n = leb(self.step, &mut counter);
        s.absorb(&counter[..n]);
        let mut out = [0; 32];
        s.finish(4, &mut out);
        let mut s = customized(b"OBEND.CRYPTO.FS.RATCHET/v1");
        field(&mut s, &self.state);
        field(&mut s, &out);
        s.finish(4, &mut self.state);
        self.step = self.step.checked_add(1).expect("transcript exhausted");
        out
    }
    pub fn goldilocks(&mut self) -> Goldilocks {
        let b = self.squeeze();
        Goldilocks::reduce(u128::from_be_bytes(b[..16].try_into().unwrap()))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Goldilocks(u64);
impl Goldilocks {
    pub const P: u64 = 0xffff_ffff_0000_0001;
    const EPS: u64 = 0xffff_ffff;
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const fn new(x: u64) -> Self {
        let (d, borrow) = x.overflowing_sub(Self::P);
        Self((d & 0u64.wrapping_sub(!borrow as u64)) | (x & 0u64.wrapping_sub(borrow as u64)))
    }
    pub fn value(self) -> u64 {
        self.0
    }
    pub fn reduce(x: u128) -> Self {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let (t, borrow) = lo.overflowing_sub(hi >> 32);
        let t = t.wrapping_sub(Self::EPS & 0u64.wrapping_sub(borrow as u64));
        let (t, carry) = t.overflowing_add((hi & Self::EPS) * Self::EPS);
        Self::new(t.wrapping_add(Self::EPS & 0u64.wrapping_sub(carry as u64)))
    }
    pub fn centered_norm(self) -> u64 {
        self.0.min(Self::P - self.0)
    }
}
impl core::ops::Add for Goldilocks {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (s, carry) = self.0.overflowing_add(rhs.0);
        Self::new(s.wrapping_add(Self::EPS & 0u64.wrapping_sub(carry as u64)))
    }
}
impl core::ops::Sub for Goldilocks {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (s, borrow) = self.0.overflowing_sub(rhs.0);
        Self(s.wrapping_sub(Self::EPS & 0u64.wrapping_sub(borrow as u64)))
    }
}
impl core::ops::Mul for Goldilocks {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::reduce(self.0 as u128 * rhs.0 as u128)
    }
}
fn eval(coeffs: &[Goldilocks], x: Goldilocks) -> Goldilocks {
    coeffs
        .iter()
        .rev()
        .fold(Goldilocks::ZERO, |acc, c| acc * x + *c)
}

struct Bytes<const N: usize> {
    data: [u8; N],
    len: usize,
}
impl<const N: usize> Bytes<N> {
    fn new() -> Self {
        Self {
            data: [0; N],
            len: 0,
        }
    }
    fn push(&mut self, bytes: &[u8]) -> Option<()> {
        let end = self.len.checked_add(bytes.len())?;
        self.data.get_mut(self.len..end)?.copy_from_slice(bytes);
        self.len = end;
        Some(())
    }
    fn field(&mut self, bytes: &[u8]) -> Option<()> {
        let mut enc = [0; 10];
        let n = leb(bytes.len() as u64, &mut enc);
        self.push(&enc[..n])?;
        self.push(bytes)
    }
    fn slice(&self) -> &[u8] {
        &self.data[..self.len]
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct FullPinnedPublicInputs {
    pub circuit_desc_digest: Digest,
    pub actor_vk_digest: Digest,
    pub pre_state_root: Digest,
    pub post_state_root: Digest,
    pub cap_root: Digest,
    pub revoked_root: Digest,
    pub height: u64,
    pub turn_hash: Digest,
}
impl FullPinnedPublicInputs {
    fn encoded(&self) -> Bytes<256> {
        let mut a = Bytes::<100>::new();
        let mut b = Bytes::<100>::new();
        let mut c = Bytes::<50>::new();
        a.field(&self.circuit_desc_digest).unwrap();
        a.field(&self.actor_vk_digest).unwrap();
        a.field(&self.pre_state_root).unwrap();
        b.field(&self.post_state_root).unwrap();
        b.field(&self.cap_root).unwrap();
        b.field(&self.revoked_root).unwrap();
        let mut height = [0; 10];
        let n = leb(self.height, &mut height);
        c.field(&height[..n]).unwrap();
        c.field(&self.turn_hash).unwrap();
        c.field(&[]).unwrap();
        let mut out = Bytes::new();
        out.field(a.slice()).unwrap();
        out.field(b.slice()).unwrap();
        out.field(c.slice()).unwrap();
        out
    }
    pub fn transcript(&self) -> Transcript<RelationBound> {
        Transcript::new(&[])
            .bind_relation(
                b"obend.sovereign-turn.v1",
                &self.circuit_desc_digest,
                self.encoded().slice(),
            )
            .unwrap()
    }
}

pub struct CanopyQuery<'a> {
    pub index: usize,
    pub row: &'a [Goldilocks],
    pub path: &'a [Digest],
}
pub struct CanopyBatchOpening<'a> {
    pub depth: u32,
    pub cap_height: u32,
    pub cap: &'a [Digest],
    pub queries: &'a [CanopyQuery<'a>],
    pub iacc: Goldilocks,
}
pub fn canopy_leaf(row: &[Goldilocks]) -> Digest {
    let mut s = customized(b"obend.canopy.leaf.v1");
    s.left(row.len() as u64);
    for x in row {
        s.absorb(&x.0.to_be_bytes());
    }
    s.digest()
}
pub fn canopy_parent(left: &Digest, right: &Digest) -> Digest {
    let mut s = customized(b"obend.canopy.node.v1");
    s.absorb(left);
    s.absorb(right);
    s.digest()
}
pub fn canopy_root(depth: u32, cap_height: u32, cap: &[Digest]) -> Digest {
    let mut s = customized(b"obend.canopy.cap.v1");
    s.absorb(&depth.to_be_bytes());
    s.absorb(&cap_height.to_be_bytes());
    s.left(cap.len() as u64);
    for d in cap {
        s.absorb(d);
    }
    s.digest()
}
/// Counts every invocation, including leaf hashing. Shared-cap root is one cSHAKE.
/// Returns (shared-cap, naive), where naive authenticates each query to a binary root.
pub fn canopy_hash_count(q: usize, depth: u32, t: u32) -> Option<(usize, usize)> {
    if t > depth {
        return None;
    }
    Some((
        q.checked_mul((depth - t) as usize + 1)?.checked_add(1)?,
        q.checked_mul(depth as usize + 1)?,
    ))
}
/// Opens the committed codeword at transcript-selected positions and checks a random
/// linear combination against verifier-owned RS column polynomials. This is not a
/// proximity test for a prover-supplied unknown polynomial.
pub fn verify_canopy(
    tr: &mut Transcript<RelationBound>,
    expected_root: &Digest,
    polynomials: &[&[Goldilocks]],
    proof: &CanopyBatchOpening<'_>,
) -> bool {
    if proof.depth >= usize::BITS
        || proof.cap_height > proof.depth
        || proof.queries.is_empty()
        || polynomials.is_empty()
        || proof.cap.len() != (1usize << proof.cap_height)
    {
        return false;
    }
    if canopy_root(proof.depth, proof.cap_height, proof.cap) != *expected_root {
        return false;
    }
    tr.absorb(b"canopy.root", expected_root);
    let alpha = tr.goldilocks();
    let rho = tr.goldilocks();
    let mut acc = Goldilocks::ZERO;
    let mut expected = Goldilocks::ZERO;
    let mut weight = Goldilocks::ONE;
    let bottom = (proof.depth - proof.cap_height) as usize;
    for q in proof.queries {
        let challenge = tr.squeeze();
        let sample = u64::from_be_bytes(challenge[..8].try_into().unwrap()) as usize
            & ((1usize << proof.depth) - 1);
        if q.index != sample || q.row.len() != polynomials.len() || q.path.len() != bottom {
            return false;
        }
        let mut h = canopy_leaf(q.row);
        let mut index = q.index;
        for sibling in q.path {
            h = if index & 1 == 0 {
                canopy_parent(&h, sibling)
            } else {
                canopy_parent(sibling, &h)
            };
            index >>= 1;
        }
        if proof.cap.get(index) != Some(&h) {
            return false;
        }
        let x = Goldilocks::new(q.index as u64);
        let mut a = Goldilocks::ONE;
        let mut actual = Goldilocks::ZERO;
        let mut predicted = Goldilocks::ZERO;
        for (value, coeffs) in q.row.iter().zip(polynomials) {
            actual = actual + a * *value;
            predicted = predicted + a * eval(coeffs, x);
            a = a * alpha;
        }
        acc = acc + weight * actual;
        expected = expected + weight * predicted;
        weight = weight * rho;
    }
    acc == expected && proof.iacc == acc
}

/// A rank-one Kronecker projection: each layer contracts triples using {-1,0,+1}.
/// Scratch starts as the input vector and is shortened logically after each layer.
pub fn kronecker_ternary(scratch: &mut [Goldilocks], factors: &[[i8; 3]]) -> Option<Goldilocks> {
    let mut len = scratch.len();
    for factor in factors {
        if len == 0 || len % 3 != 0 || factor.iter().any(|x| !(-1..=1).contains(x)) {
            return None;
        }
        for i in 0..len / 3 {
            let mut out = Goldilocks::ZERO;
            for j in 0..3 {
                match factor[j] {
                    -1 => out = out - scratch[3 * i + j],
                    0 => (),
                    1 => out = out + scratch[3 * i + j],
                    _ => return None,
                }
            }
            scratch[i] = out;
        }
        len /= 3;
    }
    if len == 1 {
        Some(scratch[0])
    } else {
        None
    }
}
fn witness_hash(w: &[Goldilocks]) -> Digest {
    canopy_leaf(w)
}
pub fn pikku_challenge(
    tr: &mut Transcript<RelationBound>,
    w1: &[Goldilocks],
    w2: &[Goldilocks],
) -> Goldilocks {
    tr.absorb(b"pikku.w1", &witness_hash(w1));
    tr.absorb(b"pikku.w2", &witness_hash(w2));
    tr.goldilocks()
}
pub fn verify_pikku(
    tr: &mut Transcript<RelationBound>,
    w1: &[Goldilocks],
    w2: &[Goldilocks],
    folded: &[Goldilocks],
    beta: u64,
) -> bool {
    if w1.is_empty() || w1.len() != w2.len() || w1.len() != folded.len() || beta > Goldilocks::P / 2
    {
        return false;
    }
    let c = pikku_challenge(tr, w1, w2);
    w1.iter().zip(w2).zip(folded).all(|((a, b), f)| {
        a.centered_norm() <= beta
            && b.centered_norm() <= beta
            && f.centered_norm() <= beta
            && *f == *a + c * *b
    })
}

/// Storage only. Safe access requires unique Producer/Consumer handles, created by
/// an exclusive split. No Copy/Clone endpoints and no shared-reference push/pop API.
#[repr(C, align(64))]
pub struct IpcRing<T: Copy, const N: usize> {
    write: AtomicUsize,
    _write_pad: [u8; 64 - core::mem::size_of::<usize>()],
    read: AtomicUsize,
    _read_pad: [u8; 64 - core::mem::size_of::<usize>()],
    slots: [UnsafeCell<MaybeUninit<T>>; N],
}
// SAFETY: data slots are accessed only by unique endpoints; Release/Acquire publishes
// initialization and prevents overwrite until the consumer has copied the value.
unsafe impl<T: Copy + Send, const N: usize> Sync for IpcRing<T, N> {}
impl<T: Copy, const N: usize> Default for IpcRing<T, N> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Copy, const N: usize> IpcRing<T, N> {
    pub const fn new() -> Self {
        Self {
            write: AtomicUsize::new(0),
            _write_pad: [0; 64 - core::mem::size_of::<usize>()],
            read: AtomicUsize::new(0),
            _read_pad: [0; 64 - core::mem::size_of::<usize>()],
            slots: [const { UnsafeCell::new(MaybeUninit::uninit()) }; N],
        }
    }
    pub fn split(&mut self) -> (Producer<'_, T, N>, Consumer<'_, T, N>) {
        assert!(N.is_power_of_two() && N <= isize::MAX as usize);
        (Producer { ring: self }, Consumer { ring: self })
    }
}
pub struct Producer<'a, T: Copy, const N: usize> {
    ring: &'a IpcRing<T, N>,
}
pub struct Consumer<'a, T: Copy, const N: usize> {
    ring: &'a IpcRing<T, N>,
}
impl<T: Copy, const N: usize> Producer<'_, T, N> {
    pub fn push(&mut self, value: T) -> Result<(), T> {
        let write = self.ring.write.load(Ordering::Relaxed);
        let read = self.ring.read.load(Ordering::Acquire);
        if write.wrapping_sub(read) >= N {
            return Err(value);
        }
        // SAFETY: this endpoint exclusively owns the unoccupied write slot.
        unsafe {
            (*self.ring.slots[write % N].get()).write(value);
        }
        self.ring
            .write
            .store(write.wrapping_add(1), Ordering::Release);
        Ok(())
    }
}
impl<T: Copy, const N: usize> Consumer<'_, T, N> {
    pub fn pop(&mut self) -> Option<T> {
        let read = self.ring.read.load(Ordering::Relaxed);
        if read == self.ring.write.load(Ordering::Acquire) {
            return None;
        }
        // SAFETY: producer published this initialized slot and cannot overwrite it
        // until the subsequent Release advances read. T is Copy, so no destructor races.
        let value = unsafe { (*self.ring.slots[read % N].get()).assume_init_read() };
        self.ring
            .read
            .store(read.wrapping_add(1), Ordering::Release);
        Some(value)
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct SovereignTurnBundle<R: Copy> {
    pub public_inputs: FullPinnedPublicInputs,
    pub challenge0: Digest,
    pub effect_vk_digest: Digest,
    pub last_row_gate_ok: bool,
    pub receipt: R,
}
/// Implementations must establish the complete committed relation, including roots,
/// conservation, authority, revocation, effects and EVERY row. Gate flags below only
/// reject early; they are not a substitute for this check.
pub trait RelationVerifier<R: Copy> {
    fn verify_relation(&self, pi: &FullPinnedPublicInputs, challenge: &Digest, receipt: &R)
        -> bool;
}
pub fn verify_cipherclerk<R: Copy, V: RelationVerifier<R>>(
    v: &V,
    b: &SovereignTurnBundle<R>,
) -> bool {
    if b.public_inputs.revoked_root == [0; 32]
        || !b.last_row_gate_ok
        || b.effect_vk_digest != b.public_inputs.actor_vk_digest
    {
        return false;
    }
    let challenge = b.public_inputs.transcript().squeeze();
    challenge == b.challenge0 && v.verify_relation(&b.public_inputs, &challenge, &b.receipt)
}
/// A complete, intentionally narrow relation: an authenticated no-op changes no state
/// and invokes no capability or custom effect. It needs no private-state witness.
pub struct IdentityRelation {
    pub circuit: Digest,
    pub actor: Digest,
    pub cap: Digest,
    pub revoked: Digest,
}
impl RelationVerifier<()> for IdentityRelation {
    fn verify_relation(&self, p: &FullPinnedPublicInputs, _: &Digest, _: &()) -> bool {
        p.circuit_desc_digest == self.circuit
            && p.actor_vk_digest == self.actor
            && p.cap_root == self.cap
            && p.revoked_root == self.revoked
            && p.pre_state_root == p.post_state_root
            && p.turn_hash == hash(b"obend.identity-turn.v1", &[])
    }
}

/// Fixed-footprint stack/`IpcRing`-storable `Canopy` + `PikkuFold` receipt for
/// sovereign state-advancing turns inside a `no_std` Microkit Protection Domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct CanopyPikkuQuery<const COLS: usize, const BOT: usize> {
    pub index: usize,
    pub row: [Goldilocks; COLS],
    pub path: [Digest; BOT],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct CanopyPikkuReceipt<
    const CAP: usize,
    const Q: usize,
    const BOT: usize,
    const COLS: usize,
    const W: usize,
> {
    pub depth: u32,
    pub cap_height: u32,
    pub cap: [Digest; CAP],
    pub queries: [CanopyPikkuQuery<COLS, BOT>; Q],
    pub iacc: Goldilocks,
    pub w1: [Goldilocks; W],
    pub w2: [Goldilocks; W],
    pub folded: [Goldilocks; W],
    pub claimed_proj: Goldilocks,
}

/// Concrete `Canopy` + `PikkuFold` relation verifier driving `VerifierPd` over `IpcRing`:
/// pins `circuit_desc_digest`, authenticates `post_state_root` as the `Canopy` commitment root,
/// verifies batched `Canopy` Merkle + RS `iacc` openings, verifies `PikkuFold` norm-bounded
/// witness folding, and checks Kronecker ternary linear projection consistency on the folded witness.
pub struct CanopyPikkuRelation<
    const COLS: usize,
    const DEG: usize,
    const LAYERS: usize,
    const W: usize,
> {
    pub circuit: Digest,
    pub polynomials: [[Goldilocks; DEG]; COLS],
    pub kronecker_factors: [[i8; 3]; LAYERS],
    pub beta: u64,
}

impl<const COLS: usize, const DEG: usize, const LAYERS: usize, const W: usize>
    CanopyPikkuRelation<COLS, DEG, LAYERS, W>
{
    /// The batched `Canopy` opening of `r` against `root`, on the caller's transcript.
    fn canopy<const CAP: usize, const Q: usize, const BOT: usize>(
        &self,
        tr: &mut Transcript<RelationBound>,
        root: &Digest,
        r: &CanopyPikkuReceipt<CAP, Q, BOT, COLS, W>,
    ) -> bool {
        let poly_refs: [&[Goldilocks]; COLS] = core::array::from_fn(|i| &self.polynomials[i][..]);
        let query_views: [CanopyQuery<'_>; Q] = core::array::from_fn(|i| CanopyQuery {
            index: r.queries[i].index,
            row: &r.queries[i].row,
            path: &r.queries[i].path,
        });
        let opening = CanopyBatchOpening {
            depth: r.depth,
            cap_height: r.cap_height,
            cap: &r.cap,
            queries: &query_views,
            iacc: r.iacc,
        };
        verify_canopy(tr, root, &poly_refs, &opening)
    }
    /// The Kronecker ternary projection of the folded witness is the claimed one.
    fn projects<const CAP: usize, const Q: usize, const BOT: usize>(
        &self,
        r: &CanopyPikkuReceipt<CAP, Q, BOT, COLS, W>,
    ) -> bool {
        let mut scratch = r.folded;
        kronecker_ternary(&mut scratch, &self.kronecker_factors) == Some(r.claimed_proj)
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
    > RelationVerifier<CanopyPikkuReceipt<CAP, Q, BOT, COLS, W>>
    for CanopyPikkuRelation<COLS, DEG, LAYERS, W>
{
    fn verify_relation(
        &self,
        pi: &FullPinnedPublicInputs,
        challenge0: &Digest,
        r: &CanopyPikkuReceipt<CAP, Q, BOT, COLS, W>,
    ) -> bool {
        if pi.circuit_desc_digest != self.circuit || Q == 0 || COLS == 0 || W == 0 {
            return false;
        }
        let mut tr = pi.transcript();
        tr.squeeze() == *challenge0
            && self.canopy(&mut tr, &pi.post_state_root, r)
            && verify_pikku(&mut tr, &r.w1, &r.w2, &r.folded, self.beta)
            && self.projects(r)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct SettlementVerdict {
    pub height: u64,
    pub accepted: bool,
    pub committed_root: Digest,
}
pub struct VerifierPd<V> {
    pub verifier: V,
    pub committed_root: Digest,
    pub height: u64,
    pending: Option<SettlementVerdict>,
}
impl<V> VerifierPd<V> {
    pub fn new(verifier: V, root: Digest, height: u64) -> Self {
        Self {
            verifier,
            committed_root: root,
            height,
            pending: None,
        }
    }
    /// Backpressure preserves a computed verdict. No inbound item is consumed while
    /// a previous verdict waits for output space. State advances only once per height.
    pub fn drain<R: Copy, const I: usize, const O: usize>(
        &mut self,
        inbound: &mut Consumer<'_, SovereignTurnBundle<R>, I>,
        outbound: &mut Producer<'_, SettlementVerdict, O>,
    ) -> usize
    where
        V: RelationVerifier<R>,
    {
        let mut count = 0;
        loop {
            if let Some(pending) = self.pending.take() {
                if let Err(pending) = outbound.push(pending) {
                    self.pending = Some(pending);
                    return count;
                }
            }
            let Some(b) = inbound.pop() else {
                return count;
            };
            let accepted = self.height.checked_add(1) == Some(b.public_inputs.height)
                && b.public_inputs.pre_state_root == self.committed_root
                && verify_cipherclerk(&self.verifier, &b);
            if accepted {
                self.committed_root = b.public_inputs.post_state_root;
                self.height = b.public_inputs.height;
            }
            self.pending = Some(SettlementVerdict {
                height: b.public_inputs.height,
                accepted,
                committed_root: self.committed_root,
            });
            count += 1;
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PdHealthClaim {
    Healthy(Digest),
    Recovered { epoch: u64, root: Digest },
    Degraded,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Divergence {
    Artifact {
        claimed: PdHealthClaim,
        observed: PdHealthClaim,
    },
    RecoveryNotHolding,
    SilentHeartbeat,
    ForgedVerdict,
}
/// A coherent snapshot must be taken by the Microkit mapping adapter. Plain fields
/// are intentionally not an unsafe claim that racing shared-memory reads are atomic.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct PdArtifactRegion {
    pub committed_root: Digest,
    pub epoch: u64,
    pub ring_epoch: u64,
    pub crc_ok: bool,
    pub heartbeat: u64,
}
impl PdArtifactRegion {
    pub fn probe(&self) -> PdHealthClaim {
        if !self.crc_ok || self.epoch != self.ring_epoch || self.committed_root == [0; 32] {
            PdHealthClaim::Degraded
        } else {
            PdHealthClaim::Recovered {
                epoch: self.epoch,
                root: self.committed_root,
            }
        }
    }
}
pub trait MonitorSubsystem {
    fn probe_divergence(&self) -> Option<Divergence>;
}
pub struct RecoveryMonitor<'a> {
    pub artifact: &'a PdArtifactRegion,
    pub claim: PdHealthClaim,
    pub minimum_heartbeat: u64,
}
impl MonitorSubsystem for RecoveryMonitor<'_> {
    fn probe_divergence(&self) -> Option<Divergence> {
        if self.artifact.heartbeat < self.minimum_heartbeat {
            return Some(Divergence::SilentHeartbeat);
        }
        let observed = self.artifact.probe();
        let agrees = match self.claim {
            PdHealthClaim::Healthy(root) => {
                self.artifact.crc_ok
                    && self.artifact.epoch == self.artifact.ring_epoch
                    && root != [0; 32]
                    && root == self.artifact.committed_root
            }
            other => other == observed,
        };
        if agrees {
            None
        } else {
            Some(Divergence::Artifact {
                claimed: self.claim,
                observed,
            })
        }
    }
}
pub struct MonitorLayer<'a, S: MonitorSubsystem> {
    pub inner: &'a S,
    pub recorded: Option<Divergence>,
}
impl<S: MonitorSubsystem> MonitorSubsystem for MonitorLayer<'_, S> {
    fn probe_divergence(&self) -> Option<Divergence> {
        if self.recorded == self.inner.probe_divergence() {
            None
        } else {
            Some(Divergence::ForgedVerdict)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn hex<const N: usize>(s: &str) -> [u8; N] {
        assert_eq!(s.len(), N * 2);
        let mut out = [0; N];
        for i in 0..N {
            out[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }
    fn pi() -> FullPinnedPublicInputs {
        FullPinnedPublicInputs {
            circuit_desc_digest: [1; 32],
            actor_vk_digest: [2; 32],
            pre_state_root: [3; 32],
            post_state_root: [3; 32],
            cap_root: [4; 32],
            revoked_root: [5; 32],
            height: 1,
            turn_hash: hash(b"obend.identity-turn.v1", &[]),
        }
    }
    fn identity() -> IdentityRelation {
        let p = pi();
        IdentityRelation {
            circuit: p.circuit_desc_digest,
            actor: p.actor_vk_digest,
            cap: p.cap_root,
            revoked: p.revoked_root,
        }
    }
    fn bundle(p: FullPinnedPublicInputs) -> SovereignTurnBundle<()> {
        SovereignTurnBundle {
            public_inputs: p,
            challenge0: p.transcript().squeeze(),
            effect_vk_digest: p.actor_vk_digest,
            last_row_gate_ok: true,
            receipt: (),
        }
    }
    #[test]
    fn nist_keccak_and_cshake_known_answers() {
        let mut a = [0; 25];
        keccak_f1600(&mut a);
        assert_eq!(a[0], 0xf1258f7940e1dde7);
        assert_eq!(a[1], 0x84d5ccf933c0478a);
        assert_eq!(a[24], 0xeaf1ff7b5ceca249);
        assert_eq!(
            hash(b"", b""),
            hex("46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f")
        );
        let mut out = [0; 64];
        cshake256(b"Email Signature", &[0, 1, 2, 3], &mut out);
        assert_eq!(out, hex("d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd164020e2be0560858d9c00c037e34a96937c561a74c412bb4c746469527281c8c"));
        assert_eq!(hash(b"domain", b"x"), hash(b"domain", b"x"));
        assert_ne!(hash(b"domain", b"x"), hash(b"domain2", b"x"));
        assert_ne!(hash(b"a", b"bc"), hash(b"ab", b"c"));
    }
    #[test]
    fn lean_public_input_framing_vector() {
        let p = FullPinnedPublicInputs {
            circuit_desc_digest: [1; 32],
            actor_vk_digest: [2; 32],
            pre_state_root: [3; 32],
            post_state_root: [4; 32],
            cap_root: [5; 32],
            revoked_root: [6; 32],
            height: 300,
            turn_hash: [8; 32],
        };
        let mut expected = std::vec![99, 32];
        expected.extend([1; 32]);
        expected.push(32);
        expected.extend([2; 32]);
        expected.push(32);
        expected.extend([3; 32]);
        expected.extend([99, 32]);
        expected.extend([4; 32]);
        expected.push(32);
        expected.extend([5; 32]);
        expected.push(32);
        expected.extend([6; 32]);
        expected.extend([37, 2, 172, 2, 32]);
        expected.extend([8; 32]);
        expected.push(0);
        assert_eq!(p.encoded().slice(), expected.as_slice());
    }
    #[test]
    fn field_arithmetic_against_integer_reference() {
        let p = Goldilocks::P;
        assert_eq!(Goldilocks::new(p - 1) + Goldilocks::new(2), Goldilocks::ONE);
        let edge = [0, 1, 2, 0xffff_ffff, 0x1_0000_0000, p - 2, p - 1, u64::MAX];
        for &a in &edge {
            for &b in &edge {
                let x = Goldilocks::new(a);
                let y = Goldilocks::new(b);
                assert_eq!((x * y).0, ((x.0 as u128 * y.0 as u128) % p as u128) as u64);
                assert_eq!((x + y).0, ((x.0 as u128 + y.0 as u128) % p as u128) as u64);
                assert_eq!(
                    (x - y).0,
                    ((x.0 as u128 + p as u128 - y.0 as u128) % p as u128) as u64
                );
            }
        }
        let mut n = 0x1234_5678_9abc_def0u64;
        for _ in 0..10000 {
            n ^= n << 13;
            n ^= n >> 7;
            n ^= n << 17;
            let a = Goldilocks::new(n);
            n = n.rotate_left(29).wrapping_mul(0x9e3779b97f4a7c15);
            let b = Goldilocks::new(n);
            let c = Goldilocks::new(n.reverse_bits());
            assert_eq!((a * b).0, ((a.0 as u128 * b.0 as u128) % p as u128) as u64);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            let wide = ((n as u128) << 64) | n.reverse_bits() as u128;
            assert_eq!(Goldilocks::reduce(wide).0, (wide % p as u128) as u64);
        }
    }
    #[test]
    fn all_eight_public_inputs_pin_challenge_zero() {
        let p = pi();
        let original = p.transcript().squeeze();
        for field in 0..8 {
            let mut q = p;
            match field {
                0 => q.circuit_desc_digest[0] ^= 1,
                1 => q.actor_vk_digest[0] ^= 1,
                2 => q.pre_state_root[0] ^= 1,
                3 => q.post_state_root[0] ^= 1,
                4 => q.cap_root[0] ^= 1,
                5 => q.revoked_root[0] ^= 1,
                6 => q.height += 1,
                _ => q.turn_hash[0] ^= 1,
            }
            assert_ne!(original, q.transcript().squeeze());
            let mut b = bundle(q);
            b.challenge0 = original;
            assert!(!verify_cipherclerk(&identity(), &b));
        }
        let mut b = bundle(p);
        b.public_inputs.revoked_root = [0; 32];
        assert!(!verify_cipherclerk(&identity(), &b));
        b = bundle(p);
        b.last_row_gate_ok = false;
        assert!(!verify_cipherclerk(&identity(), &b));
        b = bundle(p);
        b.effect_vk_digest = [9; 32];
        assert!(!verify_cipherclerk(&identity(), &b));
        let mut q = p;
        q.post_state_root = [9; 32];
        assert!(!verify_cipherclerk(&identity(), &bundle(q)));
    }
    #[test]
    fn shared_cap_rs_iacc_and_tampering() {
        const Q: usize = 4;
        let coeff = [Goldilocks::new(7), Goldilocks::new(3)];
        let polys: [&[Goldilocks]; 1] = [&coeff];
        let rows: [[Goldilocks; 1]; 8] =
            core::array::from_fn(|i| [eval(&coeff, Goldilocks::new(i as u64))]);
        let leaves: [Digest; 8] = core::array::from_fn(|i| canopy_leaf(&rows[i]));
        let cap: [Digest; 4] =
            core::array::from_fn(|i| canopy_parent(&leaves[2 * i], &leaves[2 * i + 1]));
        let root = canopy_root(3, 2, &cap);
        let mut tr = pi().transcript();
        tr.absorb(b"canopy.root", &root);
        let _alpha = tr.goldilocks();
        let rho = tr.goldilocks();
        let indexes: [usize; Q] = core::array::from_fn(|_| {
            u64::from_be_bytes(tr.squeeze()[..8].try_into().unwrap()) as usize & 7
        });
        let paths: [[Digest; 1]; Q] = core::array::from_fn(|i| [leaves[indexes[i] ^ 1]]);
        let queries: [CanopyQuery; Q] = core::array::from_fn(|i| CanopyQuery {
            index: indexes[i],
            row: &rows[indexes[i]],
            path: &paths[i],
        });
        let mut iacc = Goldilocks::ZERO;
        let mut w = Goldilocks::ONE;
        for &i in &indexes {
            iacc = iacc + w * rows[i][0];
            w = w * rho;
        }
        let mut proof = CanopyBatchOpening {
            depth: 3,
            cap_height: 2,
            cap: &cap,
            queries: &queries,
            iacc,
        };
        assert!(verify_canopy(&mut pi().transcript(), &root, &polys, &proof));
        let (shared, naive) = canopy_hash_count(Q, 3, 2).unwrap();
        assert_eq!((shared, naive), (9, 16));
        assert!(shared < Q * 3);
        proof.iacc = iacc + Goldilocks::ONE;
        assert!(!verify_canopy(
            &mut pi().transcript(),
            &root,
            &polys,
            &proof
        ));
        proof.iacc = iacc;
        let mut bad_cap = cap;
        bad_cap[0][0] ^= 1;
        proof.cap = &bad_cap;
        assert!(!verify_canopy(
            &mut pi().transcript(),
            &root,
            &polys,
            &proof
        ));
        proof.cap = &cap;
        let mut bad_row = rows[indexes[0]];
        bad_row[0] = bad_row[0] + Goldilocks::ONE;
        let bad_queries: [CanopyQuery; Q] = core::array::from_fn(|i| CanopyQuery {
            index: indexes[i],
            row: if i == 0 { &bad_row } else { &rows[indexes[i]] },
            path: &paths[i],
        });
        proof.queries = &bad_queries;
        assert!(!verify_canopy(
            &mut pi().transcript(),
            &root,
            &polys,
            &proof
        ));
        proof.queries = &queries;
        let wrong_coeff = [Goldilocks::new(8), Goldilocks::new(3)];
        assert!(!verify_canopy(
            &mut pi().transcript(),
            &root,
            &[&wrong_coeff],
            &proof
        ));
        proof.depth = usize::BITS;
        assert!(!verify_canopy(
            &mut pi().transcript(),
            &root,
            &polys,
            &proof
        ));
    }
    #[test]
    fn ternary_projection_norm_and_fold() {
        let mut input = core::array::from_fn::<_, 9, _>(|i| Goldilocks::new(i as u64));
        assert_eq!(
            kronecker_ternary(&mut input, &[[1, 0, -1], [1, -1, 1]]),
            Some(Goldilocks::ZERO - Goldilocks::new(2))
        );
        assert_eq!(
            kronecker_ternary(&mut [Goldilocks::ONE; 3], &[[2, 0, 0]]),
            None
        );
        let w1 = [Goldilocks::new(3), Goldilocks::new(4)];
        let w2 = [Goldilocks::new(2), Goldilocks::new(1)];
        let c = pikku_challenge(&mut pi().transcript(), &w1, &w2);
        let folded = [w1[0] + c * w2[0], w1[1] + c * w2[1]];
        assert!(verify_pikku(
            &mut pi().transcript(),
            &w1,
            &w2,
            &folded,
            Goldilocks::P / 2
        ));
        assert!(!verify_pikku(&mut pi().transcript(), &w1, &w2, &folded, 2));
        let mut bad = folded;
        bad[1] = bad[1] + Goldilocks::ONE;
        assert!(!verify_pikku(
            &mut pi().transcript(),
            &w1,
            &w2,
            &bad,
            Goldilocks::P / 2
        ));
        let mut q = pi();
        q.height += 1;
        assert!(!verify_pikku(
            &mut q.transcript(),
            &w1,
            &w2,
            &folded,
            Goldilocks::P / 2
        ));
    }
    #[test]
    fn pd_ipc_replay_and_backpressure() {
        let mut inbound = IpcRing::<SovereignTurnBundle<()>, 4>::new();
        let mut outbound = IpcRing::<SettlementVerdict, 1>::new();
        let (mut tx, mut rx) = inbound.split();
        let (mut otx, mut orx) = outbound.split();
        let b = bundle(pi());
        assert!(tx.push(b).is_ok());
        assert!(tx.push(b).is_ok());
        let mut pd = VerifierPd::new(identity(), pi().pre_state_root, 0);
        assert_eq!(pd.drain(&mut rx, &mut otx), 2);
        assert_eq!(pd.height, 1);
        assert!(orx.pop().unwrap().accepted);
        assert_eq!(pd.drain(&mut rx, &mut otx), 0);
        assert!(!orx.pop().unwrap().accepted);
        assert!(orx.pop().is_none());
    }
    #[test]
    fn spsc_threaded_and_counter_wrap() {
        let mut ring = IpcRing::<u64, 8>::new();
        ring.write.store(usize::MAX - 3, Ordering::Relaxed);
        ring.read.store(usize::MAX - 3, Ordering::Relaxed);
        let (mut tx, mut rx) = ring.split();
        std::thread::scope(|scope| {
            scope.spawn(move || {
                for i in 0..20000 {
                    while tx.push(i).is_err() {
                        std::thread::yield_now();
                    }
                }
            });
            for i in 0..20000 {
                loop {
                    if let Some(n) = rx.pop() {
                        assert_eq!(n, i);
                        break;
                    }
                    std::thread::yield_now();
                }
            }
        });
    }
    #[test]
    fn recursive_monitor_catches_two_lying_layers() {
        let a = PdArtifactRegion {
            committed_root: [9; 32],
            epoch: 8,
            ring_epoch: 7,
            crc_ok: true,
            heartbeat: 10,
        };
        let pd = RecoveryMonitor {
            artifact: &a,
            claim: PdHealthClaim::Recovered {
                epoch: 8,
                root: [9; 32],
            },
            minimum_heartbeat: 9,
        };
        assert!(pd.probe_divergence().is_some());
        let first = MonitorLayer {
            inner: &pd,
            recorded: None,
        };
        assert_eq!(first.probe_divergence(), Some(Divergence::ForgedVerdict));
        let second = MonitorLayer {
            inner: &first,
            recorded: None,
        };
        assert_eq!(second.probe_divergence(), Some(Divergence::ForgedVerdict));
        let honest = MonitorLayer {
            inner: &second,
            recorded: second.probe_divergence(),
        };
        assert_eq!(honest.probe_divergence(), None);
        let silent = RecoveryMonitor {
            artifact: &a,
            claim: PdHealthClaim::Degraded,
            minimum_heartbeat: 11,
        };
        assert_eq!(silent.probe_divergence(), Some(Divergence::SilentHeartbeat));
    }
    #[test]
    fn verifier_pd_canopy_pikku_end_to_end_ipc() {
        let coeff = [Goldilocks::new(11), Goldilocks::new(5)];
        let rows: [[Goldilocks; 1]; 8] =
            core::array::from_fn(|i| [eval(&coeff, Goldilocks::new(i as u64))]);
        let leaves: [Digest; 8] = core::array::from_fn(|i| canopy_leaf(&rows[i]));
        let cap: [Digest; 4] =
            core::array::from_fn(|i| canopy_parent(&leaves[2 * i], &leaves[2 * i + 1]));
        let post_root = canopy_root(3, 2, &cap);
        let p = FullPinnedPublicInputs {
            circuit_desc_digest: [0x11; 32],
            actor_vk_digest: [0x22; 32],
            pre_state_root: [0x33; 32],
            post_state_root: post_root,
            cap_root: [0x44; 32],
            revoked_root: [0x55; 32],
            height: 1,
            turn_hash: [0x66; 32],
        };
        let mut tr = p.transcript();
        let challenge0 = tr.squeeze();
        tr.absorb(b"canopy.root", &post_root);
        let _alpha = tr.goldilocks();
        let rho = tr.goldilocks();
        let indexes: [usize; 4] = core::array::from_fn(|_| {
            u64::from_be_bytes(tr.squeeze()[..8].try_into().unwrap()) as usize & 7
        });
        let queries: [CanopyPikkuQuery<1, 1>; 4] = core::array::from_fn(|i| CanopyPikkuQuery {
            index: indexes[i],
            row: rows[indexes[i]],
            path: [leaves[indexes[i] ^ 1]],
        });
        let mut iacc = Goldilocks::ZERO;
        let mut weight = Goldilocks::ONE;
        for &idx in &indexes {
            iacc = iacc + weight * rows[idx][0];
            weight = weight * rho;
        }
        let w1 = [Goldilocks::new(4), Goldilocks::new(2), Goldilocks::new(1)];
        let w2 = [Goldilocks::new(3), Goldilocks::new(1), Goldilocks::new(2)];
        let c = pikku_challenge(&mut tr, &w1, &w2);
        let folded: [Goldilocks; 3] = core::array::from_fn(|i| w1[i] + c * w2[i]);
        let factors = [[1i8, -1, 1]];
        let mut scratch = folded;
        let claimed_proj = kronecker_ternary(&mut scratch, &factors).unwrap();
        let receipt = CanopyPikkuReceipt {
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
        let rel = CanopyPikkuRelation {
            circuit: p.circuit_desc_digest,
            polynomials: [coeff],
            kronecker_factors: factors,
            beta: Goldilocks::P / 2,
        };
        let good_bundle = SovereignTurnBundle {
            public_inputs: p,
            challenge0,
            effect_vk_digest: p.actor_vk_digest,
            last_row_gate_ok: true,
            receipt,
        };
        let mut forged_bundle = good_bundle;
        forged_bundle.public_inputs.height = 2;
        forged_bundle.public_inputs.pre_state_root = post_root;
        forged_bundle.challenge0 = forged_bundle.public_inputs.transcript().squeeze();
        forged_bundle.receipt.claimed_proj = claimed_proj + Goldilocks::ONE;

        let mut inbound = IpcRing::<_, 4>::new();
        let mut outbound = IpcRing::<SettlementVerdict, 4>::new();
        let (mut tx, mut rx) = inbound.split();
        let (mut otx, mut orx) = outbound.split();
        assert!(tx.push(good_bundle).is_ok());
        assert!(tx.push(forged_bundle).is_ok());

        let mut pd = VerifierPd::new(rel, p.pre_state_root, 0);
        assert_eq!(pd.drain(&mut rx, &mut otx), 2);
        let v1 = orx.pop().unwrap();
        assert!(v1.accepted);
        assert_eq!(v1.committed_root, post_root);
        let v2 = orx.pop().unwrap();
        assert!(!v2.accepted);
        assert_eq!(pd.committed_root, post_root);
        assert_eq!(pd.height, 1);

        let artifact = PdArtifactRegion {
            committed_root: pd.committed_root,
            epoch: pd.height,
            ring_epoch: pd.height,
            crc_ok: true,
            heartbeat: 5,
        };
        let mon = RecoveryMonitor {
            artifact: &artifact,
            claim: PdHealthClaim::Healthy(post_root),
            minimum_heartbeat: 5,
        };
        assert_eq!(mon.probe_divergence(), None);
    }
}
