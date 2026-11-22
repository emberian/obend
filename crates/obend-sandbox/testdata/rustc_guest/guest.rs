#![no_std]
#![feature(core_float_math)]
//! Real `#![no_std]` WebAssembly 1.0 + Sign-Ext + Bulk-Memory Rust Guest (`wasm32-unknown-unknown`).
//!
//! Compiled on `hbox` via:
//! `rustc --edition 2021 --crate-type cdylib -C opt-level=s -C panic=abort --target wasm32-unknown-unknown guest.rs -o rustc_guest.wasm`

use core::arch::wasm32;
use core::f64::math as f64m;
use core::hint::black_box;
use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    wasm32::unreachable()
}

/// FIPS 180-4 SHA-256 `.rodata` round constants (`Data` section active segment).
static SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

static SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

static mut INPUT_SCRATCH: [u8; 512] = [0u8; 512];
static mut LAST_DIGEST: [u32; 8] = [0u32; 8];

#[inline(never)]
fn sha256_compress_block(state: &mut [u32; 8], block: &[u8; 64]) {
    // Allocates 256-byte `w` schedule on the `$__stack_pointer` linear stack!
    let mut w = [0u32; 64];
    for i in 0..16 {
        let j = i * 4;
        w[i] = u32::from_be_bytes([block[j], block[j + 1], block[j + 2], block[j + 3]]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }

    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    let k_table = black_box(&SHA256_K);
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let temp1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(k_table[i])
            .wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let temp2 = s0.wrapping_add(maj);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

#[inline(never)]
fn sha256_compute(msg: &[u8]) -> [u32; 8] {
    let mut state = *black_box(&SHA256_H0);
    let mut block = [0u8; 64];
    let mut offset = 0usize;
    while offset + 64 <= msg.len() {
        // Exercises `memory.copy` (`copy_from_slice`) on stack frame slices!
        block.copy_from_slice(&msg[offset..offset + 64]);
        sha256_compress_block(&mut state, &block);
        offset += 64;
    }

    let rem = msg.len() - offset;
    // Exercises `memory.fill` (`fill(0)`) + `memory.copy`!
    block.fill(0);
    if rem > 0 {
        block[..rem].copy_from_slice(&msg[offset..]);
    }
    block[rem] = 0x80;
    if rem >= 56 {
        sha256_compress_block(&mut state, &block);
        block.fill(0);
    }
    let bit_len = (msg.len() as u64) * 8;
    block[56..64].copy_from_slice(&bit_len.to_be_bytes());
    sha256_compress_block(&mut state, &block);
    state
}

#[no_mangle]
pub extern "C" fn guest_write_input_byte(idx: u32, byte_val: u32) {
    let i = idx as usize;
    unsafe {
        let ptr = core::ptr::addr_of_mut!(INPUT_SCRATCH) as *mut u8;
        if i < 512 {
            ptr.add(i).write(byte_val as u8);
        }
    }
}

#[no_mangle]
pub extern "C" fn guest_sha256_input(len: u32) -> u64 {
    let n = (len as usize).min(512);
    let digest = unsafe {
        let ptr = core::ptr::addr_of!(INPUT_SCRATCH) as *const u8;
        let msg = core::slice::from_raw_parts(ptr, n);
        let d = sha256_compute(msg);
        LAST_DIGEST = d;
        d
    };
    ((digest[0] as u64) << 32) | (digest[1] as u64)
}

#[no_mangle]
pub extern "C" fn guest_sha256_seeded(seed: u64, len: u32) -> u64 {
    let n = (len as usize).min(320);
    let mut local_msg = [0u8; 320];
    let mut z = seed;
    for slot in local_msg.iter_mut().take(n) {
        z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut x = z;
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^= x >> 31;
        *slot = x as u8;
    }
    let digest = sha256_compute(&local_msg[..n]);
    unsafe {
        LAST_DIGEST = digest;
    }
    ((digest[0] as u64) << 32) | (digest[1] as u64)
}

#[no_mangle]
pub extern "C" fn guest_read_digest_word(word_idx: u32) -> u32 {
    let i = (word_idx as usize) & 7;
    unsafe { LAST_DIGEST[i] }
}

// --- Trait-object & fn-pointer `call_indirect` dynamic dispatch ---

trait MixStage: Sync {
    fn step(&self, acc: i64, x: u32) -> i64;
    fn tag(&self) -> i32;
}

struct RotXorStage(u32);
struct SignExtDivStage(i32);
struct BitCountStage(u64);

impl MixStage for RotXorStage {
    #[inline(never)]
    fn step(&self, acc: i64, x: u32) -> i64 {
        let r = (acc as u64).rotate_left((x ^ self.0) & 63) as i64;
        r ^ (i64::from(x.rotate_right(11)))
    }
    #[inline(never)]
    fn tag(&self) -> i32 {
        0x101
    }
}

impl MixStage for SignExtDivStage {
    #[inline(never)]
    fn step(&self, acc: i64, x: u32) -> i64 {
        // Exercises sign-extension (`i8`/`i16`/`i32` -> `i64`) and signed 64-bit division/remainder!
        let b8 = i64::from((x as u8) as i8);
        let b16 = i64::from(((x >> 8) as u16) as i16);
        let denom = (i64::from(self.0) | 1).wrapping_add((b8 & 7) * 2);
        (acc.wrapping_add(b16 * 257) / denom).wrapping_add(acc % denom)
    }
    #[inline(never)]
    fn tag(&self) -> i32 {
        -0x202
    }
}

impl MixStage for BitCountStage {
    #[inline(never)]
    fn step(&self, acc: i64, x: u32) -> i64 {
        // Exercises `clz`, `ctz`, `popcnt` on both `i32` and `i64`!
        let u = (acc as u64) ^ self.0 ^ u64::from(x);
        let pc = i64::from(u.count_ones())
            + i64::from(u.leading_zeros())
            + i64::from(x.trailing_zeros());
        (acc.wrapping_mul(0x517c_c1b7_2722_0a95)).wrapping_add(pc)
    }
    #[inline(never)]
    fn tag(&self) -> i32 {
        0x303
    }
}

static STAGE_0: RotXorStage = RotXorStage(19);
static STAGE_1: SignExtDivStage = SignExtDivStage(13);
static STAGE_2: BitCountStage = BitCountStage(0xa5a5_5a5a_f0f0_0f0f);

static TRAIT_TABLE: [&dyn MixStage; 3] = [&STAGE_0, &STAGE_1, &STAGE_2];

#[inline(never)]
fn fn_post_a(v: i64) -> i64 {
    v.wrapping_add(0x1234_5678)
}

#[inline(never)]
fn fn_post_b(v: i64) -> i64 {
    v ^ -0x0fed_cba9_8765_4321
}

static FN_PTRS: [fn(i64) -> i64; 2] = [fn_post_a, fn_post_b];

#[no_mangle]
pub extern "C" fn guest_trait_dispatch(mode: u32, rounds: u32, init: i64) -> i64 {
    let stages = black_box(&TRAIT_TABLE[..]);
    let fns = black_box(&FN_PTRS[..]);
    let mut acc = init;
    for r in 0..rounds {
        let idx = ((mode.wrapping_add(r)) as usize) % stages.len();
        let st = stages[idx];
        acc = st.step(acc, r.wrapping_mul(0x9e37_79b9) ^ mode);
        acc = acc.wrapping_add(i64::from(st.tag()));
        let f = fns[(idx + (r as usize)) & 1];
        acc = f(acc);
    }
    acc
}

// --- Deterministic IEEE-754 `f64` & `f32` computation + NaN canonicalization ---

#[no_mangle]
pub extern "C" fn guest_f64_series(x: f64, y: f64, steps: u32) -> f64 {
    let mut acc = x;
    let mut cur = y;
    for k in 1..=steps {
        let kf = k as f64;
        let rad = f64m::sqrt((acc * acc) + (cur * cur) + kf);
        let snapped = f64m::round_ties_even(rad * 8.0) * 0.125;
        let bounded = snapped.clamp(-1_000_000.0, 1_000_000.0);
        acc = (acc * 0.75) + (f64m::floor(bounded) - f64m::ceil(cur * 0.25)) / (kf + 1.0);
        cur = f64m::trunc(cur * -0.5 + (acc.abs()).copysign(cur)) + ((acc as f32) as f64) * 0.0625;
    }
    // Also exercise saturating float->int->float roundtrip (`0xFC` `trunc_sat`)
    let sat_i = (acc * 16.0) as i64;
    acc + (sat_i as f64) * (1.0 / 1024.0)
}

#[no_mangle]
pub extern "C" fn guest_f64_nan_probe(a_bits: u64, b_bits: u64, op_kind: u32) -> u64 {
    let a = black_box(f64::from_bits(a_bits));
    let b = black_box(f64::from_bits(b_bits));
    let out = match op_kind {
        0 => a + b,
        1 => a / b,
        2 => f64m::sqrt(a),
        3 => f64m::floor(a),
        4 => f64::from(a as f32),
        // Pure sign-bit negation (`f64.neg`) preserves payload bits per Wasm 1.0 spec!
        _ => -a,
    };
    black_box(out).to_bits()
}

// --- Bounded heap bump allocation (`memory.grow`) ---

#[no_mangle]
pub extern "C" fn guest_heap_bump_checksum(grow_pages: u32, word_count: u32, seed: u32) -> i64 {
    let prev_pages = wasm32::memory_grow(0, grow_pages as usize);
    if prev_pages == usize::MAX {
        return -1;
    }
    let total_pages = wasm32::memory_size(0);
    let base_addr = prev_pages * 65_536;
    let max_words = ((grow_pages as usize) * 65_536) / 4;
    let n = (word_count as usize).min(max_words);
    let mut word_sum = 0u32;
    unsafe {
        let ptr = base_addr as *mut u32;
        let mut s = seed;
        for i in 0..n {
            s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            ptr.add(i).write(s);
        }
        for i in 0..n {
            word_sum = word_sum.wrapping_add(ptr.add(i).read_volatile());
        }
    }
    (((total_pages as u64) << 32) | u64::from(word_sum)) as i64
}

// --- Adversarial confinement probes (`spin_forever`, `alloc_bomb`, OOB load) ---

#[no_mangle]
pub extern "C" fn spin_forever(seed: u32) -> u32 {
    let mut x = seed | 1;
    loop {
        x = black_box(x.wrapping_mul(1_664_525).wrapping_add(1_013_904_223));
        // Unreachable exit condition so LLVM emits a real infinite backward-branch loop
        if x == 0 && black_box(seed) == 0xffff_fffe && black_box(x) == 1 {
            return x;
        }
    }
}

#[no_mangle]
pub extern "C" fn alloc_bomb(step_pages: u32) -> i32 {
    let step = (step_pages as usize).max(1);
    let mut acc = 0i32;
    loop {
        let res = wasm32::memory_grow(0, black_box(step));
        if res == usize::MAX {
            return -1;
        }
        acc = acc.wrapping_add(res as i32);
        if black_box(acc) == i32::MIN && step == usize::MAX {
            return acc;
        }
    }
}

#[no_mangle]
pub extern "C" fn guest_oob_load(addr: u32) -> u32 {
    // Use 1-byte aligned `u8` volatile read (`i32.load8_u`) so arbitrary `addr` (including `u32::MAX`)
    // never violates Rust pointer alignment preconditions prior to Wasm bounds trapping.
    unsafe { u32::from((addr as *const u8).read_volatile()) }
}
