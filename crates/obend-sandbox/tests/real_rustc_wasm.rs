#![forbid(unsafe_code)]
//! Real `rustc --target wasm32-unknown-unknown` Integration & Confinement Suite (`Wave 10 Tier 2B`).
//!
//! Executes the compiled `testdata/rustc_guest/rustc_guest.wasm` binary produced by `rustc` on
//! `hbox` inside `obend_sandbox::wasm_budget::run_wasm_metered` and verifies bit-identical
//! parity against native Rust across SHA-256 (`.rodata` + `$__stack_pointer` + `memory.copy` /
//! `memory.fill`), `&dyn Trait` + `fn`-pointer `call_indirect`, IEEE-754 `f64` + canonical NaN
//! normalization, bounded `memory.grow` heap bump allocation, and deterministic confinement of
//! `spin_forever` (`OutOfFuel`), `alloc_bomb` (`MemoryLimitExceeded`), `u32::MAX` offset loads,
//! and indirect-call signature mismatches.

use obend_sandbox::sha256;
use obend_sandbox::wasm_budget::{
    run_wasm_metered, WasmCapTier, WasmExecutionBudget, WasmRunError, WasmVal, CANON_F64_NAN_BITS,
    WASM_PAGE_SIZE,
};

const RUSTC_GUEST_WASM: &[u8] = include_bytes!("../testdata/rustc_guest/rustc_guest.wasm");

// --- Native host reference mirrors for exact bit-for-bit parity checks ---

trait HostMixStage: Sync {
    fn step(&self, acc: i64, x: u32) -> i64;
    fn tag(&self) -> i32;
}

struct HostRotXorStage(u32);
struct HostSignExtDivStage(i32);
struct HostBitCountStage(u64);

impl HostMixStage for HostRotXorStage {
    fn step(&self, acc: i64, x: u32) -> i64 {
        let r = (acc as u64).rotate_left((x ^ self.0) & 63) as i64;
        r ^ (i64::from(x.rotate_right(11)))
    }
    fn tag(&self) -> i32 {
        0x101
    }
}

impl HostMixStage for HostSignExtDivStage {
    fn step(&self, acc: i64, x: u32) -> i64 {
        let b8 = i64::from((x as u8) as i8);
        let b16 = i64::from(((x >> 8) as u16) as i16);
        let denom = (i64::from(self.0) | 1).wrapping_add((b8 & 7) * 2);
        (acc.wrapping_add(b16 * 257) / denom).wrapping_add(acc % denom)
    }
    fn tag(&self) -> i32 {
        -0x202
    }
}

impl HostMixStage for HostBitCountStage {
    fn step(&self, acc: i64, x: u32) -> i64 {
        let u = (acc as u64) ^ self.0 ^ u64::from(x);
        let pc = i64::from(u.count_ones())
            + i64::from(u.leading_zeros())
            + i64::from(x.trailing_zeros());
        (acc.wrapping_mul(0x517c_c1b7_2722_0a95)).wrapping_add(pc)
    }
    fn tag(&self) -> i32 {
        0x303
    }
}

fn native_trait_dispatch(mode: u32, rounds: u32, init: i64) -> i64 {
    let s0 = HostRotXorStage(19);
    let s1 = HostSignExtDivStage(13);
    let s2 = HostBitCountStage(0xa5a5_5a5a_f0f0_0f0f);
    let stages: [&dyn HostMixStage; 3] = [&s0, &s1, &s2];
    let fns: [fn(i64) -> i64; 2] = [
        |v| v.wrapping_add(0x1234_5678),
        |v| v ^ -0x0fed_cba9_8765_4321,
    ];
    let mut acc = init;
    for r in 0..rounds {
        let idx = ((mode.wrapping_add(r)) as usize) % stages.len();
        let st = stages[idx];
        acc = st.step(acc, r.wrapping_mul(0x9e37_79b9) ^ mode);
        acc = acc.wrapping_add(i64::from(st.tag()));
        acc = fns[(idx + (r as usize)) & 1](acc);
    }
    acc
}

fn native_seeded_sha256_head(seed: u64, len: u32) -> [u8; 32] {
    let n = (len as usize).min(320);
    let mut msg = vec![0u8; n];
    let mut z = seed;
    for slot in &mut msg {
        z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut x = z;
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^= x >> 31;
        *slot = x as u8;
    }
    sha256(&msg)
}

fn native_f64_series(x: f64, y: f64, steps: u32) -> f64 {
    let mut acc = x;
    let mut cur = y;
    for k in 1..=steps {
        let kf = k as f64;
        let rad = ((acc * acc) + (cur * cur) + kf).sqrt();
        let snapped = (rad * 8.0).round_ties_even() * 0.125;
        let bounded = snapped.clamp(-1_000_000.0, 1_000_000.0);
        acc = (acc * 0.75) + (bounded.floor() - (cur * 0.25).ceil()) / (kf + 1.0);
        cur = (cur * -0.5 + (acc.abs()).copysign(cur)).trunc() + f64::from(acc as f32) * 0.0625;
    }
    let sat_i = (acc * 16.0) as i64;
    acc + (sat_i as f64) * (1.0 / 1024.0)
}

#[test]
fn rustc_guest_fixture_is_genuine_compact_wasm_binary() {
    assert_eq!(&RUSTC_GUEST_WASM[0..8], b"\0asm\x01\0\0\0");
    assert!(
        RUSTC_GUEST_WASM.len() < 32 * 1024,
        "rustc_guest.wasm size {} exceeds 32 KiB limit",
        RUSTC_GUEST_WASM.len()
    );
    // Also verify synthetic `.debug_info` custom section (`0x00`) appended to `rustc_guest.wasm` is ignored cleanly!
    let mut with_debug = RUSTC_GUEST_WASM.to_vec();
    let debug_payload = b"\x0b.debug_infoDWARF_TEST_BYTES";
    with_debug.push(0x00);
    with_debug.push(debug_payload.len() as u8);
    with_debug.extend_from_slice(debug_payload);
    let rec = run_wasm_metered(
        WasmCapTier::Sandboxed,
        &with_debug,
        "guest_sha256_input",
        &[WasmVal::I32(0)],
        &WasmExecutionBudget::new(500_000, 32 * WASM_PAGE_SIZE),
    )
    .unwrap();
    assert_eq!(
        rec.results[0].as_i64().unwrap() as u64,
        0xe3b0_c442_98fc_1c14_u64
    );
}

#[test]
fn executes_real_rustc_sha256_stack_rodata_and_bulk_memory_bit_identically() {
    let budget = WasmExecutionBudget::new(2_000_000, 32 * WASM_PAGE_SIZE);
    // Test 0-byte, 3-byte, exact 56-byte padding-boundary, 64-byte block-boundary, and 245-byte multi-block!
    for &(seed, len) in &[
        (0u64, 0u32),
        (0xdead_beef_cafe_babe, 3),
        (0x0123_4567_89ab_cdef, 55),
        (0x1111_2222_3333_4444, 56),
        (0xfeed_face_0000_0001, 64),
        (0x9999_aaaa_bbbb_cccc, 245),
    ] {
        let expected_digest = native_seeded_sha256_head(seed, len);
        let expected_head = u64::from_be_bytes(expected_digest[0..8].try_into().unwrap());
        let args = [WasmVal::I64(seed as i64), WasmVal::I32(len as i32)];
        let rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            RUSTC_GUEST_WASM,
            "guest_sha256_seeded",
            &args,
            &budget,
        )
        .unwrap();
        assert_eq!(rec.results, vec![WasmVal::I64(expected_head as i64)]);
        assert!(rec.verify_commitment(&args));
    }

    // Also verify empty-input NIST FIPS 180-4 SHA-256 vector (`e3b0c44298fc1c14...`) directly!
    let empty_rec = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "guest_sha256_input",
        &[WasmVal::I32(0)],
        &budget,
    )
    .unwrap();
    assert_eq!(
        empty_rec.results[0].as_i64().unwrap() as u64,
        0xe3b0_c442_98fc_1c14_u64
    );
}

#[test]
fn executes_real_rustc_trait_object_and_fn_pointer_call_indirect_bit_identically() {
    let budget = WasmExecutionBudget::new(1_000_000, 32 * WASM_PAGE_SIZE);
    for &(mode, rounds, init) in &[
        (0u32, 17u32, 0x1234_5678_9abc_def0_i64),
        (1u32, 29u32, -0x7777_6666_5555_4444_i64),
        (2u32, 41u32, 0i64),
    ] {
        let expected = native_trait_dispatch(mode, rounds, init);
        let args = [
            WasmVal::I32(mode as i32),
            WasmVal::I32(rounds as i32),
            WasmVal::I64(init),
        ];
        let rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            RUSTC_GUEST_WASM,
            "guest_trait_dispatch",
            &args,
            &budget,
        )
        .unwrap();
        assert_eq!(rec.results, vec![WasmVal::I64(expected)]);
        assert!(rec.verify_commitment(&args));
    }
}

#[test]
fn executes_real_rustc_f64_series_and_canonicalizes_all_arithmetic_nans() {
    let budget = WasmExecutionBudget::new(1_000_000, 32 * WASM_PAGE_SIZE);
    for &(x, y, steps) in &[
        (1.25_f64, -3.5_f64, 12u32),
        (-0.0_f64, 42.125_f64, 24u32),
        (1024.75_f64, -0.0625_f64, 30u32),
    ] {
        let expected_bits = native_f64_series(x, y, steps).to_bits();
        let args = [WasmVal::f64(x), WasmVal::f64(y), WasmVal::I32(steps as i32)];
        let rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            RUSTC_GUEST_WASM,
            "guest_f64_series",
            &args,
            &budget,
        )
        .unwrap();
        assert_eq!(rec.results, vec![WasmVal::F64(expected_bits)]);
        assert!(rec.verify_commitment(&args));
    }

    // Prove NaN canonicalization on `x86_64` where hardware `0.0 / 0.0` emits `0xfff8_0000_0000_0000` (`-qNaN`),
    // negative payloaded NaNs, signaling NaNs, `sqrt(-1.0)`, `f64.floor(sNaN)`, and `f32.demote_f64` + `f64.promote_f32`!
    let neg_payload_nan = 0xfff8_dead_beef_1234_u64;
    let sig_nan = 0x7ff0_0000_0000_0001_u64;
    for &(a_bits, b_bits, op_kind) in &[
        (neg_payload_nan, 1.0_f64.to_bits(), 0u32), // f64.add with -NaN payload
        (0.0_f64.to_bits(), 0.0_f64.to_bits(), 1u32), // f64.div 0.0 / 0.0 (-qNaN on x86_64!)
        ((-1.0_f64).to_bits(), 0, 2u32),            // f64.sqrt(-1.0)
        (sig_nan, 0, 3u32),                         // f64.floor(sNaN)
        (neg_payload_nan, 0, 4u32),                 // f32.demote_f64 + f64.promote_f32(-NaN)
    ] {
        let rec = run_wasm_metered(
            WasmCapTier::Sandboxed,
            RUSTC_GUEST_WASM,
            "guest_f64_nan_probe",
            &[
                WasmVal::I64(a_bits as i64),
                WasmVal::I64(b_bits as i64),
                WasmVal::I32(op_kind as i32),
            ],
            &budget,
        )
        .unwrap();
        assert_eq!(
            rec.results[0].as_f64_bits(),
            None, // returned via `u64` (`I64`) `.to_bits()`
        );
        assert_eq!(
            rec.results[0].as_i64().unwrap() as u64,
            CANON_F64_NAN_BITS,
            "op_kind {op_kind} failed to canonicalize NaN"
        );
    }

    // Pure bitwise `f64.neg` (`op_kind = 5`) MUST flip sign bit and preserve NaN payload per Wasm 1.0 spec!
    let neg_rec = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "guest_f64_nan_probe",
        &[
            WasmVal::I64(neg_payload_nan as i64),
            WasmVal::I64(0),
            WasmVal::I32(5),
        ],
        &budget,
    )
    .unwrap();
    assert_eq!(
        neg_rec.results[0].as_i64().unwrap() as u64,
        neg_payload_nan ^ 0x8000_0000_0000_0000
    );
    // Also verify Wasm `0xA4` (`f64.min`) and `0xA5` (`f64.max`) opcodes directly propagate NaN to canonical quiet NaN!
    let wasm_f64_min_max: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x60, 0x02, 0x7c, 0x7c,
        0x01, 0x7c, // (f64, f64) -> f64
        0x03, 0x03, 0x02, 0x00, 0x00, 0x07, 0x0d, 0x02, 0x03, b'm', b'i', b'n', 0x00, 0x00, 0x03,
        b'm', b'a', b'x', 0x00, 0x01, 0x0a, 0x11, 0x02, 0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0xa4,
        0x0b, // f64.min
        0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0xa5, 0x0b, // f64.max
    ];
    for ep in ["min", "max"] {
        let r = run_wasm_metered(
            WasmCapTier::Sandboxed,
            wasm_f64_min_max,
            ep,
            &[WasmVal::F64(sig_nan), WasmVal::f64(5.0)],
            &budget,
        )
        .unwrap();
        assert_eq!(r.results, vec![WasmVal::F64(CANON_F64_NAN_BITS)]);
    }
}

#[test]
fn executes_bounded_heap_bump_allocation_and_traps_confinement_violations() {
    // 1. Bounded `memory.grow` bump allocation succeeds within budget and records exact peak memory.
    let heap_budget = WasmExecutionBudget::new(500_000, 32 * WASM_PAGE_SIZE);
    let mut expected_word_sum = 0u64;
    let mut s = 0x1357_9bdf_u32;
    for _ in 0..256 {
        s = s.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        expected_word_sum = expected_word_sum.wrapping_add(u64::from(s));
    }
    let heap_rec = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "guest_heap_bump_checksum",
        &[
            WasmVal::I32(2),
            WasmVal::I32(256),
            WasmVal::I32(0x1357_9bdf_u32 as i32),
        ],
        &heap_budget,
    )
    .unwrap();
    let packed = heap_rec.results[0].as_i64().unwrap() as u64;
    let reported_total_pages = (packed >> 32) as usize;
    assert_eq!(
        heap_rec.peak_memory_bytes,
        reported_total_pages * WASM_PAGE_SIZE
    );
    assert_eq!(packed & 0xffff_ffff, expected_word_sum & 0xffff_ffff);

    // 2. `spin_forever` compiled by `rustc` deterministically halts with `OutOfFuel` (with wall timeout disabled so host scheduling never races fuel).
    let mut spin_budget = WasmExecutionBudget::new(5_000, 32 * WASM_PAGE_SIZE);
    spin_budget.max_wall_time = None;
    let spin_err = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "spin_forever",
        &[WasmVal::I32(42)],
        &spin_budget,
    );
    assert_eq!(
        spin_err,
        Err(WasmRunError::OutOfFuel {
            max_fuel: 5_000,
            consumed: 5_000,
        })
    );

    // 3. `alloc_bomb` compiled by `rustc` deterministically halts with `MemoryLimitExceeded`.
    let max_mem = 20 * WASM_PAGE_SIZE;
    let oom_err = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "alloc_bomb",
        &[WasmVal::I32(8)],
        &WasmExecutionBudget::new(500_000, max_mem),
    );
    assert!(
        matches!(
            oom_err,
            Err(WasmRunError::MemoryLimitExceeded {
                requested_bytes,
                max_bytes
            }) if requested_bytes > max_bytes && max_bytes == max_mem
        ),
        "unexpected alloc_bomb result: {oom_err:?}"
    );

    // 4. Out-of-bounds `u32::MAX` address load inside `rustc_guest.wasm` AND `offset = u32::MAX` wrap probe trap!
    let oob_guest = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "guest_oob_load",
        &[WasmVal::I32(u32::MAX as i32)],
        &heap_budget,
    );
    assert!(matches!(oob_guest, Err(WasmRunError::Trap(ref m)) if m.contains("out of bounds")));

    let wasm_u32_max_offset: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01,
        0x7f, 0x03, 0x02, 0x01, 0x00, 0x05, 0x03, 0x01, 0x00, 0x01, 0x07, 0x07, 0x01, 0x03, b'o',
        b'o', b'b', 0x00, 0x00, 0x0a, 0x0d, 0x01, 0x0b, 0x00, 0x20, 0x00, 0x28, 0x02, 0xff, 0xff,
        0xff, 0xff, 0x0f, // i32.load align=4 offset=u32::MAX
        0x0b,
    ];
    let oob_wrap = run_wasm_metered(
        WasmCapTier::Sandboxed,
        wasm_u32_max_offset,
        "oob",
        &[WasmVal::I32(4)],
        &heap_budget,
    );
    assert!(matches!(oob_wrap, Err(WasmRunError::Trap(ref m)) if m.contains("out of bounds")));

    // 5. Indirect-call (`call_indirect`) runtime FuncType signature mismatch & OOB/null traps!
    // Module with table[0] = func 0 `(i64) -> i64`, table[1] = null, and func 1 `(i32) -> i32`
    // executing `call_indirect (type (i32) -> i32)` on table index `param 0`!
    let wasm_indirect_sig_mismatch: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        // Section 1 (Type): type 0 = (i64) -> i64, type 1 = (i32) -> i32
        0x01, 0x0b, 0x02, 0x60, 0x01, 0x7e, 0x01, 0x7e, 0x60, 0x01, 0x7f, 0x01, 0x7f,
        // Section 3 (Function): func 0 -> type 0, func 1 -> type 1
        0x03, 0x03, 0x02, 0x00, 0x01, // Section 4 (Table): 1 funcref table, min 2
        0x04, 0x04, 0x01, 0x70, 0x00, 0x02, // Section 7 (Export): "probe" -> func 1
        0x07, 0x09, 0x01, 0x05, b'p', b'r', b'o', b'b', b'e', 0x00, 0x01,
        // Section 9 (Element): active table 0 at offset 0 -> [func 0] (leaving slot 1 = null!)
        0x09, 0x07, 0x01, 0x00, 0x41, 0x00, 0x0b, 0x01, 0x00,
        // Section 10 (Code):
        // func 0: local.get 0; end (len = 4)
        // func 1: i32.const 42; local.get 0; call_indirect (type 1, table 0); end (len = 9)
        0x0a, 0x10, 0x02, 0x04, 0x00, 0x20, 0x00, 0x0b, 0x09, 0x00, 0x41, 0x2a, 0x20, 0x00, 0x11,
        0x01, 0x00, 0x0b,
    ];
    // Slot 0 holds `(i64) -> i64`, called as `(i32) -> i32` -> Trap("indirect call type mismatch")
    let sig_trap = run_wasm_metered(
        WasmCapTier::Sandboxed,
        wasm_indirect_sig_mismatch,
        "probe",
        &[WasmVal::I32(0)],
        &heap_budget,
    );
    assert!(
        matches!(sig_trap, Err(WasmRunError::Trap(ref m)) if m.contains("indirect call type mismatch")),
        "expected indirect call type mismatch trap, got {sig_trap:?}"
    );
    // Slot 1 is null funcref -> Trap("null funcref")
    let null_trap = run_wasm_metered(
        WasmCapTier::Sandboxed,
        wasm_indirect_sig_mismatch,
        "probe",
        &[WasmVal::I32(1)],
        &heap_budget,
    );
    assert!(matches!(null_trap, Err(WasmRunError::Trap(ref m)) if m.contains("null funcref")));
    // Slot 2 is OOB -> Trap("index out of bounds")
    let oob_tbl_trap = run_wasm_metered(
        WasmCapTier::Sandboxed,
        wasm_indirect_sig_mismatch,
        "probe",
        &[WasmVal::I32(2)],
        &heap_budget,
    );
    assert!(matches!(oob_tbl_trap, Err(WasmRunError::Trap(ref m)) if m.contains("out of bounds")));

    // Entrypoint host call signature mismatch on `rustc_guest.wasm` fails closed with `SignatureMismatch`.
    let host_sig_err = run_wasm_metered(
        WasmCapTier::Sandboxed,
        RUSTC_GUEST_WASM,
        "guest_f64_series",
        &[WasmVal::I32(1)],
        &heap_budget,
    );
    assert!(matches!(
        host_sig_err,
        Err(WasmRunError::SignatureMismatch(_))
    ));
}
