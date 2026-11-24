#[repr(C)]
pub struct Session {
    _unused: [u8; 0],
}

#[cfg(not(feature = "stub"))]
extern "C" {
    pub fn lean_initialize_runtime_module();
    pub fn lean_initialize_thread();
    pub fn lean_finalize_thread();
    /// Runtime-once plus thread-once initialization, in the right order (`lean/c/obend_bridge.c`).
    pub fn obend_ensure_lean_thread();

    pub fn obend_session_init(config_ptr: *const u8, config_len: usize) -> *mut Session;
    pub fn obend_session_free(session: *mut Session);

    pub fn obend_eval_cell(
        session: *mut Session,
        cell_ptr: *const u8,
        cell_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_turn_propose(
        session: *mut Session,
        turn_ptr: *const u8,
        turn_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_turn_commit(
        session: *mut Session,
        turn_id_ptr: *const u8,
        turn_id_len: usize,
    ) -> i32;

    pub fn obend_project_hardware(
        session: *mut Session,
        hw_ptr: *const u8,
        hw_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_verify_receipt(
        session: *mut Session,
        receipt_ptr: *const u8,
        receipt_len: usize,
    ) -> i32;

    pub fn obend_get_last_error(
        session: *mut Session,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_view_affordances(
        session: *mut Session,
        query_ptr: *const u8,
        query_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_cell_pop_lean(
        session: *mut Session,
        cell_ptr: *const u8,
        cell_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_cell_weave_cert(
        session: *mut Session,
        cert_ptr: *const u8,
        cert_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32;

    pub fn obend_workbook_step_json(
        s: *mut std::ffi::c_void,
        req_ba: *mut std::ffi::c_void,
    ) -> *mut std::ffi::c_void;

    pub fn obend_workbook_scrub_cell_json(
        s: *mut std::ffi::c_void,
        req_ba: *mut std::ffi::c_void,
    ) -> *mut std::ffi::c_void;

    // Legacy C ABI for callers constructing a ByteArray incrementally.
    pub fn obend_ffi_ba_empty(cap: usize) -> *mut std::ffi::c_void;
    pub fn obend_ffi_ba_push(ba: *mut std::ffi::c_void, b: u8) -> *mut std::ffi::c_void;

    /// An owned, exclusive Lean `ByteArray` (`m_rc == 1`, size and capacity `len`) holding a copy
    /// of `len` bytes at `ptr`, built by one allocation and one `memcpy` in
    /// `lean/c/obend_bridge.c`. `ptr` is not read when `len == 0`, so the dangling pointer of an
    /// empty slice is fine. Returns NULL for a nonempty null input or a length above `isize::MAX`.
    pub fn obend_mk_byte_array_from_slice(ptr: *const u8, len: usize) -> *mut std::ffi::c_void;
    pub fn obend_ffi_res_into_state(res: *mut std::ffi::c_void) -> *mut std::ffi::c_void;
}

/// Exact `<lean/lean.h>` 8-byte object header (`m_rc`, `m_cs_sz`, `m_other`, `m_tag`).
#[cfg(not(feature = "stub"))]
#[repr(C)]
struct LeanObjectHeader {
    m_rc: i32,
    m_cs_sz: u16,
    m_other: u8,
    m_tag: u8,
}

/// Exact `<lean/lean.h>` `lean_sarray_object` prefix (`m_header`, `m_size`, `m_capacity`).
#[cfg(not(feature = "stub"))]
#[repr(C)]
struct LeanSArrayHeader {
    m_header: LeanObjectHeader,
    m_size: usize,
    m_capacity: usize,
}

#[cfg(not(feature = "stub"))]
const _: () = {
    assert!(std::mem::size_of::<LeanObjectHeader>() == 8);
    assert!(std::mem::size_of::<LeanSArrayHeader>() == 8 + 2 * std::mem::size_of::<usize>());
};

#[cfg(not(feature = "stub"))]
#[inline]
unsafe fn lean_ctor_get(o: *const std::ffi::c_void, idx: usize) -> *mut std::ffi::c_void {
    let fields = (o as *const u8).add(std::mem::size_of::<LeanObjectHeader>())
        as *const *mut std::ffi::c_void;
    *fields.add(idx)
}

#[cfg(not(feature = "stub"))]
#[inline]
unsafe fn lean_unbox_uint32(o: *const std::ffi::c_void) -> u32 {
    #[cfg(target_pointer_width = "64")]
    {
        ((o as usize) >> 1) as u32
    }
    #[cfg(target_pointer_width = "32")]
    {
        let hdr = &*(o as *const LeanObjectHeader);
        let obj_bytes = (hdr.m_other as usize) * std::mem::size_of::<*mut std::ffi::c_void>();
        let payload =
            (o as *const u8).add(std::mem::size_of::<LeanObjectHeader>() + obj_bytes) as *const u32;
        *payload
    }
}

#[cfg(not(feature = "stub"))]
#[inline]
unsafe fn lean_sarray_to_vec(o: *const std::ffi::c_void) -> Vec<u8> {
    let hdr = &*(o as *const LeanSArrayHeader);
    let len = hdr.m_size;
    if len == 0 {
        return Vec::new();
    }
    let data_ptr = (o as *const u8).add(std::mem::size_of::<LeanSArrayHeader>());
    std::slice::from_raw_parts(data_ptr, len).to_vec()
}

#[cfg(not(feature = "stub"))]
unsafe fn invoke_lean_session_json(
    session: *mut Session,
    req: &[u8],
    f: unsafe extern "C" fn(*mut std::ffi::c_void, *mut std::ffi::c_void) -> *mut std::ffi::c_void,
) -> Result<Vec<u8>, i32> {
    if session.is_null() {
        return Err(-1);
    }
    // `ObendSessionHandle` (`lean/c/obend_bridge.c:7`) stores `lean_object *lean_state` at offset 0.
    let state_slot = session as *mut *mut std::ffi::c_void;
    let old_state = *state_slot;
    if old_state.is_null() {
        return Err(-2);
    }
    // One crossing for the whole request, whatever its length.
    let req_ba = obend_mk_byte_array_from_slice(req.as_ptr(), req.len());
    if req_ba.is_null() {
        return Err(-1);
    }
    // `f` consumes owned `old_state` and `req_ba`, returning owned `SessionState × ByteArray × Int32`.
    *state_slot = std::ptr::null_mut();
    let res = f(old_state, req_ba);
    if res.is_null() {
        return Err(-1);
    }
    // Borrow `inner = res.2`, `out_ba = inner.1`, `code = inner.2` while `res` is live (`m_rc >= 1`).
    let inner = lean_ctor_get(res, 1);
    let out_ba = lean_ctor_get(inner, 0);
    let code = lean_unbox_uint32(lean_ctor_get(inner, 1)) as i32;
    let out = if code == 0 {
        Some(lean_sarray_to_vec(out_ba))
    } else {
        None
    };
    // Lean's generated `obend_ffi_res_into_state` runs `lean_inc(res.1)` + `lean_dec(res)` and
    // returns owned `new_state` with zero manual refcount arithmetic in Rust.
    let new_state = obend_ffi_res_into_state(res);
    *state_slot = new_state;
    match out {
        Some(buf) => Ok(buf),
        None => Err(code),
    }
}

/// # Safety
/// `session` must be a valid live `Session` pointer owned exclusively for the duration of the call.
#[cfg(not(feature = "stub"))]
pub unsafe fn call_workbook_step_json(session: *mut Session, req: &[u8]) -> Result<Vec<u8>, i32> {
    unsafe { invoke_lean_session_json(session, req, obend_workbook_step_json) }
}

/// # Safety
/// `session` must be a valid live `Session` pointer owned exclusively for the duration of the call.
#[cfg(not(feature = "stub"))]
pub unsafe fn call_workbook_scrub_cell_json(
    session: *mut Session,
    req: &[u8],
) -> Result<Vec<u8>, i32> {
    unsafe { invoke_lean_session_json(session, req, obend_workbook_scrub_cell_json) }
}

#[cfg(all(test, not(feature = "stub")))]
mod tests {
    use super::*;

    extern "C" {
        /// What `lean_dec` reaches for an object with `m_rc == 1` (`<lean/lean.h>`): frees it.
        fn lean_dec_ref_cold(o: *mut std::ffi::c_void);
    }

    /// Cycles through all 256 byte values (131 is odd), from an offset that depends on `len`.
    fn pattern(len: usize) -> Vec<u8> {
        (0..len)
            .map(|i| (i.wrapping_mul(131).wrapping_add(len) % 256) as u8)
            .collect()
    }

    /// The object is a fresh exclusive `ByteArray` of exactly `bytes`; then release it.
    unsafe fn expect_fresh(o: *mut std::ffi::c_void, bytes: &[u8]) {
        assert!(!o.is_null());
        let hdr = &*(o as *const LeanSArrayHeader);
        assert_eq!(hdr.m_header.m_rc, 1);
        assert_eq!(hdr.m_header.m_tag, 248, "LeanScalarArray");
        assert_eq!(hdr.m_header.m_other, 1, "element size");
        assert_eq!((hdr.m_size, hdr.m_capacity), (bytes.len(), bytes.len()));
        assert_eq!(lean_sarray_to_vec(o), bytes);
        lean_dec_ref_cold(o);
    }

    #[test]
    fn bulk_byte_array_copies_each_payload_exactly() {
        for len in [0, 1, 32, 64 * 1024] {
            let mut source = pattern(len);
            let expected = source.clone();
            let array = unsafe { obend_mk_byte_array_from_slice(source.as_ptr(), len) };
            source.fill(0);
            drop(source);
            unsafe { expect_fresh(array, &expected) };
        }
        let empty: &[u8] = &[];
        unsafe {
            expect_fresh(obend_mk_byte_array_from_slice(empty.as_ptr(), 0), &[]);
            expect_fresh(obend_mk_byte_array_from_slice(std::ptr::null(), 0), &[]);
            assert!(obend_mk_byte_array_from_slice(std::ptr::null(), 1).is_null());
            assert!(obend_mk_byte_array_from_slice(empty.as_ptr(), usize::MAX).is_null());
            assert!(obend_session_init(std::ptr::null(), 1).is_null());
        }
    }
}

#[cfg(feature = "stub")]
pub mod stub {
    use super::Session;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    static NEXT_ID: AtomicUsize = AtomicUsize::new(1);

    pub const RECEIPT_MAGIC: &[u8; 16] = b"OBEND_RCPT_V1\0\0\0";

    pub const STUB_REFUSAL: &[u8] =
        b"stub FFI: no Lean kernel is linked (built with OBEND_ALLOW_STUB_FFI); nothing is verified here";

    pub struct StubSession {
        pub id: usize,
        pub scratch_buf: Mutex<Vec<u8>>,
        pub err_buf: Mutex<Vec<u8>>,
        pub pending_proposals: Mutex<Vec<Vec<u8>>>,
        pub committed_roots: Mutex<Vec<Vec<u8>>>,
    }

    fn compute_stub_digest16(payload: &[u8]) -> [u8; 16] {
        let mut h1: u64 = 0xcbf2_9ce4_8422_2325;
        let mut h2: u64 = 0x8422_2325_cbf2_9ce4;
        for (idx, &b) in payload.iter().enumerate() {
            h1 ^= b as u64;
            h1 = h1.wrapping_mul(0x0000_0100_0000_01b3);
            h2 ^= (b as u64).wrapping_add(idx as u64);
            h2 = h2.wrapping_mul(0x0000_0100_0000_01b3).rotate_left(5);
        }
        if h1 == 0 && h2 == 0 {
            h1 = 1;
        }
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&h1.to_le_bytes());
        out[8..16].copy_from_slice(&h2.to_le_bytes());
        out
    }

    fn build_stub_receipt(magic: &[u8; 16], payload: &[u8]) -> Vec<u8> {
        let mut rcpt = Vec::with_capacity(32);
        rcpt.extend_from_slice(magic);
        rcpt.extend_from_slice(&compute_stub_digest16(payload));
        rcpt
    }

    /// # Safety
    /// No requirements: the stub has no Lean runtime. `unsafe` matches the linked signature.
    pub unsafe fn lean_initialize_runtime_module() {}
    /// # Safety
    /// No requirements: the stub has no Lean runtime. `unsafe` matches the linked signature.
    pub unsafe fn lean_initialize_thread() {}
    /// # Safety
    /// No requirements: the stub has no Lean runtime. `unsafe` matches the linked signature.
    pub unsafe fn lean_finalize_thread() {}
    /// # Safety
    /// No requirements: the stub has no Lean runtime. `unsafe` matches the linked signature.
    pub unsafe fn obend_ensure_lean_thread() {}

    /// # Safety
    /// The configuration is not read. Release the returned session with [`obend_session_free`].
    pub unsafe fn obend_session_init(_config_ptr: *const u8, _config_len: usize) -> *mut Session {
        let id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
        let stub = Box::new(StubSession {
            id,
            scratch_buf: Mutex::new(Vec::new()),
            err_buf: Mutex::new(Vec::new()),
            pending_proposals: Mutex::new(Vec::new()),
            committed_roots: Mutex::new(Vec::new()),
        });
        Box::into_raw(stub) as *mut Session
    }

    /// # Safety
    /// `session` must be null or a pointer from [`obend_session_init`] that has not been freed,
    /// and it must not be used afterwards.
    pub unsafe fn obend_session_free(session: *mut Session) {
        if !session.is_null() {
            let _ = Box::from_raw(session as *mut StubSession);
        }
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length, and non-null output pointers must be writable. A buffer returned
    /// through `out_ptr` belongs to the session and is valid until its next call.
    pub unsafe fn obend_eval_cell(
        session: *mut Session,
        cell_ptr: *const u8,
        cell_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        if cell_len > 0 && cell_ptr.is_null() {
            return -1;
        }
        if cell_len == 0 {
            return -3;
        }
        let stub = &*(session as *mut StubSession);
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        -10
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length, and non-null output pointers must be writable. A buffer returned
    /// through `out_ptr` belongs to the session and is valid until its next call.
    pub unsafe fn obend_turn_propose(
        session: *mut Session,
        turn_ptr: *const u8,
        turn_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        if turn_len > 0 && turn_ptr.is_null() {
            return -1;
        }
        if turn_len == 0 {
            return -3;
        }
        let stub = &*(session as *mut StubSession);
        let slice = std::slice::from_raw_parts(turn_ptr, turn_len);
        let rcpt = build_stub_receipt(RECEIPT_MAGIC, slice);
        {
            let mut props = stub.pending_proposals.lock().unwrap();
            props.push(rcpt.clone());
        }
        let mut buf = stub.scratch_buf.lock().unwrap();
        *buf = rcpt;
        *out_ptr = buf.as_mut_ptr();
        *out_len = 32;
        0
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length.
    pub unsafe fn obend_turn_commit(
        session: *mut Session,
        turn_id_ptr: *const u8,
        turn_id_len: usize,
    ) -> i32 {
        if session.is_null() {
            return -1;
        }
        if turn_id_len > 0 && turn_id_ptr.is_null() {
            return -1;
        }
        if turn_id_len != 32 {
            return -6;
        }
        let stub = &*(session as *mut StubSession);
        let tid = std::slice::from_raw_parts(turn_id_ptr, turn_id_len);
        let mut props = stub.pending_proposals.lock().unwrap();
        if let Some(pos) = props.iter().position(|p| p.as_slice() == tid) {
            props.remove(pos);
            let mut roots = stub.committed_roots.lock().unwrap();
            if !roots.iter().any(|r| r.as_slice() == tid) {
                roots.push(tid.to_vec());
            }
            0
        } else {
            -5
        }
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length, and non-null output pointers must be writable. A buffer returned
    /// through `out_ptr` belongs to the session and is valid until its next call.
    pub unsafe fn obend_project_hardware(
        session: *mut Session,
        hw_ptr: *const u8,
        hw_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        if hw_len > 0 && hw_ptr.is_null() {
            return -1;
        }
        if hw_len == 0 {
            return -7;
        }
        let stub = &*(session as *mut StubSession);
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        -10
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length.
    pub unsafe fn obend_verify_receipt(
        session: *mut Session,
        receipt_ptr: *const u8,
        receipt_len: usize,
    ) -> i32 {
        if session.is_null() {
            return -1;
        }
        if receipt_len > 0 && receipt_ptr.is_null() {
            return -1;
        }
        let stub = &*(session as *mut StubSession);
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        -10
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. Non-null output pointers must be
    /// writable. The returned buffer belongs to the session and is valid until its next call.
    pub unsafe fn obend_get_last_error(
        session: *mut Session,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        let stub = &*(session as *mut StubSession);
        let mut buf = stub.err_buf.lock().unwrap();
        let mut scratch = stub.scratch_buf.lock().unwrap();
        *scratch = if buf.is_empty() {
            b"No error".to_vec()
        } else {
            std::mem::take(&mut *buf)
        };
        *out_ptr = scratch.as_mut_ptr();
        *out_len = scratch.len();
        0
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length, and non-null output pointers must be writable. A buffer returned
    /// through `out_ptr` belongs to the session and is valid until its next call.
    pub unsafe fn obend_view_affordances(
        session: *mut Session,
        query_ptr: *const u8,
        query_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        if query_len > 0 && query_ptr.is_null() {
            return -1;
        }
        if query_len == 0 {
            return -3;
        }
        let stub = &*(session as *mut StubSession);
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        -10
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length, and non-null output pointers must be writable. A buffer returned
    /// through `out_ptr` belongs to the session and is valid until its next call.
    pub unsafe fn obend_cell_pop_lean(
        session: *mut Session,
        cell_ptr: *const u8,
        cell_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        if cell_len > 0 && cell_ptr.is_null() {
            return -1;
        }
        if cell_len == 0 {
            return -3;
        }
        let stub = &*(session as *mut StubSession);
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        -10
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`]. A non-null input pointer must be
    /// readable for its length, and non-null output pointers must be writable. A buffer returned
    /// through `out_ptr` belongs to the session and is valid until its next call.
    pub unsafe fn obend_cell_weave_cert(
        session: *mut Session,
        cert_ptr: *const u8,
        cert_len: usize,
        out_ptr: *mut *mut u8,
        out_len: *mut usize,
    ) -> i32 {
        if session.is_null() || out_ptr.is_null() || out_len.is_null() {
            return -1;
        }
        if cert_len > 0 && cert_ptr.is_null() {
            return -1;
        }
        let stub = &*(session as *mut StubSession);
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        -10
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`].
    pub unsafe fn call_workbook_step_json(
        session: *mut Session,
        req: &[u8],
    ) -> Result<Vec<u8>, i32> {
        if session.is_null() {
            return Err(-1);
        }
        let stub = &*(session as *mut StubSession);
        if req.is_empty() {
            let mut err = stub.err_buf.lock().unwrap();
            *err = b"Empty workbook step payload".to_vec();
            return Err(-3);
        }
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        Err(-10)
    }

    /// # Safety
    /// `session` must be null or live from [`obend_session_init`].
    pub unsafe fn call_workbook_scrub_cell_json(
        session: *mut Session,
        req: &[u8],
    ) -> Result<Vec<u8>, i32> {
        if session.is_null() {
            return Err(-1);
        }
        let stub = &*(session as *mut StubSession);
        if req.is_empty() {
            let mut err = stub.err_buf.lock().unwrap();
            *err = b"Empty scrub payload".to_vec();
            return Err(-3);
        }
        let mut err = stub.err_buf.lock().unwrap();
        *err = STUB_REFUSAL.to_vec();
        Err(-10)
    }
}
#[cfg(feature = "stub")]
pub use stub::*;
