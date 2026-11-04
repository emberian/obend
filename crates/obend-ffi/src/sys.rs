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
}

#[cfg(feature = "stub")]
pub mod stub {
    use super::Session;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    static NEXT_ID: AtomicUsize = AtomicUsize::new(1);

    pub const RECEIPT_MAGIC: &[u8; 16] = b"OBEND_RCPT_V1\0\0\0";

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

    pub unsafe fn lean_initialize_runtime_module() {}
    pub unsafe fn lean_initialize_thread() {}
    pub unsafe fn lean_finalize_thread() {}
    pub unsafe fn obend_ensure_lean_thread() {}

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

    pub unsafe fn obend_session_free(session: *mut Session) {
        if !session.is_null() {
            let _ = Box::from_raw(session as *mut StubSession);
        }
    }

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
        let mut buf = stub.scratch_buf.lock().unwrap();
        let slice = std::slice::from_raw_parts(cell_ptr, cell_len);
        *buf = slice.to_vec();
        *out_ptr = buf.as_mut_ptr();
        *out_len = buf.len();
        0
    }

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
        let mut buf = stub.scratch_buf.lock().unwrap();
        let slice = std::slice::from_raw_parts(hw_ptr, hw_len);
        *buf = slice.to_vec();
        *out_ptr = buf.as_mut_ptr();
        *out_len = buf.len();
        0
    }

    /// Mirror of `Obend.FFI.Bridge.verifyReceiptCore` for the one-leaf case: the frame
    /// `root(32) || size(8) || index(8) || pathLen(8) || payload` verifies iff `root` was
    /// committed by this session and is the stub digest of `payload`. Paths are not supported
    /// by the stub (refused), nor is anything the session did not commit.
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
        if receipt_len < 56 {
            return -8;
        }
        let stub = &*(session as *mut StubSession);
        let slice = std::slice::from_raw_parts(receipt_ptr, receipt_len);
        let root = &slice[..32];
        let size = u64::from_be_bytes(slice[32..40].try_into().unwrap());
        let index = u64::from_be_bytes(slice[40..48].try_into().unwrap());
        let path_len = u64::from_be_bytes(slice[48..56].try_into().unwrap());
        if size != 1 || index != 0 || path_len != 0 {
            return -8;
        }
        let payload = &slice[56..];
        let roots = stub.committed_roots.lock().unwrap();
        if !roots.iter().any(|r| r.as_slice() == root) {
            return -8;
        }
        if build_stub_receipt(RECEIPT_MAGIC, payload).as_slice() == root {
            0
        } else {
            -8
        }
    }

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
        *buf = b"No error\0".to_vec();
        *out_ptr = buf.as_mut_ptr();
        *out_len = buf.len() - 1;
        0
    }

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
        let mut buf = stub.scratch_buf.lock().unwrap();
        *buf = b"{\"cellCount\":1,\"turn\":0,\"lawDial\":\"locked\",\"repairSuggestion\":\"suggestMultiField_admits: Bellman-Ford shortest repair delta=0\"}".to_vec();
        *out_ptr = buf.as_mut_ptr();
        *out_len = buf.len();
        0
    }

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
        let slice = std::slice::from_raw_parts(cell_ptr, cell_len);
        let snippet = if let Ok(s) = std::str::from_utf8(slice) {
            let parts: Vec<&str> = s.trim().split(':').collect();
            if parts.len() == 4 {
                let id_clean: String = parts[0]
                    .chars()
                    .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
                    .collect();
                let val = parts[1].split('.').next().unwrap_or("28").trim();
                let lo = parts[2].split('.').next().unwrap_or("15").trim();
                let hi = parts[3].split('.').next().unwrap_or("35").trim();
                format!(
                    "import Obend.Tactic.Weave\nopen Obend.Tactic.Weave\n\n/-- Auto-popped from .obnb {id_clean} -/\ntheorem cell_{id_clean}_contract : ({lo} ≤ ({val} : Int) ∧ ({val} : Int) ≤ {hi}) := by\n  obend_unfold\n  obend_law\n"
                )
            } else {
                "import Obend.Tactic.Weave\nopen Obend.Tactic.Weave\n\n/-- Auto-popped from .obnb cell_1 -/\ntheorem cell_1_contract : (0 ≤ (1 : Int) ∧ (1 : Int) ≤ 32) := by\n  obend_unfold\n  obend_law\n".to_string()
            }
        } else {
            "import Obend.Tactic.Weave\nopen Obend.Tactic.Weave\n\n/-- Auto-popped from .obnb cell_1 -/\ntheorem cell_1_contract : (0 ≤ (1 : Int) ∧ (1 : Int) ≤ 32) := by\n  obend_unfold\n  obend_law\n".to_string()
        };
        let mut buf = stub.scratch_buf.lock().unwrap();
        *buf = snippet.into_bytes();
        *out_ptr = buf.as_mut_ptr();
        *out_len = buf.len();
        0
    }

    /// The stub has no judge registry, so no witness can be checked: every weave is refused.
    /// (`Obend.FFI.Bridge.cellWeaveCertCore` accepts only a witness its registered format accepts.)
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
        *err = b"stub FFI has no judge registry; weave refused".to_vec();
        -8
    }
}
#[cfg(feature = "stub")]
pub use stub::*;

