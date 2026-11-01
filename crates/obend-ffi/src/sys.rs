#[repr(C)]
pub struct Session {
    _unused: [u8; 0],
}

#[cfg(not(feature = "stub"))]
extern "C" {
    pub fn lean_initialize_runtime_module();
    pub fn lean_initialize_thread();
    pub fn lean_finalize_thread();

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
}

#[cfg(feature = "stub")]
pub mod stub {
    use super::Session;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    static NEXT_ID: AtomicUsize = AtomicUsize::new(1);

    pub struct StubSession {
        pub id: usize,
        pub scratch_buf: Mutex<Vec<u8>>,
        pub err_buf: Mutex<Vec<u8>>,
    }

    pub unsafe fn lean_initialize_runtime_module() {}
    pub unsafe fn lean_initialize_thread() {}
    pub unsafe fn lean_finalize_thread() {}

    pub unsafe fn obend_session_init(_config_ptr: *const u8, _config_len: usize) -> *mut Session {
        let id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
        let stub = Box::new(StubSession {
            id,
            scratch_buf: Mutex::new(Vec::new()),
            err_buf: Mutex::new(Vec::new()),
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
        let mut buf = stub.scratch_buf.lock().unwrap();
        *buf = vec![42u8; 32];
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
        if turn_id_len != 32 && turn_id_len != 0 {
            return -6;
        }
        0
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
        if receipt_len >= 32 {
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
}

#[cfg(feature = "stub")]
pub use stub::*;
