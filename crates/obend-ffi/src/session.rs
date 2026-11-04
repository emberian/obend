use crate::error::ObendError;
use crate::pool::ensure_lean_thread_initialized;
use crate::sys;
use std::ptr;

pub struct ObendSession {
    handle: *mut sys::Session,
}

unsafe impl Send for ObendSession {}

impl ObendSession {
    pub fn new() -> Result<Self, ObendError> {
        Self::with_config(&[])
    }

    pub fn with_config(config: &[u8]) -> Result<Self, ObendError> {
        ensure_lean_thread_initialized();
        let handle = unsafe {
            sys::obend_session_init(
                if config.is_empty() { ptr::null() } else { config.as_ptr() },
                config.len(),
            )
        };
        if handle.is_null() {
            Err(ObendError::InitializationFailed)
        } else {
            Ok(Self { handle })
        }
    }

    pub fn eval_cell(&mut self, cell_bytes: &[u8]) -> Result<Vec<u8>, ObendError> {
        ensure_lean_thread_initialized();
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_eval_cell(
                self.handle,
                if cell_bytes.is_empty() { ptr::null() } else { cell_bytes.as_ptr() },
                cell_bytes.len(),
                &mut out_ptr,
                &mut out_len,
            )
        };
        if rc == 0 {
            let slice = if out_len == 0 || out_ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(out_ptr, out_len) }
            };
            Ok(slice.to_vec())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    pub fn propose_turn(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, ObendError> {
        ensure_lean_thread_initialized();
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_turn_propose(
                self.handle,
                if turn_bytes.is_empty() { ptr::null() } else { turn_bytes.as_ptr() },
                turn_bytes.len(),
                &mut out_ptr,
                &mut out_len,
            )
        };
        if rc == 0 {
            let slice = if out_len == 0 || out_ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(out_ptr, out_len) }
            };
            Ok(slice.to_vec())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    pub fn commit_turn(&mut self, turn_id: &[u8]) -> Result<(), ObendError> {
        ensure_lean_thread_initialized();
        let rc = unsafe {
            sys::obend_turn_commit(
                self.handle,
                if turn_id.is_empty() { ptr::null() } else { turn_id.as_ptr() },
                turn_id.len(),
            )
        };
        if rc == 0 {
            Ok(())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    pub fn project_hardware(&mut self, hw_bytes: &[u8]) -> Result<Vec<u8>, ObendError> {
        ensure_lean_thread_initialized();
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_project_hardware(
                self.handle,
                if hw_bytes.is_empty() { ptr::null() } else { hw_bytes.as_ptr() },
                hw_bytes.len(),
                &mut out_ptr,
                &mut out_len,
            )
        };
        if rc == 0 {
            let slice = if out_len == 0 || out_ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(out_ptr, out_len) }
            };
            Ok(slice.to_vec())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    pub fn verify_receipt(&mut self, receipt_bytes: &[u8]) -> Result<bool, ObendError> {
        ensure_lean_thread_initialized();
        let rc = unsafe {
            sys::obend_verify_receipt(
                self.handle,
                if receipt_bytes.is_empty() { ptr::null() } else { receipt_bytes.as_ptr() },
                receipt_bytes.len(),
            )
        };
        match rc {
            0 => Ok(true),
            -8 => Ok(false),
            code => Err(self.last_error_or(ObendError::from_code(code))),
        }
    }

    /// Propose and commit `payload` in this session and return its receipt: the one-leaf frame
    /// `encode_receipt(turn_id, 1, 0, [], payload)` that `verify_receipt` accepts here
    /// (`Obend.FFI.Bridge.buildCommittedReceipt`). A session that did not commit the turn
    /// refuses the same bytes: receipts are bound to the committing session, not self-admitted.
    pub fn commit_payload(&mut self, payload: &[u8]) -> Result<Vec<u8>, ObendError> {
        let tid = self.propose_turn(payload)?;
        self.commit_turn(&tid)?;
        Ok(encode_receipt(&tid, 1, 0, &[], payload))
    }

    pub fn get_last_error(&self) -> String {
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_get_last_error(self.handle, &mut out_ptr, &mut out_len)
        };
        if rc == 0 && !out_ptr.is_null() && out_len > 0 {
            let slice = unsafe { std::slice::from_raw_parts(out_ptr, out_len) };
            String::from_utf8_lossy(slice).into_owned()
        } else {
            String::new()
        }
    }

    pub fn view_affordances(&mut self, query_bytes: &[u8]) -> Result<Vec<u8>, ObendError> {
        ensure_lean_thread_initialized();
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_view_affordances(
                self.handle,
                if query_bytes.is_empty() { ptr::null() } else { query_bytes.as_ptr() },
                query_bytes.len(),
                &mut out_ptr,
                &mut out_len,
            )
        };
        if rc == 0 {
            let slice = if out_len == 0 || out_ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(out_ptr, out_len) }
            };
            Ok(slice.to_vec())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    pub fn pop_lean(&mut self, cell_bytes: &[u8]) -> Result<String, ObendError> {
        ensure_lean_thread_initialized();
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_cell_pop_lean(
                self.handle,
                if cell_bytes.is_empty() { ptr::null() } else { cell_bytes.as_ptr() },
                cell_bytes.len(),
                &mut out_ptr,
                &mut out_len,
            )
        };
        if rc == 0 {
            let slice = if out_len == 0 || out_ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(out_ptr, out_len) }
            };
            Ok(String::from_utf8_lossy(slice).into_owned())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    pub fn weave_cert(&mut self, cert_bytes: &[u8]) -> Result<Vec<u8>, ObendError> {
        ensure_lean_thread_initialized();
        let mut out_ptr = ptr::null_mut();
        let mut out_len = 0usize;
        let rc = unsafe {
            sys::obend_cell_weave_cert(
                self.handle,
                if cert_bytes.is_empty() { ptr::null() } else { cert_bytes.as_ptr() },
                cert_bytes.len(),
                &mut out_ptr,
                &mut out_len,
            )
        };
        if rc == 0 {
            let slice = if out_len == 0 || out_ptr.is_null() {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(out_ptr, out_len) }
            };
            Ok(slice.to_vec())
        } else {
            Err(self.last_error_or(ObendError::from_code(rc)))
        }
    }

    fn last_error_or(&self, default: ObendError) -> ObendError {
        let msg = self.get_last_error();
        if msg.is_empty() {
            default
        } else {
            ObendError::WithDetail(Box::new(default), msg)
        }
    }
}

impl Drop for ObendSession {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { sys::obend_session_free(self.handle) };
            self.handle = ptr::null_mut();
        }
    }
}

/// The receipt wire frame `Obend.FFI.Bridge.encodeReceipt`:
/// `root(32) || size(8) || index(8) || pathLen(8) || path(pathLen x 32) || payload`,
/// integers big-endian. `verify_receipt` recomputes the payload's digest and climbs the path
/// (`Obend.Receipt.Merkle.opens`); the root must be one the session committed.
pub fn encode_receipt(root: &[u8], size: u64, index: u64, path: &[[u8; 32]], payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(56 + 32 * path.len() + payload.len());
    out.extend_from_slice(root);
    out.extend_from_slice(&size.to_be_bytes());
    out.extend_from_slice(&index.to_be_bytes());
    out.extend_from_slice(&(path.len() as u64).to_be_bytes());
    for p in path {
        out.extend_from_slice(p);
    }
    out.extend_from_slice(payload);
    out
}
