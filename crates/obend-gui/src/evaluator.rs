use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NotebookCell {
    pub id: String,
    pub kind: String,
    pub source: String,
    pub status: String,
}

pub struct NotebookRunner {
    session: ObendSession,
}

impl NotebookRunner {
    pub fn new() -> Result<Self, ObendError> {
        Ok(Self {
            session: ObendSession::new()?,
        })
    }

    pub fn execute_cells(&mut self, cells: &[NotebookCell]) -> Vec<(String, Result<Vec<u8>, ObendError>)> {
        let mut results = Vec::new();
        for cell in cells {
            let res = self.session.eval_cell(cell.source.as_bytes());
            results.push((cell.id.clone(), res));
        }
        results
    }
}
