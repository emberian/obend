//! PIDE `ObendSession` elaboration, claim/law inspection, replay-turn submission, and law
//! affordance client backed by the Lean `Obend.FFI.Bridge` kernel library.

use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NotebookCell {
    pub id: String,
    pub kind: String,
    pub source: String,
    pub status: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct DeclarationSummary {
    pub name: String,
    pub declaration: String,
    pub kind: String,
    pub status: String,
    #[serde(default, rename = "typeText")]
    pub type_text: Option<String>,
    #[serde(default)]
    pub uses: usize,
    #[serde(default, rename = "objectLayers")]
    pub object_layers: Vec<String>,
    #[serde(default, rename = "leafSlots")]
    pub leaf_slots: usize,
    #[serde(default)]
    pub preview: Value,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ClaimSummary {
    pub claim: String,
    pub spec: String,
    pub name: String,
    pub status: String,
    #[serde(default)]
    pub steps: usize,
    #[serde(default)]
    pub diagnostic: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LawSummary {
    pub name: String,
    pub declaration: String,
    pub rendered: String,
    pub confluence: String,
    pub status: String,
    #[serde(default)]
    pub fields: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LeafBookSummary {
    pub object: String,
    pub layers: Vec<String>,
    #[serde(rename = "slotCount")]
    pub slot_count: usize,
    pub slots: Vec<String>,
    pub closed: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ElaborationSummary {
    pub schema: String,
    pub status: String,
    pub module: String,
    pub sha256: String,
    #[serde(default)]
    pub declarations: Vec<DeclarationSummary>,
    #[serde(default)]
    pub claims: Vec<ClaimSummary>,
    #[serde(default)]
    pub laws: Vec<LawSummary>,
    #[serde(default, rename = "leafBooks")]
    pub leaf_books: Vec<LeafBookSummary>,
    #[serde(default)]
    pub previews: Vec<Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LawAffordanceReport {
    #[serde(rename = "cellCount")]
    pub cell_count: usize,
    pub turn: usize,
    pub parsed: bool,
    #[serde(rename = "lawDial")]
    pub law_dial: String,
    pub confluence: String,
    #[serde(rename = "renderedLaw")]
    pub rendered_law: String,
    pub fields: Vec<String>,
    #[serde(rename = "repairSuggestion")]
    pub repair_suggestion: String,
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

    pub fn session_mut(&mut self) -> &mut ObendSession {
        &mut self.session
    }

    /// Elaborate a single `.obend` cell via `ObendSession::eval_cell` and parse its structured
    /// `obend.ffi.elaboration.v1` report. Non-`.obend` or ill-typed cells fail closed.
    pub fn elaborate_obend(&mut self, source: &str) -> Result<ElaborationSummary, ObendError> {
        let bytes = self.session.eval_cell(source.as_bytes())?;
        serde_json::from_slice(&bytes).map_err(|e| {
            ObendError::WithDetail(
                Box::new(ObendError::DecodeFailed),
                format!("elaboration JSON decode error: {e}"),
            )
        })
    }

    /// Query law confluence classification (`Obend.Spec.LawDial.dial`) and Bellman-Ford repair
    /// suggestions (`Obend.Vault.suggestMultiField`) for a surface `law` expression.
    pub fn query_law_affordances(
        &mut self,
        law_query: &str,
    ) -> Result<LawAffordanceReport, ObendError> {
        let bytes = self.session.view_affordances(law_query.as_bytes())?;
        serde_json::from_slice(&bytes).map_err(|e| {
            ObendError::WithDetail(
                Box::new(ObendError::DecodeFailed),
                format!("affordance JSON decode error: {e}"),
            )
        })
    }

    /// Execute a sequence of notebook cells, returning structured elaboration reports per cell ID.
    pub fn execute_cells(
        &mut self,
        cells: &[NotebookCell],
    ) -> Vec<(String, Result<ElaborationSummary, ObendError>)> {
        cells
            .iter()
            .map(|cell| (cell.id.clone(), self.elaborate_obend(&cell.source)))
            .collect()
    }
}
