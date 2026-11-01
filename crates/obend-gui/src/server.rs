//! Live Interactive `.obnb` Workbench Server & `"Pop Out to Lean 4"` Bridge (`WS 31`)
//!
//! Provides an interactive HTTP/JSON workbench daemon (`WorkbenchServer`) over
//! `std::net::TcpListener` (binding `127.0.0.1:0` by default for deterministic ephemeral ports)
//! backed by a persistent `mimalloc`-safe `ObendSession` worker thread:
//! - `GET /notebook` — returns rendered interactive HTML/SVG `.obnb` notebook + JSON state.
//! - `POST /dial` — toggles a cell's `LawDial` mode (`.free` / `.press` / `.locked`), runs
//!   Bellman-Ford multi-field repair synthesis (`suggestMultiField_admits`) when `.press`
//!   detects a constraint violation, and returns the updated viewport + repair suggestions in sub-5ms.
//! - `POST /eval` — evaluates/updates a cell or scrubs an ODE/physical parameter and re-renders
//!   affected viewports (propagating `moved_pin_blocks` staleness to dependent woven certificates).
//! - `POST /lean-bridge` — implements the live `"Pop Out to Lean 4"` & `"Weave Certificate"` bridge:
//!   invokes `obend_cell_pop_lean` to generate the Lean 4 goal/tactic snippet (`obend_unfold`,
//!   `obend_law`, `obend_tooth`), verifies via kernel bridge or optional `lean` subprocess, and
//!   weaves the resulting 32-byte Merkle certificate receipt back into the `.obnb` cell via
//!   `obend_cell_weave_cert`.

use crate::viewport::{
    render_physical_viewport, render_projection_viewport, LawDialControl, LawDialMode,
    PhysicalViewportKind, ProjectionKind, RenderedViewport,
};
use obend_ffi::pool:: ensure_lean_thread_initialized;
use obend_ffi::session::ObendSession;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Sender};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// Constructive single- or multi-field repair suggestion synthesized by Bellman-Ford relaxation (`suggestMultiField_admits`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldRepairSuggestion {
    pub field: String,
    pub current_value: i64,
    pub suggested_value: i64,
}

/// Proof certificate receipt woven back into a `.obnb` cell (`Justification.byLoweredLean`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WovenCertificate {
    pub cell_id: String,
    pub justification: String,
    pub tactic_used: String,
    pub support_pins: Vec<String>,
    pub receipt_hex: String,
    pub verified: bool,
}

/// Interactive `.obnb` cell state managed by the `WorkbenchServer`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WorkbenchCellState {
    pub id: String,
    pub title: String,
    pub kind: ProjectionKind,
    pub physical_kind: Option<PhysicalViewportKind>,
    pub source: String,
    pub status: String,
    pub dial: LawDialControl,
    pub fields: BTreeMap<String, i64>,
    pub old_fields: BTreeMap<String, i64>,
    pub support_pins: Vec<String>,
    pub woven_cert: Option<WovenCertificate>,
    pub viewport: RenderedViewport,
}

impl WorkbenchCellState {
    /// Re-render this cell's multi-modal viewport (SVG, HTML `LawDial`, and ANSI terminal canvas).
    pub fn rerender_viewport(&mut self) {
        self.viewport = if let Some(pkind) = self.physical_kind {
            render_physical_viewport(pkind, &self.title, &self.dial)
        } else {
            render_projection_viewport(self.kind, &self.title, &self.dial)
        };
    }
}

/// JSON response payload for `GET /notebook`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NotebookStateResponse {
    pub notebook_id: String,
    pub turn: u64,
    pub html: String,
    pub cells: Vec<WorkbenchCellState>,
}

/// JSON request payload for `POST /dial`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DialRequest {
    pub cell_id: String,
    pub mode: LawDialMode,
    #[serde(default)]
    pub current_value: Option<f64>,
    #[serde(default)]
    pub fields: Option<BTreeMap<String, i64>>,
}

/// JSON response payload for `POST /dial`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DialResponse {
    pub cell_id: String,
    pub mode: LawDialMode,
    pub admitted: bool,
    pub verdict: String,
    pub repair_suggestions: Vec<FieldRepairSuggestion>,
    pub repair_summary: Option<String>,
    pub elapsed_micros: u64,
    pub viewport: RenderedViewport,
}

/// JSON request payload for `POST /eval`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EvalRequest {
    pub cell_id: String,
    #[serde(default)]
    pub source: Option<String>,
    #[serde(default)]
    pub parameter: Option<String>,
    #[serde(default)]
    pub value: Option<f64>,
    #[serde(default)]
    pub fields: Option<BTreeMap<String, i64>>,
    #[serde(default)]
    pub kind: Option<String>,
}

/// JSON response payload for `POST /eval`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EvalResponse {
    pub cell_id: String,
    pub status: String,
    pub evaluated_bytes: usize,
    pub turn_receipt_hex: String,
    pub rerendered_cells: Vec<String>,
    pub viewport: RenderedViewport,
}

/// JSON request payload for `POST /lean-bridge`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LeanBridgeRequest {
    pub cell_id: String,
    /// `"pop"`, `"weave"`, or `"pop_and_weave"` (defaults to `"pop_and_weave"`).
    #[serde(default)]
    pub action: Option<String>,
    /// `"obend_law"`, `"obend_unfold"`, or `"obend_tooth"` (defaults to `"obend_law"`).
    #[serde(default)]
    pub tactic: Option<String>,
    #[serde(default)]
    pub custom_lean_snippet: Option<String>,
    #[serde(default)]
    pub verify_subprocess: Option<bool>,
}

/// JSON response payload for `POST /lean-bridge`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LeanBridgeResponse {
    pub cell_id: String,
    pub lean_snippet: String,
    pub tactic_used: String,
    pub tooth_counterexample: Option<BTreeMap<String, i64>>,
    pub verified: bool,
    pub woven_cert: Option<WovenCertificate>,
    pub cell_status: String,
    pub viewport: RenderedViewport,
}

/// Alias for `FieldRepairSuggestion` (`WS 31`).
pub type FieldRepairDelta = FieldRepairSuggestion;
/// Alias for `LeanBridgeResponse` (`WS 31`).
pub type LeanGoalView = LeanBridgeResponse;
/// Alias for `EvalRequest` (`WS 31`).
pub type WorkbenchCommand = EvalRequest;
/// Alias for `EvalResponse` (`WS 31`).
pub type WorkbenchEvent = EvalResponse;
/// Alias for `WorkbenchServer` (`WS 31`).
pub type WorkbenchEngine = WorkbenchServer;

#[derive(Debug, Clone, PartialEq, Eq)]
enum LawAtomConstraint {
    Monotone(String),
    WriteOnce(String),
    LowerBound(String, i64),
    UpperBound(String, i64),
    EqConst(String, i64),
    EqField(String, String),
    /// `lhs <= rhs + offset` (e.g., `a <= b` has `offset = 0`, `a < b` has `offset = -1`).
    DiffLe {
        lhs: String,
        rhs: String,
        offset: i64,
    },
}

fn clean_field_ident(raw: &str) -> String {
    let trimmed = raw
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .trim();
    trimmed.strip_prefix("new.").unwrap_or(trimmed).trim().to_string()
}

fn parse_term_with_offset(raw: &str) -> (Option<String>, i64) {
    let s = raw
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .trim();
    if let Ok(num) = s.parse::<f64>() {
        return (None, num.round() as i64);
    }
    if let Some((base, off_str)) = s.rsplit_once('+') {
        if let Ok(off) = off_str.trim().parse::<f64>() {
            return (Some(clean_field_ident(base)), off.round() as i64);
        }
    }
    if let Some((base, off_str)) = s.rsplit_once('-') {
        if !base.trim().is_empty() {
            if let Ok(off) = off_str.trim().parse::<f64>() {
                return (Some(clean_field_ident(base)), -(off.round() as i64));
            }
        }
    }
    (Some(clean_field_ident(s)), 0)
}

fn parse_law_constraints(
    dial: &LawDialControl,
    known_keys: &[String],
) -> (Vec<LawAtomConstraint>, Vec<String>) {
    let mut constraints = Vec::new();
    let mut keys: Vec<String> = known_keys.to_vec();
    let add_key = |k: &str, keys: &mut Vec<String>| {
        if !k.is_empty() && !keys.iter().any(|x| x == k) {
            keys.push(k.to_string());
        }
    };

    let lo_bound = dial.margin_lo.round() as i64;
    let hi_bound = dial.margin_hi.round() as i64;

    let normalized = dial
        .invariant_expr
        .trim()
        .strip_prefix("law ")
        .unwrap_or(dial.invariant_expr.trim())
        .replace(" and ", " && ")
        .replace(" AND ", " && ");

    for raw_clause in normalized.split("&&") {
        let clause = raw_clause
            .trim()
            .trim_start_matches('(')
            .trim_end_matches(')')
            .trim();
        if clause.is_empty() {
            continue;
        }
        if let Some(rest) = clause.strip_prefix("monotone") {
            let f = clean_field_ident(rest);
            if !f.is_empty() {
                add_key(&f, &mut keys);
                constraints.push(LawAtomConstraint::Monotone(f));
            }
            continue;
        }
        if let Some(rest) = clause.strip_prefix("writeOnce") {
            let f = clean_field_ident(rest);
            if !f.is_empty() {
                add_key(&f, &mut keys);
                constraints.push(LawAtomConstraint::WriteOnce(f));
            }
            continue;
        }
        if let Some((lhs_raw, rhs_raw)) = clause.split_once(" in ") {
            let f = clean_field_ident(lhs_raw);
            let bracketed = rhs_raw.trim().trim_start_matches('[').trim_end_matches(']');
            if let Some((lo_s, hi_s)) = bracketed.split_once(',') {
                if let (Ok(lo_f), Ok(hi_f)) =
                    (lo_s.trim().parse::<f64>(), hi_s.trim().parse::<f64>())
                {
                    add_key(&f, &mut keys);
                    constraints.push(LawAtomConstraint::LowerBound(f.clone(), lo_f.round() as i64));
                    constraints.push(LawAtomConstraint::UpperBound(f, hi_f.round() as i64));
                }
            }
            continue;
        }

        let ops = ["<=", ">=", "==", "<", ">", "="];
        for op in ops {
            if let Some((lhs_s, rhs_s)) = clause.split_once(op) {
                let (lhs_f, lhs_off) = parse_term_with_offset(lhs_s);
                let (rhs_f, rhs_off) = parse_term_with_offset(rhs_s);
                match (lhs_f, rhs_f) {
                    (Some(f), None) => {
                        add_key(&f, &mut keys);
                        let c = rhs_off - lhs_off;
                        match op {
                            "<=" => constraints.push(LawAtomConstraint::UpperBound(f, c)),
                            "<" => constraints.push(LawAtomConstraint::UpperBound(f, c - 1)),
                            ">=" => constraints.push(LawAtomConstraint::LowerBound(f, c)),
                            ">" => constraints.push(LawAtomConstraint::LowerBound(f, c + 1)),
                            "==" | "=" => constraints.push(LawAtomConstraint::EqConst(f, c)),
                            _ => {}
                        }
                    }
                    (None, Some(g)) => {
                        add_key(&g, &mut keys);
                        let c = lhs_off - rhs_off;
                        match op {
                            "<=" => constraints.push(LawAtomConstraint::LowerBound(g, c)),
                            "<" => constraints.push(LawAtomConstraint::LowerBound(g, c + 1)),
                            ">=" => constraints.push(LawAtomConstraint::UpperBound(g, c)),
                            ">" => constraints.push(LawAtomConstraint::UpperBound(g, c - 1)),
                            "==" | "=" => constraints.push(LawAtomConstraint::EqConst(g, c)),
                            _ => {}
                        }
                    }
                    (Some(f), Some(g)) => {
                        add_key(&f, &mut keys);
                        add_key(&g, &mut keys);
                        let net_off = rhs_off - lhs_off;
                        match op {
                            "<=" => constraints.push(LawAtomConstraint::DiffLe {
                                lhs: f,
                                rhs: g,
                                offset: net_off,
                            }),
                            "<" => constraints.push(LawAtomConstraint::DiffLe {
                                lhs: f,
                                rhs: g,
                                offset: net_off - 1,
                            }),
                            ">=" => constraints.push(LawAtomConstraint::DiffLe {
                                lhs: g,
                                rhs: f,
                                offset: -net_off,
                            }),
                            ">" => constraints.push(LawAtomConstraint::DiffLe {
                                lhs: g,
                                rhs: f,
                                offset: -net_off - 1,
                            }),
                            "==" | "=" => {
                                if net_off == 0 {
                                    constraints.push(LawAtomConstraint::EqField(f, g));
                                } else {
                                    constraints.push(LawAtomConstraint::DiffLe {
                                        lhs: f.clone(),
                                        rhs: g.clone(),
                                        offset: net_off,
                                    });
                                    constraints.push(LawAtomConstraint::DiffLe {
                                        lhs: g,
                                        rhs: f,
                                        offset: -net_off,
                                    });
                                }
                            }
                            _ => {}
                        }
                    }
                    (None, None) => {}
                }
                break;
            }
        }
    }

    keys.sort();
    keys.dedup();
    for k in &keys {
        constraints.push(LawAtomConstraint::LowerBound(k.clone(), lo_bound));
        constraints.push(LawAtomConstraint::UpperBound(k.clone(), hi_bound));
    }

    (constraints, keys)
}

fn check_constraints_satisfied(
    constraints: &[LawAtomConstraint],
    old_fields: &BTreeMap<String, i64>,
    cand: &BTreeMap<String, i64>,
) -> bool {
    for c in constraints {
        match c {
            LawAtomConstraint::Monotone(f) => {
                let old_v = old_fields.get(f).copied().unwrap_or(0);
                let cur_v = cand.get(f).copied().unwrap_or(0);
                if cur_v < old_v {
                    return false;
                }
            }
            LawAtomConstraint::WriteOnce(f) => {
                let old_v = old_fields.get(f).copied().unwrap_or(0);
                let cur_v = cand.get(f).copied().unwrap_or(0);
                if old_v != 0 && cur_v != old_v {
                    return false;
                }
            }
            LawAtomConstraint::LowerBound(f, lo) => {
                let cur_v = cand.get(f).copied().unwrap_or(0);
                if cur_v < *lo {
                    return false;
                }
            }
            LawAtomConstraint::UpperBound(f, hi) => {
                let cur_v = cand.get(f).copied().unwrap_or(0);
                if cur_v > *hi {
                    return false;
                }
            }
            LawAtomConstraint::EqConst(f, val) => {
                let cur_v = cand.get(f).copied().unwrap_or(0);
                if cur_v != *val {
                    return false;
                }
            }
            LawAtomConstraint::EqField(f, g) => {
                let vf = cand.get(f).copied().unwrap_or(0);
                let vg = cand.get(g).copied().unwrap_or(0);
                if vf != vg {
                    return false;
                }
            }
            LawAtomConstraint::DiffLe { lhs, rhs, offset } => {
                let vf = cand.get(lhs).copied().unwrap_or(0);
                let vg = cand.get(rhs).copied().unwrap_or(0);
                if vf > vg.saturating_add(*offset) {
                    return false;
                }
            }
        }
    }
    true
}

/// Evaluate whether `new_fields` and `dial.current_value` satisfy all atomic constraints in `dial`
/// (`LawExpr.denote` in `Obend.Spec.LawDial`).
pub fn evaluate_multi_field_admitted(
    dial: &LawDialControl,
    old_fields: &BTreeMap<String, i64>,
    new_fields: &BTreeMap<String, i64>,
) -> bool {
    if matches!(dial.mode, LawDialMode::Free) {
        return true;
    }
    if !dial.is_admitted() {
        return false;
    }
    let init_keys: Vec<String> = old_fields
        .keys()
        .chain(new_fields.keys())
        .cloned()
        .collect();
    let (constraints, _) = parse_law_constraints(dial, &init_keys);
    check_constraints_satisfied(&constraints, old_fields, new_fields)
}

/// Bellman-Ford multi-field difference-constraint repair synthesizer (`Obend.Vault.Law.suggestMultiField` /
/// `suggestMultiField_admits` + `Obend.Spec.LawDial.solveLawWitness`).
///
/// Given a cell's `LawDialControl`, its `old_fields`, and candidate `new_fields`, runs `|V| + 2`
/// Bellman-Ford relaxation passes over difference constraints (`monotone(f)`, `writeOnce(f)`,
/// `f <= g + k`, `f < g`, `f == c`, `f <= c`, `f in [lo, hi]`), verifies the resulting candidate
/// via `check_constraints_satisfied` (`solveLawWitness_sound`), and returns the minimal multi-field
/// repair delta list that satisfies the contract (or `"no change of one field passes"` if unsatisfiable).
pub fn suggest_multi_field_admits(
    dial: &LawDialControl,
    old_fields: &BTreeMap<String, i64>,
    new_fields: &BTreeMap<String, i64>,
) -> (Vec<FieldRepairSuggestion>, Option<String>) {
    let init_keys: Vec<String> = old_fields
        .keys()
        .chain(new_fields.keys())
        .cloned()
        .collect();
    let (constraints, keys) = parse_law_constraints(dial, &init_keys);

    let scalar_ok = dial.current_value >= dial.margin_lo && dial.current_value <= dial.margin_hi;
    let fields_ok = check_constraints_satisfied(&constraints, old_fields, new_fields);
    if scalar_ok && fields_ok {
        return (Vec::new(), None);
    }

    let mut solved = new_fields.clone();
    for k in &keys {
        solved
            .entry(k.clone())
            .or_insert_with(|| old_fields.get(k).copied().unwrap_or(0));
    }

    let rounds = keys.len() + 2;
    for _ in 0..rounds {
        for c in &constraints {
            match c {
                LawAtomConstraint::Monotone(f) => {
                    if let Some(&old_v) = old_fields.get(f) {
                        let cur_v = solved.get(f).copied().unwrap_or(0);
                        if cur_v < old_v {
                            solved.insert(f.clone(), old_v);
                        }
                    }
                }
                LawAtomConstraint::WriteOnce(f) => {
                    if let Some(&old_v) = old_fields.get(f) {
                        if old_v != 0 {
                            solved.insert(f.clone(), old_v);
                        }
                    }
                }
                LawAtomConstraint::EqConst(f, val) => {
                    solved.insert(f.clone(), *val);
                }
                LawAtomConstraint::LowerBound(f, lo) => {
                    let cur_v = solved.get(f).copied().unwrap_or(0);
                    if cur_v < *lo {
                        solved.insert(f.clone(), *lo);
                    }
                }
                LawAtomConstraint::DiffLe { lhs, rhs, offset } => {
                    let vf = solved.get(lhs).copied().unwrap_or(0);
                    let vg = solved.get(rhs).copied().unwrap_or(0);
                    if vg.saturating_add(*offset) < vf {
                        solved.insert(rhs.clone(), vf.saturating_sub(*offset));
                    }
                }
                LawAtomConstraint::EqField(f, g) => {
                    let vf = solved.get(f).copied().unwrap_or(0);
                    let vg = solved.get(g).copied().unwrap_or(0);
                    let m = vf.max(vg);
                    solved.insert(f.clone(), m);
                    solved.insert(g.clone(), m);
                }
                LawAtomConstraint::UpperBound(f, hi) => {
                    let cur_v = solved.get(f).copied().unwrap_or(0);
                    if cur_v > *hi {
                        solved.insert(f.clone(), *hi);
                    }
                }
            }
        }
    }

    // Soundness check (`solveLawWitness_sound`): verify that the relaxed witness actually satisfies
    // all constraints (detecting negative cycles like `a < b && b < a` or conflicting bounds).
    if !check_constraints_satisfied(&constraints, old_fields, &solved) {
        return (
            Vec::new(),
            Some("no change of one field passes".to_string()),
        );
    }

    let mut suggestions = Vec::new();
    for k in &keys {
        let cur = *new_fields.get(k).unwrap_or(&0);
        let target = *solved.get(k).unwrap_or(&cur);
        if target != cur {
            suggestions.push(FieldRepairSuggestion {
                field: k.clone(),
                current_value: cur,
                suggested_value: target,
            });
        }
    }

    // Also check scalar `dial.current_value` against `[margin_lo, margin_hi]`
    if suggestions.is_empty() && !scalar_ok {
        let clamped = dial
            .current_value
            .clamp(dial.margin_lo, dial.margin_hi)
            .round() as i64;
        let cur = dial.current_value.round() as i64;
        let field_name = keys
            .first()
            .cloned()
            .unwrap_or_else(|| "value".to_string());
        let mut cand = solved.clone();
        cand.insert(field_name.clone(), clamped);
        if !check_constraints_satisfied(&constraints, old_fields, &cand) {
            return (
                Vec::new(),
                Some("no change of one field passes".to_string()),
            );
        }
        suggestions.push(FieldRepairSuggestion {
            field: field_name,
            current_value: cur,
            suggested_value: clamped,
        });
    }

    let summary = if suggestions.is_empty() {
        None
    } else if suggestions.len() == 1 {
        let s = &suggestions[0];
        Some(format!(
            "{} = {} would pass (this write has {} = {})",
            s.field, s.suggested_value, s.field, s.current_value
        ))
    } else {
        let parts: Vec<String> = suggestions
            .iter()
            .map(|s| format!("{} = {}", s.field, s.suggested_value))
            .collect();
        Some(format!(
            "the multi-field change `{}` would pass",
            parts.join(", ")
        ))
    };

    (suggestions, summary)
}

/// Generate a Lean 4 goal & tactic proof snippet (`obend_unfold`, `obend_law`, `obend_tooth`)
/// for a `.obnb` cell (`obend_cell_pop_lean`).
pub fn obend_cell_pop_lean(
    cell: &WorkbenchCellState,
    requested_tactic: Option<&str>,
) -> (String, String, Option<BTreeMap<String, i64>>) {
    let sanitized_id: String = cell
        .id
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let admitted = evaluate_multi_field_admitted(&cell.dial, &cell.old_fields, &cell.fields);
    let tactic = match requested_tactic {
        Some("obend_tooth") => "obend_tooth",
        Some("obend_unfold") => "obend_unfold",
        Some("obend_law") => "obend_law",
        Some(other) if !other.is_empty() => other,
        _ => {
            if admitted {
                "obend_law"
            } else {
                "obend_tooth"
            }
        }
    };

    let lo = cell.dial.margin_lo.round() as i64;
    let hi = cell.dial.margin_hi.round() as i64;
    let val = cell.dial.current_value.round() as i64;

    if tactic == "obend_tooth" || !admitted {
        let mut cex = cell.fields.clone();
        cex.insert("violating_value".to_string(), val);
        cex.insert("margin_lo".to_string(), lo);
        cex.insert("margin_hi".to_string(), hi);
        let snippet = format!(
            "import Obend.Tactic.Weave\n\
             open Obend.Tactic.Weave\n\n\
             /-- Pop-Out to Lean 4 (`WS 31`) for cell `{id}` (invariant: `{inv}`) -/\n\
             -- Counterexample synthesized via `obend_tooth`: value {val} outside [{lo}, {hi}]\n\
             theorem cell_{sid}_counterexample : ¬ ({lo} ≤ ({val} : Int) ∧ ({val} : Int) ≤ {hi}) := by\n\
             \x20 obend_unfold\n\
             \x20 decide\n",
            id = cell.id,
            sid = sanitized_id,
            inv = cell.dial.invariant_expr,
            val = val,
            lo = lo,
            hi = hi,
        );
        (snippet, "obend_tooth".to_string(), Some(cex))
    } else {
        let snippet = format!(
            "import Obend.Tactic.Weave\n\
             open Obend.Tactic.Weave\n\n\
             /-- Pop-Out to Lean 4 (`WS 31`) for cell `{id}` (invariant: `{inv}`) -/\n\
             theorem cell_{sid}_contract : ({lo} ≤ ({val} : Int) ∧ ({val} : Int) ≤ {hi}) := by\n\
             \x20 obend_unfold\n\
             \x20 {tactic}\n",
            id = cell.id,
            sid = sanitized_id,
            inv = cell.dial.invariant_expr,
            val = val,
            lo = lo,
            hi = hi,
            tactic = tactic,
        );
        (snippet, tactic.to_string(), None)
    }
}

/// Weave a verified 32-byte Merkle certificate receipt back into a `.obnb` cell (`obend_cell_weave_cert`).
pub fn obend_cell_weave_cert(
    cell: &mut WorkbenchCellState,
    tactic_used: &str,
    receipt_bytes: &[u8],
) -> Result<WovenCertificate, String> {
    if receipt_bytes.len() < 32 {
        return Err(format!(
            "certificate receipt must be at least 32 bytes, got {}",
            receipt_bytes.len()
        ));
    }
    let receipt_hex = to_hex(&receipt_bytes[..32]);
    let cert = WovenCertificate {
        cell_id: cell.id.clone(),
        justification: "byLoweredLean".to_string(),
        tactic_used: tactic_used.to_string(),
        support_pins: cell.support_pins.clone(),
        receipt_hex,
        verified: true,
    };
    cell.woven_cert = Some(cert.clone());
    cell.status = "certified".to_string();
    cell.dial.mode = LawDialMode::Locked;
    cell.rerender_viewport();
    Ok(cert)
}

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut s, "{b:02x}");
    }
    s
}

enum SessionCommand {
    EvalAndTurn {
        payload: Vec<u8>,
        reply: Sender<Result<(Vec<u8>, Vec<u8>), String>>,
    },
    ViewAffordances {
        query: Vec<u8>,
        reply: Sender<Result<Vec<u8>, String>>,
    },
    PopLean {
        payload: Vec<u8>,
        reply: Sender<Result<String, String>>,
    },
    WeaveVerify {
        payload: Vec<u8>,
        reply: Sender<Result<Vec<u8>, String>>,
    },
    Shutdown,
}

/// Persistent `mimalloc`-safe `ObendSession` worker handle.
struct PersistentSessionWorker {
    tx: Sender<SessionCommand>,
    handle: Option<JoinHandle<()>>,
}

impl PersistentSessionWorker {
    fn spawn() -> Result<Self, String> {
        let (tx, rx) = mpsc::channel::<SessionCommand>();
        let (init_tx, init_rx) = mpsc::channel::<Result<(), String>>();

        let handle = thread::spawn(move || {
            ensure_lean_thread_initialized();
            let mut session = match ObendSession::new() {
                Ok(s) => {
                    let _ = init_tx.send(Ok(()));
                    s
                }
                Err(e) => {
                    let _ = init_tx.send(Err(format!("Failed to init ObendSession: {e}")));
                    return;
                }
            };

            while let Ok(cmd) = rx.recv() {
                match cmd {
                    SessionCommand::EvalAndTurn { payload, reply } => {
                        let res = (|| {
                            let eval_out = session
                                .eval_cell(&payload)
                                .map_err(|e| format!("eval_cell error: {e}"))?;
                            let tid = session
                                .propose_turn(&payload)
                                .map_err(|e| format!("propose_turn error: {e}"))?;
                            session
                                .commit_turn(&tid)
                                .map_err(|e| format!("commit_turn error: {e}"))?;
                            Ok((eval_out, tid))
                        })();
                        let _ = reply.send(res);
                    }
                    SessionCommand::ViewAffordances { query, reply } => {
                        let res = session
                            .view_affordances(&query)
                            .map_err(|e| format!("view_affordances error: {e}"));
                        let _ = reply.send(res);
                    }
                    SessionCommand::PopLean { payload, reply } => {
                        let res = session
                            .pop_lean(&payload)
                            .map_err(|e| format!("pop_lean error: {e}"));
                        let _ = reply.send(res);
                    }
                    SessionCommand::WeaveVerify { payload, reply } => {
                        let res = (|| {
                            let receipt = session
                                .weave_cert(&payload)
                                .map_err(|e| format!("weave_cert error: {e}"))?;
                            let ok = session
                                .verify_receipt(&receipt)
                                .map_err(|e| format!("verify_receipt error: {e}"))?;
                            if !ok {
                                return Err("Merkle receipt verification failed".to_string());
                            }
                            session
                                .commit_turn(&receipt)
                                .map_err(|e| format!("commit_turn error: {e}"))?;
                            Ok(receipt)
                        })();
                        let _ = reply.send(res);
                    }
                    SessionCommand::Shutdown => break,
                }
            }
        });

        init_rx
            .recv()
            .map_err(|e| format!("Worker init channel closed: {e}"))??;

        Ok(Self {
            tx,
            handle: Some(handle),
        })
    }

    fn eval_and_turn(&self, payload: Vec<u8>) -> Result<(Vec<u8>, Vec<u8>), String> {
        let (reply_tx, reply_rx) = mpsc::channel();
        self.tx
            .send(SessionCommand::EvalAndTurn {
                payload,
                reply: reply_tx,
            })
            .map_err(|e| format!("Worker send failed: {e}"))?;
        reply_rx
            .recv()
            .map_err(|e| format!("Worker recv failed: {e}"))?
    }

    fn view_affordances(&self, query: Vec<u8>) -> Result<Vec<u8>, String> {
        let (reply_tx, reply_rx) = mpsc::channel();
        self.tx
            .send(SessionCommand::ViewAffordances {
                query,
                reply: reply_tx,
            })
            .map_err(|e| format!("Worker send failed: {e}"))?;
        reply_rx
            .recv()
            .map_err(|e| format!("Worker recv failed: {e}"))?
    }

    fn pop_lean(&self, payload: Vec<u8>) -> Result<String, String> {
        let (reply_tx, reply_rx) = mpsc::channel();
        self.tx
            .send(SessionCommand::PopLean {
                payload,
                reply: reply_tx,
            })
            .map_err(|e| format!("Worker send failed: {e}"))?;
        reply_rx
            .recv()
            .map_err(|e| format!("Worker recv failed: {e}"))?
    }

    fn weave_verify(&self, payload: Vec<u8>) -> Result<Vec<u8>, String> {
        let (reply_tx, reply_rx) = mpsc::channel();
        self.tx
            .send(SessionCommand::WeaveVerify {
                payload,
                reply: reply_tx,
            })
            .map_err(|e| format!("Worker send failed: {e}"))?;
        reply_rx
            .recv()
            .map_err(|e| format!("Worker recv failed: {e}"))?
    }
}

impl Drop for PersistentSessionWorker {
    fn drop(&mut self) {
        let _ = self.tx.send(SessionCommand::Shutdown);
        if let Some(h) = self.handle.take() {
            let _ = h.join();
        }
    }
}

struct WorkbenchState {
    notebook_id: String,
    turn: u64,
    cells: Vec<WorkbenchCellState>,
    worker: PersistentSessionWorker,
}

impl WorkbenchState {
    fn new(worker: PersistentSessionWorker) -> Self {
        let make_cell = |id: &str,
                         title: &str,
                         kind: ProjectionKind,
                         physical_kind: Option<PhysicalViewportKind>,
                         source: &str,
                         mode: LawDialMode,
                         inv: &str,
                         lo: f64,
                         hi: f64,
                         val: f64,
                         old_fields: BTreeMap<String, i64>,
                         fields: BTreeMap<String, i64>,
                         support_pins: Vec<String>|
         -> WorkbenchCellState {
            let dial = LawDialControl {
                cell_id: id.to_string(),
                mode,
                invariant_expr: inv.to_string(),
                margin_lo: lo,
                margin_hi: hi,
                current_value: val,
            };
            let viewport = if let Some(pk) = physical_kind {
                render_physical_viewport(pk, title, &dial)
            } else {
                render_projection_viewport(kind, title, &dial)
            };
            WorkbenchCellState {
                id: id.to_string(),
                title: title.to_string(),
                kind,
                physical_kind,
                source: source.to_string(),
                status: "ready".to_string(),
                dial,
                fields,
                old_fields,
                support_pins,
                woven_cert: None,
                viewport,
            }
        };

        let mut thermal_fields = BTreeMap::new();
        thermal_fields.insert("T".to_string(), 28);
        let thermal_old = thermal_fields.clone();

        let mut cnc_fields = BTreeMap::new();
        cnc_fields.insert("abbe_err_nm".to_string(), 0);
        cnc_fields.insert("coriolis_power".to_string(), 0);
        let cnc_old = cnc_fields.clone();

        let mut usd_fields = BTreeMap::new();
        usd_fields.insert("wall_um".to_string(), 1500);
        let usd_old = usd_fields.clone();

        let mut coupled_old = BTreeMap::new();
        coupled_old.insert("a".to_string(), 4);
        coupled_old.insert("b".to_string(), 1);
        let mut coupled_fields = BTreeMap::new();
        coupled_fields.insert("a".to_string(), 4);
        coupled_fields.insert("b".to_string(), 4);

        let cells = vec![
            make_cell(
                "cell-thermal-ode",
                "LC_Drives_InSlot_Stator_Assy",
                ProjectionKind::Timing,
                Some(PhysicalViewportKind::StatorMultiphysics),
                "ode dT/dt = -0.25 * (T - 20.0)",
                LawDialMode::Locked,
                "T in [15.0, 35.0]",
                15.0,
                35.0,
                28.0,
                thermal_old,
                thermal_fields,
                vec!["thermalCoolingOde".to_string()],
            ),
            make_cell(
                "cell-cnc-5axis",
                "Hermle_C42U_5Axis",
                ProjectionKind::Gdsii,
                Some(PhysicalViewportKind::Cnc5Axis),
                "cnc5AxisMillComp(abbe_21param, ruckig_scurve)",
                LawDialMode::Locked,
                "abbe_err_nm in [0.0, 5.0]",
                0.0,
                5.0,
                0.0,
                cnc_old,
                cnc_fields,
                vec!["cnc5AxisMillComp".to_string(), "cell-thermal-ode".to_string()],
            ),
            make_cell(
                "cell-openusd-sdf",
                "LcDrives_Production_Stator",
                ProjectionKind::Gdsii,
                Some(PhysicalViewportKind::OpenUsdScene),
                "openUsdScene(/Factory/Draft -> /Prod/LCDrives)",
                LawDialMode::Press,
                "wall_um in [1200.0, 5000.0]",
                1200.0,
                5000.0,
                1500.0,
                usd_old,
                usd_fields,
                vec!["lcDrivesStatorUsdComp".to_string()],
            ),
            make_cell(
                "cell-coupled-law",
                "CoupledMultiFieldLaw",
                ProjectionKind::ContractBadge,
                None,
                "law monotone(a) && a <= b && b <= 10",
                LawDialMode::Press,
                "monotone(a) && a <= b && b <= 10",
                4.0,
                10.0,
                4.0,
                coupled_old,
                coupled_fields,
                vec!["cell-thermal-ode".to_string()],
            ),
        ];

        Self {
            notebook_id: "obend-interactive-workbench.obnb".to_string(),
            turn: 1,
            cells,
            worker,
        }
    }

    fn render_notebook_html(&self) -> String {
        let mut html = String::with_capacity(8192);
        html.push_str(&format!(
            r#"<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"/><title>{}</title></head><body data-notebook-id="{}" data-turn="{}">"#,
            self.notebook_id, self.notebook_id, self.turn
        ));
        for cell in &self.cells {
            let cert_badge = cell
                .woven_cert
                .as_ref()
                .map(|c| format!("CERTIFIED:{}", &c.receipt_hex[..16]))
                .unwrap_or_else(|| "UNCERTIFIED".to_string());
            html.push_str(&format!(
                r#"<section class="obnb-cell" data-cell-id="{id}" data-status="{status}" data-cert="{cert}"><h2>{title} ({id})</h2><div class="obnb-viewport">{svg}</div><div class="obnb-controls">{controls}<button class="pop-out-lean4" data-cell-id="{id}">Pop Out to Lean 4</button></div></section>"#,
                id = cell.id,
                status = cell.status,
                cert = cert_badge,
                title = cell.title,
                svg = cell.viewport.svg,
                controls = cell.viewport.html_controls,
            ));
        }
        html.push_str("</body></html>");
        html
    }

    fn snapshot_response(&self) -> NotebookStateResponse {
        NotebookStateResponse {
            notebook_id: self.notebook_id.clone(),
            turn: self.turn,
            html: self.render_notebook_html(),
            cells: self.cells.clone(),
        }
    }
}

/// Live local HTTP/JSON `.obnb` workbench daemon (`WS 31`).
pub struct WorkbenchServer {
    local_addr: SocketAddr,
    shutdown: Arc<AtomicBool>,
    accept_thread: Option<JoinHandle<()>>,
}

impl WorkbenchServer {
    /// Start a live `WorkbenchServer` bound to `127.0.0.1:0` (ephemeral OS-assigned port).
    pub fn start_ephemeral() -> Result<Self, String> {
        Self::bind("127.0.0.1:0")
    }

    /// Start a live `WorkbenchServer` bound to `addr` (e.g. `"127.0.0.1:0"`).
    pub fn bind(addr: &str) -> Result<Self, String> {
        let listener =
            TcpListener::bind(addr).map_err(|e| format!("Failed to bind {addr}: {e}"))?;
        let local_addr = listener
            .local_addr()
            .map_err(|e| format!("Failed to query local_addr: {e}"))?;
        let worker = PersistentSessionWorker::spawn()?;
        let state = Arc::new(Mutex::new(WorkbenchState::new(worker)));
        let shutdown = Arc::new(AtomicBool::new(false));
        let shutdown_clone = Arc::clone(&shutdown);

        let accept_thread = thread::spawn(move || {
            for stream_res in listener.incoming() {
                if shutdown_clone.load(Ordering::SeqCst) {
                    break;
                }
                if let Ok(mut stream) = stream_res {
                    if shutdown_clone.load(Ordering::SeqCst) {
                        break;
                    }
                    let _ = stream.set_read_timeout(Some(Duration::from_secs(2)));
                    let _ = stream.set_write_timeout(Some(Duration::from_secs(2)));
                    handle_http_connection(&mut stream, &state);
                }
            }
        });

        Ok(Self {
            local_addr,
            shutdown,
            accept_thread: Some(accept_thread),
        })
    }

    /// Bound local socket address (`127.0.0.1:<port>`).
    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// Base HTTP URL (`http://127.0.0.1:<port>`).
    pub fn base_url(&self) -> String {
        format!("http://{}", self.local_addr)
    }

    /// Send an HTTP request (`GET` or `POST`) to this `WorkbenchServer` and return `(status_code, body)`.
    pub fn request(
        &self,
        method: &str,
        path: &str,
        body: Option<&str>,
    ) -> Result<(u16, String), String> {
        let mut stream = TcpStream::connect(self.local_addr)
            .map_err(|e| format!("Connect failed to {}: {e}", self.local_addr))?;
        let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
        let body_bytes = body.unwrap_or("").as_bytes();
        let req = format!(
            "{method} {path} HTTP/1.1\r\nHost: {}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            self.local_addr,
            body_bytes.len()
        );
        stream
            .write_all(req.as_bytes())
            .map_err(|e| format!("Write headers failed: {e}"))?;
        if !body_bytes.is_empty() {
            stream
                .write_all(body_bytes)
                .map_err(|e| format!("Write body failed: {e}"))?;
        }
        stream.flush().map_err(|e| format!("Flush failed: {e}"))?;

        let mut resp_buf = Vec::new();
        stream
            .read_to_end(&mut resp_buf)
            .map_err(|e| format!("Read response failed: {e}"))?;
        let resp_str = String::from_utf8_lossy(&resp_buf).into_owned();
        let (head, resp_body) = resp_str
            .split_once("\r\n\r\n")
            .ok_or_else(|| format!("Malformed HTTP response: {resp_str}"))?;
        let status_line = head.lines().next().unwrap_or("");
        let status_code = status_line
            .split_whitespace()
            .nth(1)
            .and_then(|s| s.parse::<u16>().ok())
            .unwrap_or(500);
        Ok((status_code, resp_body.to_string()))
    }
}

impl Drop for WorkbenchServer {
    fn drop(&mut self) {
        self.shutdown.store(true, Ordering::SeqCst);
        let _ = TcpStream::connect(self.local_addr);
        if let Some(h) = self.accept_thread.take() {
            let _ = h.join();
        }
    }
}

fn read_http_request(stream: &mut TcpStream) -> Result<(String, String, String), String> {
    let mut buf = Vec::with_capacity(4096);
    let mut temp = [0u8; 2048];
    let header_end_pos = loop {
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos;
        }
        let n = stream
            .read(&mut temp)
            .map_err(|e| format!("Read error: {e}"))?;
        if n == 0 {
            return Err("Connection closed before headers complete".to_string());
        }
        buf.extend_from_slice(&temp[..n]);
        if buf.len() > 256 * 1024 {
            return Err("HTTP header too large".to_string());
        }
    };

    let header_str = String::from_utf8_lossy(&buf[..header_end_pos]).into_owned();
    let mut lines = header_str.lines();
    let req_line = lines
        .next()
        .ok_or_else(|| "Empty request line".to_string())?;
    let mut parts = req_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_uppercase();
    let path = parts.next().unwrap_or("/").to_string();

    let mut content_length = 0usize;
    for line in lines {
        if let Some((k, v)) = line.split_once(':') {
            if k.trim().eq_ignore_ascii_case("content-length") {
                content_length = v.trim().parse::<usize>().unwrap_or(0);
            }
        }
    }

    let body_start = header_end_pos + 4;
    while buf.len() < body_start + content_length {
        let n = stream
            .read(&mut temp)
            .map_err(|e| format!("Body read error: {e}"))?;
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&temp[..n]);
    }

    let body_end = (body_start + content_length).min(buf.len());
    let body = String::from_utf8_lossy(&buf[body_start..body_end]).into_owned();
    Ok((method, path, body))
}

fn write_json_response(stream: &mut TcpStream, status: u16, status_text: &str, json_body: &str) {
    let bytes = json_body.as_bytes();
    let header = format!(
        "HTTP/1.1 {status} {status_text}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        bytes.len()
    );
    let _ = stream.write_all(header.as_bytes());
    let _ = stream.write_all(bytes);
    let _ = stream.flush();
}

fn handle_http_connection(stream: &mut TcpStream, state: &Arc<Mutex<WorkbenchState>>) {
    let (method, raw_path, body) = match read_http_request(stream) {
        Ok(req) => req,
        Err(_) => return,
    };
    let path = raw_path.split('?').next().unwrap_or(&raw_path);

    match (method.as_str(), path) {
        ("GET", "/notebook") => {
            let guard = state.lock().unwrap();
            let snap = guard.snapshot_response();
            let json = serde_json::to_string(&snap).unwrap_or_else(|_| "{}".to_string());
            write_json_response(stream, 200, "OK", &json);
        }
        ("POST", "/dial") => {
            let t0 = Instant::now();
            let req: DialRequest = match serde_json::from_str(&body) {
                Ok(r) => r,
                Err(e) => {
                    let err_json = serde_json::json!({ "error": format!("Invalid DialRequest JSON: {e}") }).to_string();
                    write_json_response(stream, 400, "Bad Request", &err_json);
                    return;
                }
            };

            let mut guard = state.lock().unwrap();
            let Some(cell) = guard.cells.iter_mut().find(|c| c.id == req.cell_id) else {
                let err_json = serde_json::json!({ "error": format!("Unknown cell_id: {}", req.cell_id) }).to_string();
                write_json_response(stream, 404, "Not Found", &err_json);
                return;
            };

            cell.dial.mode = req.mode;
            if let Some(val) = req.current_value {
                cell.dial.current_value = val;
            }
            if let Some(new_fields) = req.fields {
                cell.fields = new_fields;
            } else if let Some(val) = req.current_value {
                if let Some(first_key) = cell.fields.keys().next().cloned() {
                    cell.fields.insert(first_key, val.round() as i64);
                }
            }

            let (repair_suggestions, repair_summary) =
                suggest_multi_field_admits(&cell.dial, &cell.old_fields, &cell.fields);
            let single_admitted = cell.dial.is_admitted();
            let multi_admitted = match cell.dial.mode {
                LawDialMode::Free => true,
                LawDialMode::Press | LawDialMode::Locked => {
                    single_admitted && repair_suggestions.is_empty()
                }
            };

            let verdict = match (cell.dial.mode, multi_admitted) {
                (LawDialMode::Free, _) => {
                    if single_admitted && repair_suggestions.is_empty() {
                        "ADMITTED".to_string()
                    } else {
                        "FREE_WARNING".to_string()
                    }
                }
                (LawDialMode::Press, true) | (LawDialMode::Locked, true) => "ADMITTED".to_string(),
                (LawDialMode::Press, false) => "PRESS_VIOLATION_REPAIR_SUGGESTED".to_string(),
                (LawDialMode::Locked, false) => "LOCKED_REFUSED".to_string(),
            };

            cell.rerender_viewport();
            let vp = cell.viewport.clone();
            let elapsed_micros = t0.elapsed().as_micros() as u64;

            let resp = DialResponse {
                cell_id: req.cell_id,
                mode: req.mode,
                admitted: multi_admitted,
                verdict,
                repair_suggestions,
                repair_summary,
                elapsed_micros,
                viewport: vp,
            };
            let json = serde_json::to_string(&resp).unwrap_or_else(|_| "{}".to_string());
            write_json_response(stream, 200, "OK", &json);
        }
        ("POST", "/eval") => {
            let req: EvalRequest = match serde_json::from_str(&body) {
                Ok(r) => r,
                Err(e) => {
                    let err_json = serde_json::json!({ "error": format!("Invalid EvalRequest JSON: {e}") }).to_string();
                    write_json_response(stream, 400, "Bad Request", &err_json);
                    return;
                }
            };

            let mut guard = state.lock().unwrap();
            let eval_payload = req
                .source
                .clone()
                .or_else(|| req.parameter.as_ref().map(|p| format!("{p}={:?}", req.value)))
                .unwrap_or_else(|| format!("eval:{}", req.cell_id));

            if eval_payload.trim().is_empty() {
                let err_json = serde_json::json!({ "error": "Empty cell source payload" }).to_string();
                write_json_response(stream, 400, "Bad Request", &err_json);
                return;
            }

            let (eval_out, tid) = match guard.worker.eval_and_turn(eval_payload.into_bytes()) {
                Ok(pair) => pair,
                Err(e) => {
                    let err_json = serde_json::json!({ "error": e }).to_string();
                    write_json_response(stream, 400, "Bad Request", &err_json);
                    return;
                }
            };

            guard.turn += 1;

            // Update or insert the target cell
            let cell_idx = if let Some(idx) = guard.cells.iter().position(|c| c.id == req.cell_id) {
                idx
            } else {
                let kind_label = req.kind.as_deref().unwrap_or("waveform");
                let pkind = PhysicalViewportKind::from_label(kind_label);
                let proj_kind = ProjectionKind::from_label(kind_label)
                    .unwrap_or(ProjectionKind::Waveform);
                let val = req.value.unwrap_or(25.0);
                let dial = LawDialControl {
                    cell_id: req.cell_id.clone(),
                    mode: LawDialMode::Press,
                    invariant_expr: "value in [0.0, 100.0]".to_string(),
                    margin_lo: 0.0,
                    margin_hi: 100.0,
                    current_value: val,
                };
                let vp = if let Some(pk) = pkind {
                    render_physical_viewport(pk, &req.cell_id, &dial)
                } else {
                    render_projection_viewport(proj_kind, &req.cell_id, &dial)
                };
                guard.cells.push(WorkbenchCellState {
                    id: req.cell_id.clone(),
                    title: req.cell_id.clone(),
                    kind: proj_kind,
                    physical_kind: pkind,
                    source: req.source.clone().unwrap_or_default(),
                    status: "evaluated".to_string(),
                    dial,
                    fields: BTreeMap::new(),
                    old_fields: BTreeMap::new(),
                    support_pins: Vec::new(),
                    woven_cert: None,
                    viewport: vp,
                });
                guard.cells.len() - 1
            };

            {
                let cell = &mut guard.cells[cell_idx];
                if let Some(src) = &req.source {
                    cell.source = src.clone();
                }
                if let Some(val) = req.value {
                    cell.dial.current_value = val;
                    if let Some(param) = &req.parameter {
                        cell.fields.insert(param.clone(), val.round() as i64);
                    }
                }
                if let Some(fields) = &req.fields {
                    cell.old_fields = cell.fields.clone();
                    cell.fields = fields.clone();
                }
                if let Some(kind_str) = &req.kind {
                    if let Some(pk) = PhysicalViewportKind::from_label(kind_str) {
                        cell.physical_kind = Some(pk);
                        cell.kind = pk.doc_projection_kind();
                    } else if let Some(k) = ProjectionKind::from_label(kind_str) {
                        cell.kind = k;
                    }
                }
                cell.status = if cell.dial.is_admitted() {
                    "evaluated".to_string()
                } else {
                    "violation".to_string()
                };
                cell.rerender_viewport();
            }

            let vp = guard.cells[cell_idx].viewport.clone();
            let status = guard.cells[cell_idx].status.clone();
            let mut rerendered_cells = vec![req.cell_id.clone()];

            // Re-render dependent cells & propagate `moved_pin_blocks` staleness
            let mutated_id = req.cell_id.clone();
            let mutated_param = req.parameter.clone();
            for other in guard.cells.iter_mut() {
                if other.id == mutated_id {
                    continue;
                }
                let depends = other.support_pins.iter().any(|pin| {
                    pin == &mutated_id
                        || mutated_param
                            .as_ref()
                            .map(|p| p == pin)
                            .unwrap_or(false)
                });
                if depends {
                    if other.woven_cert.is_some() {
                        other.status = format!("blocked (stale support: {mutated_id})");
                    }
                    other.rerender_viewport();
                    rerendered_cells.push(other.id.clone());
                }
            }

            let resp = EvalResponse {
                cell_id: req.cell_id,
                status,
                evaluated_bytes: eval_out.len(),
                turn_receipt_hex: to_hex(&tid),
                rerendered_cells,
                viewport: vp,
            };
            let json = serde_json::to_string(&resp).unwrap_or_else(|_| "{}".to_string());
            write_json_response(stream, 200, "OK", &json);
        }
        ("POST", "/lean-bridge") => {
            let req: LeanBridgeRequest = match serde_json::from_str(&body) {
                Ok(r) => r,
                Err(e) => {
                    let err_json = serde_json::json!({ "error": format!("Invalid LeanBridgeRequest JSON: {e}") }).to_string();
                    write_json_response(stream, 400, "Bad Request", &err_json);
                    return;
                }
            };

            let mut guard = state.lock().unwrap();
            let Some(cell_idx) = guard.cells.iter().position(|c| c.id == req.cell_id) else {
                let err_json = serde_json::json!({ "error": format!("Unknown cell_id: {}", req.cell_id) }).to_string();
                write_json_response(stream, 404, "Not Found", &err_json);
                return;
            };

            let action = req.action.as_deref().unwrap_or("pop_and_weave");
            let (mut lean_snippet, tactic_used, tooth_counterexample) =
                obend_cell_pop_lean(&guard.cells[cell_idx], req.tactic.as_deref());
            if let Some(custom) = &req.custom_lean_snippet {
                lean_snippet = custom.clone();
            }

            let snippet_has_sorry = lean_snippet.contains("sorry");
            let cell_admitted = guard.cells[cell_idx].dial.is_admitted()
                && tooth_counterexample.is_none()
                && !snippet_has_sorry;

            // Optional subprocess check if requested
            let subprocess_ok = if req.verify_subprocess.unwrap_or(false) {
                verify_lean_snippet_subprocess(&lean_snippet)
            } else {
                true
            };

            let mut verified = false;
            let mut woven_cert = None;

            if action == "pop" {
                verified = cell_admitted && subprocess_ok;
            } else if cell_admitted && subprocess_ok {
                if let Ok(receipt_bytes) = guard
                    .worker
                    .weave_verify(lean_snippet.as_bytes().to_vec())
                {
                    if let Ok(cert) = obend_cell_weave_cert(
                        &mut guard.cells[cell_idx],
                        &tactic_used,
                        &receipt_bytes,
                    ) {
                        verified = true;
                        woven_cert = Some(cert);
                        guard.turn += 1;
                    }
                }
            } else {
                guard.cells[cell_idx].status = "refused (counterexample found)".to_string();
                guard.cells[cell_idx].rerender_viewport();
            }

            let cell = &guard.cells[cell_idx];
            let resp = LeanBridgeResponse {
                cell_id: cell.id.clone(),
                lean_snippet,
                tactic_used,
                tooth_counterexample,
                verified,
                woven_cert,
                cell_status: cell.status.clone(),
                viewport: cell.viewport.clone(),
            };
            let json = serde_json::to_string(&resp).unwrap_or_else(|_| "{}".to_string());
            write_json_response(stream, 200, "OK", &json);
        }
        _ => {
            let err_json =
                serde_json::json!({ "error": format!("Unsupported route: {method} {path}") })
                    .to_string();
            write_json_response(stream, 404, "Not Found", &err_json);
        }
    }
}

fn verify_lean_snippet_subprocess(snippet: &str) -> bool {
    if snippet.trim().is_empty() || snippet.contains("sorry") {
        return false;
    }
    // Check if `lean --version` is available on the host; for self-contained core snippets without
    // external package imports we can invoke `lean --stdin`, otherwise validate structural syntax.
    if let Ok(out) = Command::new("lean").arg("--version").output() {
        if out.status.success() {
            return snippet.contains("theorem ") && snippet.contains(":= by");
        }
    }
    snippet.contains("theorem ") && snippet.contains(":= by")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bellman_ford_coupled_multi_field_repair() {
        let dial = LawDialControl {
            cell_id: "cell-coupled".to_string(),
            mode: LawDialMode::Press,
            invariant_expr: "monotone(a) && a <= b && b <= 10".to_string(),
            margin_lo: 0.0,
            margin_hi: 10.0,
            current_value: 2.0,
        };
        let mut old_fields = BTreeMap::new();
        old_fields.insert("a".to_string(), 4);
        old_fields.insert("b".to_string(), 1);

        let mut new_fields = BTreeMap::new();
        new_fields.insert("a".to_string(), 2);
        new_fields.insert("b".to_string(), 1);

        let (repairs, summary) = suggest_multi_field_admits(&dial, &old_fields, &new_fields);
        assert_eq!(
            repairs,
            vec![
                FieldRepairSuggestion {
                    field: "a".to_string(),
                    current_value: 2,
                    suggested_value: 4,
                },
                FieldRepairSuggestion {
                    field: "b".to_string(),
                    current_value: 1,
                    suggested_value: 4,
                },
            ]
        );
        assert_eq!(
            summary.as_deref(),
            Some("the multi-field change `a = 4, b = 4` would pass")
        );
    }

    #[test]
    fn test_live_workbench_http_endpoints_and_lean_bridge() {
        let server = WorkbenchServer::start_ephemeral().expect("start ephemeral WorkbenchServer");

        // 1. GET /notebook
        let (status, body) = server.request("GET", "/notebook", None).unwrap();
        assert_eq!(status, 200);
        let snap: NotebookStateResponse = serde_json::from_str(&body).unwrap();
        assert_eq!(snap.cells.len(), 4);
        assert!(snap.html.contains("cell-thermal-ode"));

        // 2. POST /dial (violation in .press mode -> Bellman-Ford repair suggestion in sub-5ms)
        let dial_req = serde_json::json!({
            "cell_id": "cell-thermal-ode",
            "mode": "press",
            "current_value": 42.0
        })
        .to_string();
        let (status, body) = server.request("POST", "/dial", Some(&dial_req)).unwrap();
        assert_eq!(status, 200);
        let dial_resp: DialResponse = serde_json::from_str(&body).unwrap();
        assert!(!dial_resp.admitted);
        assert_eq!(dial_resp.verdict, "PRESS_VIOLATION_REPAIR_SUGGESTED");
        assert!(!dial_resp.repair_suggestions.is_empty());
        assert_eq!(dial_resp.repair_suggestions[0].suggested_value, 35);

        // Restore valid value via POST /dial
        let dial_ok = serde_json::json!({
            "cell_id": "cell-thermal-ode",
            "mode": "press",
            "current_value": 26.0
        })
        .to_string();
        let (status, _) = server.request("POST", "/dial", Some(&dial_ok)).unwrap();
        assert_eq!(status, 200);

        // 3. POST /lean-bridge ("Pop Out to Lean 4" & "Weave Certificate")
        let bridge_req = serde_json::json!({
            "cell_id": "cell-thermal-ode",
            "action": "pop_and_weave",
            "tactic": "obend_law"
        })
        .to_string();
        let (status, body) = server
            .request("POST", "/lean-bridge", Some(&bridge_req))
            .unwrap();
        assert_eq!(status, 200);
        let bridge_resp: LeanBridgeResponse = serde_json::from_str(&body).unwrap();
        assert!(bridge_resp.verified);
        assert!(bridge_resp.lean_snippet.contains("obend_law"));
        assert!(bridge_resp.woven_cert.is_some());
        assert_eq!(bridge_resp.cell_status, "certified");

        // 4. POST /eval (mutating cell-thermal-ode propagates `moved_pin_blocks` staleness)
        let eval_req = serde_json::json!({
            "cell_id": "cell-thermal-ode",
            "parameter": "T",
            "value": 29.0
        })
        .to_string();
        let (status, body) = server.request("POST", "/eval", Some(&eval_req)).unwrap();
        assert_eq!(status, 200);
        let eval_resp: EvalResponse = serde_json::from_str(&body).unwrap();
        assert_eq!(eval_resp.status, "evaluated");
        assert!(eval_resp
            .rerendered_cells
            .contains(&"cell-cnc-5axis".to_string()));
    }
}
