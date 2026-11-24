#![forbid(unsafe_code)]
//! Bounded-frame newline-delimited JSON channel (`LineChannel`) & `ConfinedBrain` state machine.
//!
//! Quarried and hardened from `breadstuffs/grain-jail/src/{lib.rs,protocol.rs}`:
//! - Enforces a strict byte-level frame ceiling (`DEFAULT_MAX_LINE_BYTES = 1 MiB`) BEFORE UTF-8
//!   decoding or JSON parsing, refusing oversized frames and NUL bytes fail-closed.
//! - Poisons the channel after any framing/flood violation so the remainder of a split attacker
//!   frame can never be parsed as a fresh command on a subsequent `recv()`.
//! - Replaces recursive blank-line skipping with a bounded iterative loop
//!   (`MAX_CONSECUTIVE_EMPTY_LINES = 64`), eliminating stack-overflow DoS on `"\n".repeat(N)`.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, BufRead, Read, Write};

use serde::{Deserialize, Serialize};

/// Default per-frame byte ceiling (`1 MiB`) for confined-body IPC messages.
pub const DEFAULT_MAX_LINE_BYTES: usize = 1 << 20;

/// Maximum consecutive blank keep-alive lines permitted before refusing as a frame flood.
pub const MAX_CONSECUTIVE_EMPTY_LINES: usize = 64;

/// A message from a jailed body to the grain host.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BodyMsg {
    Propose(Proposal),
    Done(DoneNote),
}

/// One proposed tool/cell action from the jailed body.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proposal {
    pub tool: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub args: Option<BTreeMap<String, String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub amount_cents: Option<i64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value: Option<String>,
}

impl Proposal {
    pub fn invoke(tool: impl Into<String>) -> Self {
        Self {
            tool: tool.into(),
            args: None,
            amount_cents: None,
            path: None,
            value: None,
        }
    }

    pub fn op(tool: impl Into<String>, args: impl IntoIterator<Item = (String, String)>) -> Self {
        Self {
            tool: tool.into(),
            args: Some(args.into_iter().collect()),
            amount_cents: None,
            path: None,
            value: None,
        }
    }
}

/// Optional closing note sent when the jailed body finishes cleanly.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct DoneNote {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
}

/// Host verdict returned to the jailed body in lockstep after each proposal.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Verdict {
    pub admitted: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refusal: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_ok: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
}

impl Verdict {
    pub fn admit(tool_ok: bool, summary: Option<String>) -> Self {
        Self {
            admitted: true,
            refusal: None,
            tool_ok: Some(tool_ok),
            summary,
        }
    }

    pub fn refuse(reason: impl Into<String>) -> Self {
        Self {
            admitted: false,
            refusal: Some(reason.into()),
            tool_ok: None,
            summary: None,
        }
    }
}

/// Validated grain-host action mapped from a body [`Proposal`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfinedAction {
    Invoke {
        service: String,
    },
    Op {
        tool: String,
        args: BTreeMap<String, String>,
    },
    Spend {
        service: String,
        amount_cents: u64,
    },
    CellRead {
        path: String,
    },
    CellWrite {
        path: String,
        value: String,
    },
}

/// In-band refusal reasons for malformed proposals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MapError {
    EmptyTool,
    MissingPath(String),
    MissingValue,
    NonPositiveSpend(i64),
}

impl fmt::Display for MapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTool => write!(f, "proposal `tool` must not be empty"),
            Self::MissingPath(t) => write!(f, "proposal `{t}` needs a non-empty `path`"),
            Self::MissingValue => write!(f, "`cell-write` needs a `value`"),
            Self::NonPositiveSpend(a) => write!(f, "spend amount must be > 0, got {a}"),
        }
    }
}

impl std::error::Error for MapError {}

/// Total validation mapping from an untrusted [`Proposal`] into a [`ConfinedAction`].
pub fn map_proposal(p: &Proposal) -> Result<ConfinedAction, MapError> {
    if p.tool.trim().is_empty() {
        return Err(MapError::EmptyTool);
    }
    let service = || {
        p.tool
            .strip_prefix("invoke:")
            .or_else(|| p.tool.strip_prefix("spend:"))
            .unwrap_or(&p.tool)
            .to_string()
    };
    if let Some(args) = &p.args {
        return Ok(ConfinedAction::Op {
            tool: p.tool.clone(),
            args: args.clone(),
        });
    }
    if let Some(amount) = p.amount_cents {
        if amount <= 0 {
            return Err(MapError::NonPositiveSpend(amount));
        }
        return Ok(ConfinedAction::Spend {
            service: service(),
            amount_cents: amount as u64,
        });
    }
    match p.tool.as_str() {
        "cell-write" => {
            let path = p
                .path
                .clone()
                .filter(|s| !s.is_empty())
                .ok_or_else(|| MapError::MissingPath("cell-write".into()))?;
            let value = p.value.clone().ok_or(MapError::MissingValue)?;
            Ok(ConfinedAction::CellWrite { path, value })
        }
        "cell-read" => {
            let path = p
                .path
                .clone()
                .filter(|s| !s.is_empty())
                .ok_or_else(|| MapError::MissingPath("cell-read".into()))?;
            Ok(ConfinedAction::CellRead { path })
        }
        _ => {
            let svc = service();
            if svc.trim().is_empty() {
                return Err(MapError::EmptyTool);
            }
            Ok(ConfinedAction::Invoke { service: svc })
        }
    }
}

/// Transport contract between the grain host and a confined subprocess body.
pub trait BodyChannel {
    fn recv(&mut self) -> io::Result<Option<BodyMsg>>;
    fn send(&mut self, verdict: &Verdict) -> io::Result<()>;
}

/// Bounded-frame newline-delimited JSON channel (`1 MiB` default cap, poison-on-overflow).
pub struct LineChannel<R: BufRead, W: Write> {
    reader: R,
    writer: W,
    raw_buf: Vec<u8>,
    max_line_bytes: usize,
    poisoned: bool,
}

impl<R: BufRead, W: Write> LineChannel<R, W> {
    pub fn new(reader: R, writer: W) -> Self {
        Self {
            reader,
            writer,
            raw_buf: Vec::new(),
            max_line_bytes: DEFAULT_MAX_LINE_BYTES,
            poisoned: false,
        }
    }

    pub fn with_max_line_bytes(mut self, max: usize) -> Self {
        self.max_line_bytes = max.max(1);
        self
    }

    pub fn max_line_bytes(&self) -> usize {
        self.max_line_bytes
    }

    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    pub fn into_parts(self) -> (R, W) {
        (self.reader, self.writer)
    }
}

impl<R: BufRead, W: Write> BodyChannel for LineChannel<R, W> {
    fn recv(&mut self) -> io::Result<Option<BodyMsg>> {
        if self.poisoned {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LineChannel permanently poisoned after framing violation",
            ));
        }

        let mut empty_lines = 0usize;
        loop {
            self.raw_buf.clear();
            // Read at most `max_line_bytes + 2` so a payload of `max_line_bytes` + `\r\n` fits
            // while any payload > `max_line_bytes` (with or without `\n`) is deterministically caught!
            let take_cap = (self.max_line_bytes as u64).saturating_add(2);
            let n = (&mut self.reader)
                .take(take_cap)
                .read_until(b'\n', &mut self.raw_buf)?;
            if n == 0 {
                return Ok(None);
            }
            if !self.raw_buf.ends_with(b"\n") {
                self.poisoned = true;
                if self.raw_buf.len() > self.max_line_bytes {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "confined-body frame exceeds max_line_bytes ({} > {}) without newline",
                            self.raw_buf.len(),
                            self.max_line_bytes
                        ),
                    ));
                }
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "confined-body frame truncated without terminating newline",
                ));
            }

            // Strip trailing `\n` and optional `\r`, then enforce exact payload ceiling `<= max_line_bytes`.
            let mut end = self.raw_buf.len() - 1;
            if end > 0 && self.raw_buf[end - 1] == b'\r' {
                end -= 1;
            }
            let payload = &self.raw_buf[..end];
            if payload.len() > self.max_line_bytes {
                self.poisoned = true;
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "confined-body frame payload exceeds max_line_bytes ({} > {})",
                        payload.len(),
                        self.max_line_bytes
                    ),
                ));
            }
            if payload.contains(&0) {
                self.poisoned = true;
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "confined-body frame contains forbidden NUL byte",
                ));
            }
            if payload.iter().all(u8::is_ascii_whitespace) {
                empty_lines += 1;
                if empty_lines > MAX_CONSECUTIVE_EMPTY_LINES {
                    self.poisoned = true;
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "confined-body exceeded maximum consecutive empty keep-alive lines",
                    ));
                }
                continue;
            }
            let text = std::str::from_utf8(payload).map_err(|e| {
                self.poisoned = true;
                io::Error::new(io::ErrorKind::InvalidData, e)
            })?;
            let msg: BodyMsg = serde_json::from_str(text).map_err(|e| {
                self.poisoned = true;
                io::Error::new(io::ErrorKind::InvalidData, e)
            })?;
            return Ok(Some(msg));
        }
    }

    fn send(&mut self, verdict: &Verdict) -> io::Result<()> {
        if self.poisoned {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LineChannel permanently poisoned after framing violation",
            ));
        }
        let mut buf = serde_json::to_vec(verdict)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        if buf.len() > self.max_line_bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "outbound verdict exceeds max_line_bytes ({} > {})",
                    buf.len(),
                    self.max_line_bytes
                ),
            ));
        }
        buf.push(b'\n');
        self.writer.write_all(&buf)?;
        self.writer.flush()
    }
}

/// Host-side confined-body driver over any [`BodyChannel`].
pub struct ConfinedBrain<C: BodyChannel> {
    body: C,
    done: bool,
    unmapped_refusals: u64,
    timed_out: bool,
}

impl<C: BodyChannel> ConfinedBrain<C> {
    pub fn new(body: C) -> Self {
        Self {
            body,
            done: false,
            unmapped_refusals: 0,
            timed_out: false,
        }
    }

    pub fn unmapped_refusals(&self) -> u64 {
        self.unmapped_refusals
    }

    pub fn timed_out(&self) -> bool {
        self.timed_out
    }

    pub fn into_body(self) -> C {
        self.body
    }

    pub fn next_action(&mut self) -> Option<ConfinedAction> {
        loop {
            if self.done {
                return None;
            }
            match self.body.recv() {
                Ok(Some(BodyMsg::Propose(p))) => match map_proposal(&p) {
                    Ok(action) => return Some(action),
                    Err(reason) => {
                        self.unmapped_refusals += 1;
                        if self
                            .body
                            .send(&Verdict::refuse(reason.to_string()))
                            .is_err()
                        {
                            self.done = true;
                            return None;
                        }
                    }
                },
                Ok(Some(BodyMsg::Done(_))) | Ok(None) => {
                    self.done = true;
                    return None;
                }
                Err(e) => {
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    ) {
                        self.timed_out = true;
                    }
                    self.done = true;
                    return None;
                }
            }
        }
    }

    pub fn observe(&mut self, verdict: &Verdict) {
        if self.body.send(verdict).is_err() {
            self.done = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn oversized_frame_refused_and_channel_permanently_poisoned() {
        // Attempt 1: 512 bytes without newline + valid JSON on second half -> must fail AND stay poisoned!
        let second_half =
            serde_json::to_string(&BodyMsg::Propose(Proposal::invoke("smuggled"))).unwrap();
        let mut stream = "x".repeat(300);
        stream.push_str(&second_half);
        stream.push('\n');

        let mut ch =
            LineChannel::new(Cursor::new(stream.into_bytes()), Vec::new()).with_max_line_bytes(128);
        assert!(ch.recv().is_err(), "oversized frame must fail closed");
        assert!(ch.is_poisoned());
        assert!(
            ch.recv().is_err(),
            "subsequent recv on poisoned channel must NEVER parse smuggled tail!"
        );
    }

    #[test]
    fn oversized_newline_terminated_frame_also_refused() {
        let mut msg = serde_json::to_string(&BodyMsg::Propose(Proposal {
            tool: "cell-write".into(),
            args: None,
            amount_cents: None,
            path: Some("notes/1".into()),
            value: Some("A".repeat(400)),
        }))
        .unwrap();
        msg.push('\n');

        let mut ch =
            LineChannel::new(Cursor::new(msg.into_bytes()), Vec::new()).with_max_line_bytes(128);
        assert!(ch.recv().is_err());
        assert!(ch.is_poisoned());
    }

    #[test]
    fn empty_line_flood_bounded_without_stack_overflow() {
        let flood = "\n".repeat(10_000);
        let mut ch = LineChannel::new(Cursor::new(flood.into_bytes()), Vec::new());
        assert!(ch.recv().is_err());
        assert!(ch.is_poisoned());
    }

    #[test]
    fn valid_proposals_drive_confined_brain_lockstep() {
        let mut wire = String::new();
        for m in [
            BodyMsg::Propose(Proposal::invoke("invoke:health")),
            BodyMsg::Propose(Proposal {
                tool: "cell-write".into(),
                args: None,
                amount_cents: None,
                path: Some("k".into()),
                value: None,
            }),
            BodyMsg::Propose(Proposal {
                tool: "spend:compute".into(),
                args: None,
                amount_cents: Some(500),
                path: None,
                value: None,
            }),
            BodyMsg::Done(DoneNote {
                summary: Some("complete".into()),
            }),
        ] {
            wire.push_str(&serde_json::to_string(&m).unwrap());
            wire.push('\n');
        }

        let ch = LineChannel::new(Cursor::new(wire.into_bytes()), Vec::new());
        let mut brain = ConfinedBrain::new(ch);
        assert_eq!(
            brain.next_action(),
            Some(ConfinedAction::Invoke {
                service: "health".into()
            })
        );
        brain.observe(&Verdict::admit(true, Some("ok".into())));
        // Malformed cell-write refused in-band; next_action returns the valid spend!
        assert_eq!(
            brain.next_action(),
            Some(ConfinedAction::Spend {
                service: "compute".into(),
                amount_cents: 500
            })
        );
        assert_eq!(brain.unmapped_refusals(), 1);
        brain.observe(&Verdict::admit(true, None));
        assert_eq!(brain.next_action(), None);
    }
}
