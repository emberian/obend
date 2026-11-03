//! Live `obend-fpga-hal` Telemetry, Integrated Logic Analyzer (`ILA`), `OBCAMv1` Execution,
//! and 3-Phase Glitch-Free `ICAP` DPR Hot-Swap HTTP API (`QUALIFICATION-AND-SILICON-LEAN.md` Mandate #6 & §3.1).

use obend_fpga_hal::regs::{PackedNodeWord88, SiliconElabWireFrame, OBEND_MAGIC_F20};
use obend_fpga_hal::{FpgaHalError, IcapDprSwapReceipt, ObendFpgaHal, SiliconTelemetry};
use serde::de::{self, Deserializer, Visitor};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

/// Maximum clock cycles allowed in a single `POST /api/fpga/step` request.
pub const MAX_API_STEP_CYCLES: u32 = 100_000;

/// Number of input/output ports surfaced in the live ILA snapshot (`OBEND_IN_PORT[0..15]`, `OBEND_OUT_PORT[0..15]`).
pub const ILA_IO_PORT_COUNT: usize = 16;

/// Number of `always_ff` architectural registers surfaced in `OBEND_STATE_SNAP[0..31]`.
pub const ILA_STATE_SNAP_COUNT: usize = 32;

/// Deserialize a `u64` from either a JSON integer (`12345`) or a decimal/hex string (`"0xCAFEBABE12345678"`),
/// preserving full 64-bit precision across browser `JSON.stringify` and Rust callers.
pub fn deserialize_u64_flex<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: Deserializer<'de>,
{
    struct U64FlexVisitor;

    impl<'de> Visitor<'de> for U64FlexVisitor {
        type Value = u64;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("an unsigned 64-bit integer or hex/decimal string (e.g. \"0xCAFE...\")")
        }

        fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E> {
            Ok(v)
        }

        fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            u64::try_from(v).map_err(|_| E::custom(format!("negative u64 value: {v}")))
        }

        fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            parse_u64_str(s).map_err(E::custom)
        }

        fn visit_string<E>(self, s: String) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            self.visit_str(&s)
        }
    }

    deserializer.deserialize_any(U64FlexVisitor)
}

fn parse_u64_str(raw: &str) -> Result<u64, String> {
    let cleaned: String = raw.trim().chars().filter(|&c| c != '_').collect();
    if cleaned.is_empty() {
        return Err("empty u64 string".to_string());
    }
    if let Some(hex) = cleaned
        .strip_prefix("0x")
        .or_else(|| cleaned.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).map_err(|e| format!("invalid hex u64 `{raw}`: {e}"))
    } else {
        cleaned
            .parse::<u64>()
            .map_err(|e| format!("invalid decimal u64 `{raw}`: {e}"))
    }
}

fn deserialize_port_map_flex<'de, D>(
    deserializer: D,
) -> Result<Option<BTreeMap<usize, u64>>, D::Error>
where
    D: Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum FlexVal {
        Num(u64),
        Neg(i64),
        Str(String),
    }

    let opt: Option<BTreeMap<String, FlexVal>> = Option::deserialize(deserializer)?;
    let Some(raw_map) = opt else {
        return Ok(None);
    };
    let mut out = BTreeMap::new();
    for (k, v) in raw_map {
        let idx = k
            .trim()
            .parse::<usize>()
            .map_err(|e| de::Error::custom(format!("invalid port index `{k}`: {e}")))?;
        let word = match v {
            FlexVal::Num(n) => n,
            FlexVal::Neg(i) => u64::try_from(i)
                .map_err(|_| de::Error::custom(format!("negative port value `{i}`")))?,
            FlexVal::Str(s) => parse_u64_str(&s).map_err(de::Error::custom)?,
        };
        out.insert(idx, word);
    }
    Ok(Some(out))
}

/// JSON response for `GET /api/fpga/telemetry`.
///
/// Flattens `SiliconTelemetry` so all canonical fields (`backend`, `total_cycles`,
/// `silicon_cycles`, `cam_hits`, `cam_allocs`, `uram_bypass_hits`, `noc_flits`,
/// `discr_lut_hits`, `zone3_match_thm`, `kernel_accepted`, `dpr_isolated`,
/// `dpr_fallback_active`) appear directly at the top level alongside BAR0 magic verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FpgaTelemetryResponse {
    #[serde(flatten)]
    pub telemetry: SiliconTelemetry,
    pub bar0_magic_u64: u64,
    pub bar0_magic_hex: String,
    pub bar0_magic_ascii: String,
    pub bar0_magic_valid: bool,
}

/// Named architectural signal annotation for the live Integrated Logic Analyzer (`ILA`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IlaNamedSignal {
    pub bank: String,
    pub index: usize,
    pub label: String,
    pub value: u64,
    pub value_hex: String,
}

/// JSON response for `GET /api/fpga/ila` (`OBEND_IN_PORT[0..15]`, `OBEND_OUT_PORT[0..15]`, `OBEND_STATE_SNAP[0..31]`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FpgaIlaSnapshot {
    pub backend: String,
    pub total_cycles: u64,
    pub in_ports: Vec<u64>,
    pub out_ports: Vec<u64>,
    pub state_snap: Vec<u64>,
    pub named_signals: Vec<IlaNamedSignal>,
}

/// JSON request payload for `POST /api/fpga/step`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FpgaStepRequest {
    /// Sparse map of `(port_idx -> 64-bit value)` to write into `OBEND_IN_PORT[0..31]`.
    #[serde(default, deserialize_with = "deserialize_port_map_flex")]
    pub in_ports: Option<BTreeMap<usize, u64>>,
    /// Optional dense prefix of values to write starting at `OBEND_IN_PORT[0]`.
    #[serde(default)]
    pub in_port_values: Option<Vec<u64>>,
    /// Number of hardware clock cycles to step (`1..=100_000`; `0` writes ports without advancing clock; defaults to `1` or `4` with `obcam_frame`).
    #[serde(default)]
    pub cycles: Option<u32>,
    /// Optional 7-section `OBCAMv1` `SiliconElabWireFrame` to push over 512-bit AXI4-Stream DMA and execute across Zones 1–4.
    #[serde(default)]
    pub obcam_frame: Option<SiliconElabWireFrame>,
    /// Optional hex-encoded Lean `OBCAMv1` LEB128 wire frame (`Obend.Lower.ExprCAM.serializeSiliconWireFrame`).
    #[serde(default)]
    pub lean_wire_hex: Option<String>,
    /// Convenience toggle for browser UI: synthesize & submit a canonical 7-section `OBCAMv1` frame when `true`.
    #[serde(default)]
    pub run_demo_obcam_frame: Option<bool>,
}

/// JSON response payload for `POST /api/fpga/step`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FpgaStepResponse {
    pub cycles_executed: u32,
    pub obcam_submitted: bool,
    pub telemetry: SiliconTelemetry,
    pub ila: FpgaIlaSnapshot,
}

/// JSON request payload for `POST /api/fpga/dpr-swap`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FpgaDprSwapRequest {
    pub slot_name: String,
    #[serde(deserialize_with = "deserialize_u64_flex")]
    pub frame_word: u64,
    #[serde(deserialize_with = "deserialize_u64_flex")]
    pub expected_digest: u64,
    #[serde(deserialize_with = "deserialize_u64_flex")]
    pub computed_digest: u64,
    #[serde(default)]
    pub moved_pin_violation: bool,
}

/// JSON response payload for `POST /api/fpga/dpr-swap`.
///
/// Flattens `IcapDprSwapReceipt` (`slot_name`, `frame_word`, `expected_digest`, `computed_digest`,
/// `moved_pin_violation`, `committed`, `fallback_activated`, `held_output_port0_during_isolation`)
/// and attaches post-swap `telemetry` + `ila` state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FpgaDprSwapResponse {
    #[serde(flatten)]
    pub receipt: IcapDprSwapReceipt,
    pub frame_word_hex: String,
    pub expected_digest_hex: String,
    pub computed_digest_hex: String,
    pub telemetry: SiliconTelemetry,
    pub ila: FpgaIlaSnapshot,
}

/// Query live `SiliconTelemetry` + BAR0 `"OBENDF20"` magic verification from `ObendFpgaHal`.
pub fn query_fpga_telemetry(hal: &ObendFpgaHal) -> Result<FpgaTelemetryResponse, String> {
    let telemetry = hal.read_telemetry().map_err(|e| e.to_string())?;
    let (magic_u64, magic_valid) = match hal.verify_magic() {
        Ok(m) => (m, m == OBEND_MAGIC_F20),
        Err(FpgaHalError::InvalidMagic { found, .. }) => (found, false),
        Err(e) => return Err(e.to_string()),
    };
    let ascii_bytes = magic_u64.to_le_bytes();
    let magic_ascii: String = ascii_bytes
        .iter()
        .map(|&b| {
            if b.is_ascii_graphic() || b == b' ' {
                b as char
            } else {
                '.'
            }
        })
        .collect();

    Ok(FpgaTelemetryResponse {
        telemetry,
        bar0_magic_u64: magic_u64,
        bar0_magic_hex: format!("0x{magic_u64:016x}"),
        bar0_magic_ascii: magic_ascii,
        bar0_magic_valid: magic_valid,
    })
}

/// Read `OBEND_IN_PORT[0..15]`, `OBEND_OUT_PORT[0..15]`, and `OBEND_STATE_SNAP[0..31]` for ILA inspection.
pub fn query_fpga_ila(
    hal: &ObendFpgaHal,
    shadow_in_ports: &[u64; 32],
) -> Result<FpgaIlaSnapshot, String> {
    let telem = hal.read_telemetry().map_err(|e| e.to_string())?;
    let in_ports = shadow_in_ports[..ILA_IO_PORT_COUNT].to_vec();

    let mut out_ports = Vec::with_capacity(ILA_IO_PORT_COUNT);
    for idx in 0..ILA_IO_PORT_COUNT {
        out_ports.push(hal.read_out_port(idx).map_err(|e| e.to_string())?);
    }

    let mut state_snap = Vec::with_capacity(ILA_STATE_SNAP_COUNT);
    for idx in 0..ILA_STATE_SNAP_COUNT {
        state_snap.push(hal.read_state_snap(idx).map_err(|e| e.to_string())?);
    }

    let out_labels: [(usize, &str); 15] = [
        (0, "CleanroomTcad.oxide_nm"),
        (1, "CleanroomTcad.vth_mv"),
        (2, "CleanroomTcad.idrain_ua"),
        (3, "CleanroomTcad.gate_delay_ps"),
        (4, "CleanroomTcad.channel_delay_ps"),
        (5, "LcDrivesStator.slot_fill_pm"),
        (6, "LcDrivesStator.winding_loss_w"),
        (7, "LcDrivesStator.cooling_bar"),
        (8, "LcDrivesStator.torque_nm"),
        (9, "LcDrivesStator.peak_temp_c"),
        (10, "Cnc5AxisMill.feed_cmd"),
        (11, "Cnc5AxisMill.servo_lag_um"),
        (12, "Cnc5AxisMill.deflection_um"),
        (13, "Cnc5AxisMill.axis_pos_um"),
        (14, "Cnc5AxisMill.compensated_err_um"),
    ];

    let mut named_signals = Vec::with_capacity(20);
    for (idx, label) in [
        (0usize, "CleanroomTcad.in_drive"),
        (1usize, "LcDrivesStator.in_drive"),
        (2usize, "Cnc5AxisMill.in_drive"),
    ] {
        let v = in_ports[idx];
        named_signals.push(IlaNamedSignal {
            bank: "IN_PORT".to_string(),
            index: idx,
            label: label.to_string(),
            value: v,
            value_hex: format!("0x{v:016x}"),
        });
    }
    for (idx, label) in out_labels {
        let v = out_ports[idx];
        named_signals.push(IlaNamedSignal {
            bank: "OUT_PORT".to_string(),
            index: idx,
            label: label.to_string(),
            value: v,
            value_hex: format!("0x{v:016x}"),
        });
    }
    for (idx, label) in [
        (0usize, "always_ff.tcad_oxide_q"),
        (2usize, "always_ff.tcad_idrain_q"),
        (4usize, "always_ff.tcad_cdelay_q"),
    ] {
        let v = state_snap[idx];
        named_signals.push(IlaNamedSignal {
            bank: "STATE_SNAP".to_string(),
            index: idx,
            label: label.to_string(),
            value: v,
            value_hex: format!("0x{v:016x}"),
        });
    }

    Ok(FpgaIlaSnapshot {
        backend: telem.backend,
        total_cycles: telem.total_cycles,
        in_ports,
        out_ports,
        state_snap,
        named_signals,
    })
}

/// Construct a canonical 7-section `OBCAMv1` `SiliconElabWireFrame` exercising Zone 1 CAM allocation,
/// UltraRAM RAW collision bypass, Zone 2 NoC unification flits, Zone 3 `DiscrTree` LUT matching, and Zone 4 kernel check.
pub fn build_demo_obcam_wire_frame() -> SiliconElabWireFrame {
    let mut frame = SiliconElabWireFrame::new(0x1001, 0x1001, 0x0204, 512);
    let node = PackedNodeWord88 {
        opcode: 0x04,
        binder_depth: 2,
        child0: 0x1001,
        child1: 0x1001,
    };
    frame.cam_nodes.push(node);
    frame.cam_nodes.push(node);
    frame.env_decls.push((10, 0x1001, 0x1002));
    frame.inductive_rules.push((20, 21, 1, 0));
    frame.quot_entries.push([1, 2, 3, 4]);
    frame.discr_trie_entries.push((0x1001, 0x0204, 42));
    frame.unify_worklist.push((0x1001, 0x1001));
    frame.infer_seeds.push((0x1001, 0x1001));
    frame
}

fn decode_hex_bytes(hex_raw: &str) -> Result<Vec<u8>, String> {
    let trimmed = hex_raw.trim();
    let stripped = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
        .unwrap_or(trimmed);
    let compact: String = stripped
        .chars()
        .filter(|c| !c.is_whitespace() && *c != '_')
        .collect();
    if compact.is_empty() {
        return Err("empty lean_wire_hex payload".to_string());
    }
    if compact.len() % 2 != 0 {
        return Err(format!(
            "lean_wire_hex must have even number of hex digits, got {}",
            compact.len()
        ));
    }
    let mut out = Vec::with_capacity(compact.len() / 2);
    let bytes = compact.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let pair = std::str::from_utf8(&bytes[i..i + 2]).map_err(|e| e.to_string())?;
        let b = u8::from_str_radix(pair, 16)
            .map_err(|_| format!("invalid hex byte `{pair}` in lean_wire_hex"))?;
        out.push(b);
        i += 2;
    }
    Ok(out)
}

/// Execute `POST /api/fpga/step`: validate inputs, write `OBEND_IN_PORT`, step clock cycles or submit `OBCAMv1`,
/// and return updated `SiliconTelemetry` + `FpgaIlaSnapshot`.
pub fn execute_fpga_step(
    hal: &mut ObendFpgaHal,
    shadow_in_ports: &mut [u64; 32],
    req: FpgaStepRequest,
) -> Result<FpgaStepResponse, (u16, String)> {
    if let Some(c) = req.cycles {
        if c > MAX_API_STEP_CYCLES {
            return Err((
                400,
                format!("cycles ({c}) exceeds maximum allowed per step ({MAX_API_STEP_CYCLES})"),
            ));
        }
    }

    if let Some(ref dense) = req.in_port_values {
        if dense.len() > 32 {
            return Err((
                400,
                format!(
                    "in_port_values length ({}) exceeds 32 BAR0 input ports",
                    dense.len()
                ),
            ));
        }
        for (idx, &val) in dense.iter().enumerate() {
            hal.write_in_port(idx, val)
                .map_err(|e| (500, e.to_string()))?;
            shadow_in_ports[idx] = val;
        }
    }

    if let Some(ref sparse) = req.in_ports {
        for (&idx, &val) in sparse {
            if idx >= 32 {
                return Err((
                    400,
                    format!("OBEND_IN_PORT index {idx} out of bounds (must be in 0..32)"),
                ));
            }
        }
        for (&idx, &val) in sparse {
            hal.write_in_port(idx, val)
                .map_err(|e| (500, e.to_string()))?;
            shadow_in_ports[idx] = val;
        }
    }

    let mut obcam_submitted = false;
    let cycles_executed: u32;

    if let Some(ref wire_hex) = req.lean_wire_hex {
        let wire_bytes = decode_hex_bytes(wire_hex).map_err(|e| (400, e))?;
        let cyc = req.cycles.unwrap_or(4).max(3);
        hal.run_lean_wire_bytes(&wire_bytes, cyc)
            .map_err(|e| match e {
                FpgaHalError::WireDecode(msg) => (400, format!("OBCAMv1 wire decode error: {msg}")),
                other => (500, other.to_string()),
            })?;
        obcam_submitted = true;
        cycles_executed = cyc;
    } else if let Some(ref frame) = req.obcam_frame {
        let cyc = req.cycles.unwrap_or(4).max(3);
        hal.run_silicon_elab_frame(frame, cyc)
            .map_err(|e| (500, e.to_string()))?;
        obcam_submitted = true;
        cycles_executed = cyc;
    } else if req.run_demo_obcam_frame.unwrap_or(false) {
        let frame = build_demo_obcam_wire_frame();
        let cyc = req.cycles.unwrap_or(4).max(3);
        hal.run_silicon_elab_frame(&frame, cyc)
            .map_err(|e| (500, e.to_string()))?;
        obcam_submitted = true;
        cycles_executed = cyc;
    } else {
        match req.cycles {
            Some(0) => {
                cycles_executed = 0;
            }
            Some(n) => {
                hal.step_cycles(n).map_err(|e| (500, e.to_string()))?;
                cycles_executed = n;
            }
            None => {
                hal.step_cycles(1).map_err(|e| (500, e.to_string()))?;
                cycles_executed = 1;
            }
        }
    }

    let telemetry = hal.read_telemetry().map_err(|e| (500, e.to_string()))?;
    let ila = query_fpga_ila(hal, shadow_in_ports).map_err(|e| (500, e))?;

    Ok(FpgaStepResponse {
        cycles_executed,
        obcam_submitted,
        telemetry,
        ila,
    })
}

/// Execute `POST /api/fpga/dpr-swap`: run 3-phase glitch-free `perform_icap_dpr_hot_swap`
/// and return the `IcapDprSwapReceipt` + updated `SiliconTelemetry` + `FpgaIlaSnapshot`.
pub fn execute_fpga_dpr_swap(
    hal: &mut ObendFpgaHal,
    shadow_in_ports: &[u64; 32],
    req: FpgaDprSwapRequest,
) -> Result<FpgaDprSwapResponse, (u16, String)> {
    let slot_trimmed = req.slot_name.trim();
    if slot_trimmed.is_empty() {
        return Err((400, "slot_name must not be empty".to_string()));
    }

    let receipt = hal
        .perform_icap_dpr_hot_swap(
            slot_trimmed.to_string(),
            req.frame_word,
            req.expected_digest,
            req.computed_digest,
            req.moved_pin_violation,
        )
        .map_err(|e| (500, e.to_string()))?;

    let telemetry = hal.read_telemetry().map_err(|e| (500, e.to_string()))?;
    let ila = query_fpga_ila(hal, shadow_in_ports).map_err(|e| (500, e))?;

    Ok(FpgaDprSwapResponse {
        frame_word_hex: format!("0x{:016x}", receipt.frame_word),
        expected_digest_hex: format!("0x{:016x}", receipt.expected_digest),
        computed_digest_hex: format!("0x{:016x}", receipt.computed_digest),
        receipt,
        telemetry,
        ila,
    })
}
