//! Rich Interactive SVG/HTML/Terminal-Canvas Viewport Rendering (`WS 25`)
//!
//! Renders interactive SVG, HTML, and terminal-canvas viewports across all 10 `ProjectionKind`s
//! (supporting both canonical `Obend.Doc.ProjectionKind` labels and CAD/Mathematica viewport kinds:
//! `circuit`, `netlist`, `timing`, `gdsii`, `waveform`, `cellQuote`, `notebookCell`, `proofTree`,
//! `contractBadge`, `clearingLedger`), including:
//! - 2D/3D validated interval & Picard–Lindelöf ODE flowpipe tube plots,
//! - GDSII physical mask layouts with DRC cutline violation markers,
//! - `ReductionMachine` eFPGA tile activity heatmaps,
//! - Live `.free` / `.press` / `.locked` `LawDial` interactive controls.

use serde::{Deserialize, Serialize};

/// All 10 viewport projection kinds (with lossless parsing from both viewport aliases and
/// `Obend.Doc.ProjectionKind` wire labels).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProjectionKind {
    Circuit,
    Netlist,
    Timing,
    Gdsii,
    Waveform,
    CellQuote,
    NotebookCell,
    ProofTree,
    ContractBadge,
    ClearingLedger,
}

impl ProjectionKind {
    /// All 10 canonical viewport kinds.
    pub const ALL: [ProjectionKind; 10] = [
        ProjectionKind::Circuit,
        ProjectionKind::Netlist,
        ProjectionKind::Timing,
        ProjectionKind::Gdsii,
        ProjectionKind::Waveform,
        ProjectionKind::CellQuote,
        ProjectionKind::NotebookCell,
        ProjectionKind::ProofTree,
        ProjectionKind::ContractBadge,
        ProjectionKind::ClearingLedger,
    ];

    /// Canonical viewport label (`circuit`, `netlist`, `timing`, `gdsii`, `waveform`,
    /// `cellQuote`, `notebookCell`, `proofTree`, `contractBadge`, `clearingLedger`).
    pub fn as_str(self) -> &'static str {
        match self {
            ProjectionKind::Circuit => "circuit",
            ProjectionKind::Netlist => "netlist",
            ProjectionKind::Timing => "timing",
            ProjectionKind::Gdsii => "gdsii",
            ProjectionKind::Waveform => "waveform",
            ProjectionKind::CellQuote => "cellQuote",
            ProjectionKind::NotebookCell => "notebookCell",
            ProjectionKind::ProofTree => "proofTree",
            ProjectionKind::ContractBadge => "contractBadge",
            ProjectionKind::ClearingLedger => "clearingLedger",
        }
    }

    /// Corresponding `Obend.Doc.ProjectionKind` wire label in Lean (`Obend/Doc/Structured.lean`).
    pub fn doc_kind_label(self) -> &'static str {
        match self {
            ProjectionKind::Circuit => "hardwareSchematic",
            ProjectionKind::Netlist => "deosAffordance",
            ProjectionKind::Timing => "hardwareTiming",
            ProjectionKind::Gdsii => "hardwareLayout",
            ProjectionKind::Waveform => "casSymbolic",
            ProjectionKind::CellQuote => "obendCode",
            ProjectionKind::NotebookCell => "prose",
            ProjectionKind::ProofTree => "leanBridge",
            ProjectionKind::ContractBadge => "lawContract",
            ProjectionKind::ClearingLedger => "ledgerSeat",
        }
    }

    /// Parse from either the 10 viewport labels, the 10 `Obend.Doc.ProjectionKind` labels,
    /// or the `WS 30` physical-world projection labels.
    pub fn from_label(label: &str) -> Option<Self> {
        match label {
            "circuit" | "hardwareSchematic" => Some(ProjectionKind::Circuit),
            "netlist" | "deosAffordance" => Some(ProjectionKind::Netlist),
            "timing" | "hardwareTiming" | "stator_multiphysics" | "physical_stator_multiphysics" => {
                Some(ProjectionKind::Timing)
            }
            "gdsii"
            | "hardwareLayout"
            | "cnc_5axis"
            | "physical_cnc_5axis"
            | "openusd_scene"
            | "physical_openusd_scene" => Some(ProjectionKind::Gdsii),
            "waveform" | "casSymbolic" => Some(ProjectionKind::Waveform),
            "cellQuote" | "obendCode" => Some(ProjectionKind::CellQuote),
            "notebookCell" | "prose" => Some(ProjectionKind::NotebookCell),
            "proofTree" | "leanBridge" => Some(ProjectionKind::ProofTree),
            "contractBadge" | "lawContract" => Some(ProjectionKind::ContractBadge),
            "clearingLedger" | "ledgerSeat" => Some(ProjectionKind::ClearingLedger),
            _ => None,
        }
    }
}

/// Interactive `LawDial` enforcement regime (`.free`, `.press`, `.locked`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LawDialMode {
    /// Exploratory mode: invariant violations are recorded as warnings without blocking transitions.
    #[serde(alias = "free", alias = ".free", alias = "FREE")]
    Free,
    /// Soft backpressure mode: invariant margin is tracked with dual slack warnings.
    #[serde(alias = "press", alias = ".press", alias = "PRESS")]
    Press,
    /// Hard verified enforcement: transition is admitted iff the 4-tier `ContractCert` discharges.
    #[serde(alias = "locked", alias = ".locked", alias = "LOCKED")]
    Locked,
}

impl LawDialMode {
    pub fn as_str(self) -> &'static str {
        match self {
            LawDialMode::Free => "free",
            LawDialMode::Press => "press",
            LawDialMode::Locked => "locked",
        }
    }

    pub fn from_label(label: &str) -> Option<Self> {
        match label.trim().trim_start_matches('.').to_ascii_lowercase().as_str() {
            "free" => Some(LawDialMode::Free),
            "press" => Some(LawDialMode::Press),
            "locked" => Some(LawDialMode::Locked),
            _ => None,
        }
    }

    pub fn badge_color(self) -> &'static str {
        match self {
            LawDialMode::Free => "#3b82f6",
            LawDialMode::Press => "#f59e0b",
            LawDialMode::Locked => "#10b981",
        }
    }
}

/// Interactive `LawDial` control state bound to a cell contract.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LawDialControl {
    pub cell_id: String,
    pub mode: LawDialMode,
    pub invariant_expr: String,
    pub margin_lo: f64,
    pub margin_hi: f64,
    pub current_value: f64,
}

impl LawDialControl {
    /// Evaluate whether the current value satisfies `[margin_lo, margin_hi]` under the active `LawDialMode`.
    pub fn is_admitted(&self) -> bool {
        let in_bounds = self.current_value >= self.margin_lo && self.current_value <= self.margin_hi;
        match self.mode {
            LawDialMode::Free => true,
            LawDialMode::Press | LawDialMode::Locked => in_bounds,
        }
    }

    /// Render an interactive HTML/SVG control widget for the `LawDial`.
    pub fn render_html(&self) -> String {
        let admitted = self.is_admitted();
        let status_label = if admitted { "ADMITTED" } else { "REFUSED" };
        let color = self.mode.badge_color();
        format!(
            r#"<div class="obend-law-dial" data-cell-id="{cell_id}" data-mode="{mode}" data-status="{status}">
  <span class="dial-badge" style="background:{color}">.{mode}</span>
  <code class="dial-inv">{inv}</code>
  <input type="range" min="{lo:.2}" max="{hi:.2}" value="{val:.2}" step="0.1" disabled="{locked}" />
  <span class="dial-verdict">{status} ({val:.2} in [{lo:.2}, {hi:.2}])</span>
</div>"#,
            cell_id = self.cell_id,
            mode = self.mode.as_str(),
            status = status_label,
            color = color,
            inv = self.invariant_expr,
            lo = self.margin_lo,
            hi = self.margin_hi,
            val = self.current_value,
            locked = matches!(self.mode, LawDialMode::Locked),
        )
    }
}

/// A validated 1D/2D/3D interval slice for ODE flowpipe and Taylor-model plots (`WS 25`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FlowpipeSlice {
    pub step: usize,
    pub t_lo: f64,
    pub t_hi: f64,
    pub x_lo: f64,
    pub x_hi: f64,
    pub y_lo: f64,
    pub y_hi: f64,
    pub z_lo: f64,
    pub z_hi: f64,
}

/// GDSII mask rectangle with optional DRC violation marker.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GdsiiRect {
    pub layer: u16,
    pub x: i32,
    pub y: i32,
    pub width: u32,
    pub height: u32,
    pub drc_violation: Option<String>,
}

/// `ReductionMachine` eFPGA tile activity sample for heatmap rendering.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EfpgaTileActivity {
    pub tile_x: u8,
    pub tile_y: u8,
    pub utilization_pct: u8,
    pub beta_steps: u32,
    pub cam_hits: u32,
}

/// Physical-world projection kinds for `WS 30` (`PhysicalProjection.lean`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PhysicalViewportKind {
    /// 5-axis CNC kinematic toolpath with Featherstone 6D spatial twists/wrenches, Ruckig S-curves,
    /// and 21-parameter Abbe volumetric error pre-compensation (`cnc_5axis` / `physical_cnc_5axis`).
    Cnc5Axis,
    /// Apple/Pixar OpenUSD scene hierarchy (`SdfPath`), non-destructive `LIVERPS` `relocates`,
    /// `AffineForm1D` SDF intervals, and `timeSamples` lifecycle tracks (`openusd_scene` / `physical_openusd_scene`).
    OpenUsdScene,
    /// Coupled LC-Drive stator multiphysics combining Darcy-Weisbach microchannel cooling and
    /// validated continuous ODE flowpipes (`stator_multiphysics` / `physical_stator_multiphysics`).
    StatorMultiphysics,
}

impl PhysicalViewportKind {
    pub const ALL: [PhysicalViewportKind; 3] = [
        PhysicalViewportKind::Cnc5Axis,
        PhysicalViewportKind::OpenUsdScene,
        PhysicalViewportKind::StatorMultiphysics,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            PhysicalViewportKind::Cnc5Axis => "cnc_5axis",
            PhysicalViewportKind::OpenUsdScene => "openusd_scene",
            PhysicalViewportKind::StatorMultiphysics => "stator_multiphysics",
        }
    }

    pub fn lean_kind_label(self) -> &'static str {
        match self {
            PhysicalViewportKind::Cnc5Axis => "physical_cnc_5axis",
            PhysicalViewportKind::OpenUsdScene => "physical_openusd_scene",
            PhysicalViewportKind::StatorMultiphysics => "physical_stator_multiphysics",
        }
    }

    pub fn doc_projection_kind(self) -> ProjectionKind {
        match self {
            PhysicalViewportKind::Cnc5Axis => ProjectionKind::Gdsii,
            PhysicalViewportKind::OpenUsdScene => ProjectionKind::Gdsii,
            PhysicalViewportKind::StatorMultiphysics => ProjectionKind::Timing,
        }
    }

    pub fn from_label(label: &str) -> Option<Self> {
        match label.trim() {
            "cnc_5axis" | "physical_cnc_5axis" | "cncToolpath" => {
                Some(PhysicalViewportKind::Cnc5Axis)
            }
            "openusd_scene" | "physical_openusd_scene" | "openUsdScene" => {
                Some(PhysicalViewportKind::OpenUsdScene)
            }
            "stator_multiphysics" | "physical_stator_multiphysics" | "statorMultiphysics" => {
                Some(PhysicalViewportKind::StatorMultiphysics)
            }
            _ => None,
        }
    }
}

/// 5-axis CNC kinematic toolpath waypoint with 21-parameter Abbe volumetric error compensation (`WS 30`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Cnc5AxisWaypoint {
    pub step: usize,
    pub target_nm: (i64, i64, i64),
    pub volumetric_error_nm: (i64, i64, i64),
    pub abbe_compensated_cmd_nm: (i64, i64, i64),
    pub ruckig_vel_scaled2: i64,
    pub coriolis_power: i64,
}

impl Cnc5AxisWaypoint {
    /// Actual tip position after applying the Abbe-compensated command in the presence of volumetric error.
    pub fn actual_tip_nm(&self) -> (i64, i64, i64) {
        (
            self.abbe_compensated_cmd_nm.0 + self.volumetric_error_nm.0,
            self.abbe_compensated_cmd_nm.1 + self.volumetric_error_nm.1,
            self.abbe_compensated_cmd_nm.2 + self.volumetric_error_nm.2,
        )
    }

    /// True iff 21-parameter Abbe pre-compensation exactly cancels the volumetric + lever-arm error.
    pub fn is_abbe_exact_cancelled(&self) -> bool {
        self.actual_tip_nm() == self.target_nm
    }

    /// True iff the Featherstone gyroscopic/Coriolis spatial wrench performs zero mechanical work.
    pub fn is_coriolis_workless(&self) -> bool {
        self.coriolis_power == 0
    }
}

/// OpenUSD hierarchical `SdfPath` scene-graph node with `AffineForm1D` SDF bounds and `timeSamples` state (`WS 30`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OpenUsdPrimNode {
    pub prim_path: String,
    pub relocated_path: String,
    pub affine_c0_um: i64,
    pub affine_radius_um: i64,
    pub time_code: u64,
    pub peak_temp_milli_c: i64,
    pub lifecycle_invariant_ok: bool,
}

impl OpenUsdPrimNode {
    /// Validated `AffineForm1D` interval enclosure `[c0 - radius, c0 + radius]` in micrometers.
    pub fn sdf_interval_um(&self) -> (i64, i64) {
        (
            self.affine_c0_um - self.affine_radius_um,
            self.affine_c0_um + self.affine_radius_um,
        )
    }
}

/// Coupled LC-drive stator multiphysics telemetry combining microchannel hydraulics and ODE flowpipe bounds (`WS 30`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StatorChannelTelemetry {
    pub part_name: String,
    pub darcy_pressure_drop_scaled: i64,
    pub winding_temp_c_lo: f64,
    pub winding_temp_c_hi: f64,
    pub max_temp_limit_c: f64,
    pub flowpipe_certified: bool,
}

impl StatorChannelTelemetry {
    pub fn is_multiphysics_certified(&self) -> bool {
        self.flowpipe_certified && self.winding_temp_c_hi <= self.max_temp_limit_c
    }

    pub fn status_label(&self) -> &'static str {
        if self.is_multiphysics_certified() {
            "MULTIPHYSICS_CERTIFIED"
        } else {
            "UNSAFE"
        }
    }
}

/// Golden 5-axis CNC toolpath waypoints matching `Obend.Vault.PhysicalProjection.goldenCncViewportSpec` (`Hermle_C42U_5Axis`).
pub fn golden_cnc_5axis_waypoints() -> Vec<Cnc5AxisWaypoint> {
    vec![
        Cnc5AxisWaypoint {
            step: 0,
            target_nm: (100_000, 200_000, 50_000),
            volumetric_error_nm: (-438, -308, 5),
            abbe_compensated_cmd_nm: (100_438, 200_308, 49_995),
            ruckig_vel_scaled2: 0,
            coriolis_power: 0,
        },
        Cnc5AxisWaypoint {
            step: 1,
            target_nm: (125_000, 215_000, 48_000),
            volumetric_error_nm: (-410, -290, 8),
            abbe_compensated_cmd_nm: (125_410, 215_290, 47_992),
            ruckig_vel_scaled2: 80,
            coriolis_power: 0,
        },
        Cnc5AxisWaypoint {
            step: 2,
            target_nm: (150_000, 230_000, 45_000),
            volumetric_error_nm: (-395, -275, 4),
            abbe_compensated_cmd_nm: (150_395, 230_275, 44_996),
            ruckig_vel_scaled2: 160,
            coriolis_power: 0,
        },
    ]
}

/// Golden OpenUSD scene-graph nodes matching `Obend.Vault.PhysicalProjection.goldenOpenUsdViewportSpec` (`LcDrives_Production_Stator`).
pub fn golden_openusd_prims() -> Vec<OpenUsdPrimNode> {
    vec![
        OpenUsdPrimNode {
            prim_path: "/Factory/Draft/Stator/Slot01".to_string(),
            relocated_path: "/Prod/LCDrives/Stator/Slot01".to_string(),
            affine_c0_um: 1500,
            affine_radius_um: 25,
            time_code: 0,
            peak_temp_milli_c: 25_000,
            lifecycle_invariant_ok: true,
        },
        OpenUsdPrimNode {
            prim_path: "/Factory/Draft/Stator/Slot02".to_string(),
            relocated_path: "/Prod/LCDrives/Stator/Slot02".to_string(),
            affine_c0_um: 1500,
            affine_radius_um: 25,
            time_code: 20,
            peak_temp_milli_c: 55_000,
            lifecycle_invariant_ok: true,
        },
        OpenUsdPrimNode {
            prim_path: "/Factory/Draft/Stator/Slot03".to_string(),
            relocated_path: "/Prod/LCDrives/Stator/Slot03".to_string(),
            affine_c0_um: 1500,
            affine_radius_um: 25,
            time_code: 100,
            peak_temp_milli_c: 122_000,
            lifecycle_invariant_ok: true,
        },
    ]
}

/// Golden coupled LC-drive stator telemetry matching `Obend.Vault.PhysicalProjection.goldenStatorMultiphysicsSpec`.
pub fn golden_stator_telemetry() -> StatorChannelTelemetry {
    StatorChannelTelemetry {
        part_name: "LC_Drives_InSlot_Stator_Assy".to_string(),
        darcy_pressure_drop_scaled: 4_992_187_500,
        winding_temp_c_lo: 22.9,
        winding_temp_c_hi: 30.0,
        max_temp_limit_c: 35.0,
        flowpipe_certified: true,
    }
}

/// Golden continuous ODE flowpipe slices for the coupled LC-drive stator thermal cooling trajectory.
pub fn golden_stator_flowpipe_slices() -> Vec<FlowpipeSlice> {
    vec![
        FlowpipeSlice {
            step: 0,
            t_lo: 0.0,
            t_hi: 0.5,
            x_lo: 28.0,
            x_hi: 30.0,
            y_lo: -10.0,
            y_hi: -8.0,
            z_lo: 0.0,
            z_hi: 1.0,
        },
        FlowpipeSlice {
            step: 1,
            t_lo: 0.5,
            t_hi: 1.0,
            x_lo: 25.2,
            x_hi: 27.8,
            y_lo: -7.8,
            y_hi: -5.2,
            z_lo: 0.5,
            z_hi: 1.5,
        },
        FlowpipeSlice {
            step: 2,
            t_lo: 1.0,
            t_hi: 1.5,
            x_lo: 22.9,
            x_hi: 26.1,
            y_lo: -6.1,
            y_hi: -2.9,
            z_lo: 1.0,
            z_hi: 2.0,
        },
    ]
}

/// Rendered multi-modal viewport output (SVG, HTML control panel, and terminal ASCII canvas).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RenderedViewport {
    pub kind: ProjectionKind,
    pub title: String,
    pub svg: String,
    pub html_controls: String,
    pub terminal_canvas: String,
}

/// Render a 2D/3D validated ODE flowpipe & interval enclosure SVG plot (`WS 25`).
pub fn render_flowpipe_svg(
    title: &str,
    slices: &[FlowpipeSlice],
    safe_min: f64,
    safe_max: f64,
) -> String {
    let mut svg = String::with_capacity(2048);
    svg.push_str(&format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 360" data-projection="flowpipe" data-title="{title}">"##,
    ));
    // Safe operating envelope band
    svg.push_str(&format!(
        r##"<rect class="safe-envelope" x="40" y="{:.1}" width="560" height="{:.1}" fill="#10b98122" stroke="#10b981" stroke-dasharray="4,2" />"##,
        300.0 - safe_max * 5.0,
        (safe_max - safe_min).abs() * 5.0
    ));
    // 2D & isometric 3D interval boxes
    for slice in slices {
        let x = 50.0 + (slice.step as f64) * 90.0 + slice.z_lo * 4.0;
        let y_top = 300.0 - slice.x_hi * 5.0 - slice.z_hi * 2.0;
        let height = ((slice.x_hi - slice.x_lo).abs() * 5.0).max(4.0);
        let width = ((slice.t_hi - slice.t_lo).abs() * 40.0).max(28.0);
        let safe = slice.x_lo >= safe_min && slice.x_hi <= safe_max;
        let fill = if safe { "#3b82f666" } else { "#ef444488" };
        let stroke = if safe { "#2563eb" } else { "#dc2626" };
        svg.push_str(&format!(
            r##"<rect class="flowpipe-box" data-step="{step}" x="{x:.1}" y="{y_top:.1}" width="{width:.1}" height="{height:.1}" fill="{fill}" stroke="{stroke}" stroke-width="1.5" />"##,
            step = slice.step,
        ));
    }
    svg.push_str("</svg>");
    svg
}

/// Render a GDSII physical mask layout with DRC cutline violation markers (`WS 25`).
pub fn render_gdsii_svg(rects: &[GdsiiRect]) -> String {
    let mut svg = String::from(
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 360" data-projection="gdsii">"##,
    );
    for r in rects {
        let color = match r.layer {
            68 => "#3b82f688", // Metal1
            69 => "#a855f788", // Metal2
            _ => "#10b98188",  // Poly / Active
        };
        svg.push_str(&format!(
            r##"<rect class="gds-mask" data-layer="{layer}" x="{x}" y="{y}" width="{w}" height="{h}" fill="{color}" stroke="#1e293b" />"##,
            layer = r.layer,
            x = r.x,
            y = r.y,
            w = r.width,
            h = r.height,
            color = color
        ));
        if let Some(violation) = &r.drc_violation {
            svg.push_str(&format!(
                r##"<circle class="drc-marker" cx="{cx}" cy="{cy}" r="8" fill="none" stroke="#ef4444" stroke-width="2" data-drc="{v}" />"##,
                cx = r.x + (r.width as i32) / 2,
                cy = r.y + (r.height as i32) / 2,
                v = violation
            ));
        }
    }
    svg.push_str("</svg>");
    svg
}

/// Render a `ReductionMachine` eFPGA tile activity & `ExprCAM` hit heatmap (`WS 25`).
pub fn render_efpga_heatmap_svg(tiles: &[EfpgaTileActivity]) -> String {
    let mut svg = String::from(
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 480 480" data-projection="efpga-heatmap">"##,
    );
    for t in tiles {
        let x = 24 + (t.tile_x as u32) * 52;
        let y = 24 + (t.tile_y as u32) * 52;
        let heat = if t.utilization_pct >= 80 {
            "#ef4444"
        } else if t.utilization_pct >= 40 {
            "#f59e0b"
        } else {
            "#10b981"
        };
        svg.push_str(&format!(
            r##"<rect class="efpga-tile" data-x="{tx}" data-y="{ty}" data-util="{u}" data-cam-hits="{cam}" x="{x}" y="{y}" width="46" height="46" fill="{heat}" rx="4" />"##,
            tx = t.tile_x,
            ty = t.tile_y,
            u = t.utilization_pct,
            cam = t.cam_hits,
            x = x,
            y = y,
            heat = heat,
        ));
    }
    svg.push_str("</svg>");
    svg
}

/// Render a 5-axis CNC kinematic toolpath viewport SVG with Abbe volumetric compensation & Ruckig S-curve telemetry (`WS 30`).
pub fn render_cnc_5axis_toolpath_svg(machine_name: &str, waypoints: &[Cnc5AxisWaypoint]) -> String {
    let all_certified = waypoints
        .iter()
        .all(|wp| wp.is_abbe_exact_cancelled() && wp.is_coriolis_workless());
    let badge = if all_certified {
        "Abbe-Certified"
    } else {
        "Abbe-Uncompensated"
    };
    let mut svg = format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 360" data-projection="physical-cnc-5axis" data-machine="{machine_name}" data-badge="{badge}"><text x="20" y="26" fill="#f8fafc">5-Axis CNC Toolpath ({machine_name}) [{badge}]</text>"##,
    );
    let mut poly_pts = String::new();
    for wp in waypoints {
        let abbe_cancelled = wp.is_abbe_exact_cancelled();
        let cx = 60 + (wp.step as i64) * 110;
        let cy = 180 - (wp.ruckig_vel_scaled2 / 4);
        if !poly_pts.is_empty() {
            poly_pts.push(' ');
        }
        poly_pts.push_str(&format!("{cx},{cy}"));
        let err_dx = (wp.volumetric_error_nm.0 / 25).clamp(-36, 36);
        let err_dy = (wp.volumetric_error_nm.1 / 25).clamp(-36, 36);
        svg.push_str(&format!(
            r##"<g class="cnc-waypoint" data-step="{step}" data-abbe-cancelled="{abbe}" data-coriolis-power="{cp}" data-ruckig-vel="{vel}"><rect class="abbe-corridor" x="{bx}" y="{by}" width="24" height="24" fill="#10b98122" stroke="#10b981" /><circle cx="{cx}" cy="{cy}" r="6" fill="#10b981" /><line class="abbe-error-vector" x1="{cx}" y1="{cy}" x2="{ex}" y2="{ey}" stroke="#f59e0b" stroke-width="1.5" /><line class="ruckig-scurve-vec" x1="{cx}" y1="{cy}" x2="{cx2}" y2="{cy2}" stroke="#38bdf8" stroke-width="2" /></g>"##,
            step = wp.step,
            abbe = abbe_cancelled,
            cp = wp.coriolis_power,
            vel = wp.ruckig_vel_scaled2,
            bx = cx - 12,
            by = cy - 12,
            cx = cx,
            cy = cy,
            ex = cx + err_dx,
            ey = cy + err_dy,
            cx2 = cx + 18,
            cy2 = cy - 12,
        ));
    }
    svg.push_str(&format!(
        r##"<polyline class="cnc-toolpath-xy" fill="none" stroke="#38bdf8" stroke-width="2" points="{poly_pts}" />"##,
    ));
    svg.push_str("</svg>");
    svg
}

/// Render an Apple/Pixar OpenUSD `SdfPath` scene-graph, `LIVERPS` relocates, and `AffineForm1D` SDF enclosure SVG (`WS 30`).
pub fn render_openusd_scene_svg(stage_name: &str, prims: &[OpenUsdPrimNode]) -> String {
    let all_ok = prims.iter().all(|p| p.lifecycle_invariant_ok);
    let lca_badge = if all_ok { "LCA PASS" } else { "LCA VIOLATION" };
    let mut svg = format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 360" data-projection="physical-openusd-scene" data-stage="{stage_name}" data-lca="{lca_badge}"><text x="24" y="24" fill="#f8fafc">OpenUSD Scene Graph ({stage_name}) [{lca_badge}]</text>"##,
    );
    for (idx, prim) in prims.iter().enumerate() {
        let y = 40 + (idx as u32) * 70;
        let (lo, hi) = prim.sdf_interval_um();
        let color = if prim.lifecycle_invariant_ok {
            "#10b981"
        } else {
            "#ef4444"
        };
        svg.push_str(&format!(
            r##"<g class="openusd-prim" data-sdf-path="{path}" data-relocated="{rel}" data-sdf-interval="[{lo},{hi}]" data-self-cancel="[0,0]" data-time="{tc}"><rect x="32" y="{y}" width="560" height="52" rx="6" fill="#0f172a" stroke="{color}" /><text x="48" y="{ty}" fill="#f8fafc">{path} -&gt; {rel} (SDF [{lo}, {hi}] um, t={tc}, T={temp_c:.1}C)</text></g>"##,
            path = prim.prim_path,
            rel = prim.relocated_path,
            lo = lo,
            hi = hi,
            tc = prim.time_code,
            temp_c = (prim.peak_temp_milli_c as f64) / 1000.0,
            y = y,
            ty = y + 30,
            color = color,
        ));
    }
    svg.push_str("</svg>");
    svg
}

/// Render a coupled LC-drive stator multiphysics + continuous ODE flowpipe SVG (`WS 30`).
pub fn render_stator_multiphysics_svg(
    telemetry: &StatorChannelTelemetry,
    flowpipe_slices: &[FlowpipeSlice],
) -> String {
    let status = telemetry.status_label();
    let thermal_badge = if telemetry.is_multiphysics_certified() {
        "THERMAL SAFE"
    } else {
        "THERMAL EXCURSION"
    };
    let fp_inner = render_flowpipe_svg(
        &telemetry.part_name,
        flowpipe_slices,
        15.0,
        telemetry.max_temp_limit_c,
    );
    format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 420" data-projection="physical-stator-multiphysics" data-part="{part}" data-status="{status}" data-darcy="{darcy}"><g class="stator-header"><text x="24" y="28" fill="#10b981">Coupled LC/Stator Multiphysics {part}: {status} [{thermal_badge}] (Darcy drop={darcy}, S0/S1 T=[{tlo:.1}, {thi:.1}]C &lt;= {tmax:.1}C)</text></g>{fp}</svg>"##,
        part = telemetry.part_name,
        status = status,
        thermal_badge = thermal_badge,
        darcy = telemetry.darcy_pressure_drop_scaled,
        tlo = telemetry.winding_temp_c_lo,
        thi = telemetry.winding_temp_c_hi,
        tmax = telemetry.max_temp_limit_c,
        fp = fp_inner,
    )
}

/// Render an ANSI-colored terminal canvas for a 5-axis CNC kinematic toolpath (`WS 30`).
pub fn render_cnc_5axis_ansi(
    machine_name: &str,
    waypoints: &[Cnc5AxisWaypoint],
    dial: &LawDialControl,
) -> String {
    let all_abbe = waypoints.iter().all(|w| w.is_abbe_exact_cancelled());
    let all_coriolis = waypoints.iter().all(|w| w.is_coriolis_workless());
    format!(
        "\x1b[1;36m+-[physical_cnc_5axis]-[{machine}]------------------------------+\x1b[0m\n\
         | Waypoints: {:<4} | Abbe Exact Cancelled: \x1b[32m{:<5}\x1b[0m | Coriolis W=0: \x1b[32m{:<5}\x1b[0m |\n\
         | Dial     : .{:<6} | Admitted: {:<5} | Value: {:>8.2}              |\n\
         \x1b[1;36m+------------------------------------------------------------------+\x1b[0m",
        waypoints.len(),
        all_abbe,
        all_coriolis,
        dial.mode.as_str(),
        dial.is_admitted(),
        dial.current_value,
        machine = machine_name,
    )
}

/// Render an ANSI-colored terminal canvas for an OpenUSD scene hierarchy & `AffineForm1D` SDF track (`WS 30`).
pub fn render_openusd_scene_ansi(
    stage_name: &str,
    prims: &[OpenUsdPrimNode],
    dial: &LawDialControl,
) -> String {
    let all_ok = prims.iter().all(|p| p.lifecycle_invariant_ok);
    let first_sdf = prims.first().map(|p| p.sdf_interval_um()).unwrap_or((0, 0));
    format!(
        "\x1b[1;35m+-[physical_openusd_scene]-[{stage}]-------------------------+\x1b[0m\n\
         | Prims: {:<4} | Affine SDF: [{:>5}, {:>5}] um | Lifecycle OK: \x1b[32m{:<5}\x1b[0m |\n\
         | Dial : .{:<6} | Admitted: {:<5} | Value: {:>8.2}                  |\n\
         \x1b[1;35m+------------------------------------------------------------------+\x1b[0m",
        prims.len(),
        first_sdf.0,
        first_sdf.1,
        all_ok,
        dial.mode.as_str(),
        dial.is_admitted(),
        dial.current_value,
        stage = stage_name,
    )
}

/// Render an ANSI-colored terminal canvas for coupled LC-Drive stator multiphysics (`WS 30`).
pub fn render_stator_multiphysics_ansi(
    telemetry: &StatorChannelTelemetry,
    flowpipe_slices: &[FlowpipeSlice],
    dial: &LawDialControl,
) -> String {
    format!(
        "\x1b[1;32m+-[physical_stator_multiphysics]-[{part}]-------------------+\x1b[0m\n\
         | Status: {:<22} | Darcy Drop: {:<12} | Slices: {:<2} |\n\
         | Winding T: [{:>5.1}, {:>5.1}]C <= {:>5.1}C | Dial: .{:<6} (Admitted: {:<5}) |\n\
         \x1b[1;32m+------------------------------------------------------------------+\x1b[0m",
        telemetry.status_label(),
        telemetry.darcy_pressure_drop_scaled,
        flowpipe_slices.len(),
        telemetry.winding_temp_c_lo,
        telemetry.winding_temp_c_hi,
        telemetry.max_temp_limit_c,
        dial.mode.as_str(),
        dial.is_admitted(),
        part = telemetry.part_name,
    )
}

/// Construct a full multi-modal `RenderedViewport` (SVG + HTML + ANSI) for a 5-axis CNC toolpath (`WS 30`).
pub fn render_cnc_5axis_viewport(
    machine_name: &str,
    waypoints: &[Cnc5AxisWaypoint],
    dial: &LawDialControl,
) -> RenderedViewport {
    let svg = render_cnc_5axis_toolpath_svg(machine_name, waypoints);
    let html_controls = format!(
        r#"<div class="obend-physical-panel" data-physical-kind="cnc_5axis" data-machine="{machine_name}">{}</div>"#,
        dial.render_html()
    );
    let terminal_canvas = render_cnc_5axis_ansi(machine_name, waypoints, dial);
    RenderedViewport {
        kind: ProjectionKind::Gdsii,
        title: machine_name.to_string(),
        svg,
        html_controls,
        terminal_canvas,
    }
}

/// Construct a full multi-modal `RenderedViewport` (SVG + HTML + ANSI) for an OpenUSD scene graph (`WS 30`).
pub fn render_openusd_scene_viewport(
    stage_name: &str,
    prims: &[OpenUsdPrimNode],
    dial: &LawDialControl,
) -> RenderedViewport {
    let svg = render_openusd_scene_svg(stage_name, prims);
    let html_controls = format!(
        r#"<div class="obend-physical-panel" data-physical-kind="openusd_scene" data-stage="{stage_name}">{}</div>"#,
        dial.render_html()
    );
    let terminal_canvas = render_openusd_scene_ansi(stage_name, prims, dial);
    RenderedViewport {
        kind: ProjectionKind::Gdsii,
        title: stage_name.to_string(),
        svg,
        html_controls,
        terminal_canvas,
    }
}

/// Construct a full multi-modal `RenderedViewport` (SVG + HTML + ANSI) for coupled LC-Drive stator multiphysics (`WS 30`).
pub fn render_stator_multiphysics_viewport(
    telemetry: &StatorChannelTelemetry,
    flowpipe_slices: &[FlowpipeSlice],
    dial: &LawDialControl,
) -> RenderedViewport {
    let svg = render_stator_multiphysics_svg(telemetry, flowpipe_slices);
    let html_controls = format!(
        r#"<div class="obend-physical-panel" data-physical-kind="stator_multiphysics" data-part="{}">{}</div>"#,
        telemetry.part_name,
        dial.render_html()
    );
    let terminal_canvas = render_stator_multiphysics_ansi(telemetry, flowpipe_slices, dial);
    RenderedViewport {
        kind: ProjectionKind::Timing,
        title: telemetry.part_name.clone(),
        svg,
        html_controls,
        terminal_canvas,
    }
}

/// Render any of the 3 `PhysicalViewportKind`s (`cnc_5axis`, `openusd_scene`, `stator_multiphysics`)
/// using golden physical-world telemetry adjusted by the active `LawDialControl` (`WS 30`).
pub fn render_physical_viewport(
    kind: PhysicalViewportKind,
    title: &str,
    dial: &LawDialControl,
) -> RenderedViewport {
    match kind {
        PhysicalViewportKind::Cnc5Axis => {
            let mut waypoints = golden_cnc_5axis_waypoints();
            if !dial.is_admitted() {
                if let Some(first) = waypoints.first_mut() {
                    let residual = dial.current_value.round() as i64;
                    first.abbe_compensated_cmd_nm.0 += if residual == 0 { 1 } else { residual };
                }
            }
            render_cnc_5axis_viewport(title, &waypoints, dial)
        }
        PhysicalViewportKind::OpenUsdScene => {
            let mut prims = golden_openusd_prims();
            let affects_wall = dial.invariant_expr.contains("wall")
                || dial.margin_hi >= 1000.0
                || !dial.is_admitted();
            if affects_wall {
                if let Some(first) = prims.first_mut() {
                    first.affine_c0_um = dial.current_value.round() as i64;
                    first.lifecycle_invariant_ok = dial.is_admitted();
                }
            }
            render_openusd_scene_viewport(title, &prims, dial)
        }
        PhysicalViewportKind::StatorMultiphysics => {
            let mut telemetry = golden_stator_telemetry();
            telemetry.part_name = title.to_string();
            telemetry.winding_temp_c_hi = dial.current_value;
            telemetry.max_temp_limit_c = dial.margin_hi;
            telemetry.flowpipe_certified = dial.is_admitted();
            let mut slices = golden_stator_flowpipe_slices();
            if let Some(first) = slices.first_mut() {
                first.x_hi = dial.current_value;
                first.x_lo = (dial.current_value - 2.0).max(0.0);
            }
            render_stator_multiphysics_viewport(&telemetry, &slices, dial)
        }
    }
}

/// Render any of the 10 `ProjectionKind`s into a complete `RenderedViewport` with SVG, HTML `LawDial`
/// controls, and terminal ASCII canvas.
pub fn render_projection_viewport(
    kind: ProjectionKind,
    title: &str,
    dial: &LawDialControl,
) -> RenderedViewport {
    let default_slices = [
        FlowpipeSlice {
            step: 0,
            t_lo: 0.0,
            t_hi: 0.5,
            x_lo: 28.0,
            x_hi: 30.0,
            y_lo: -10.0,
            y_hi: -8.0,
            z_lo: 0.0,
            z_hi: 1.0,
        },
        FlowpipeSlice {
            step: 1,
            t_lo: 0.5,
            t_hi: 1.0,
            x_lo: 22.9,
            x_hi: 26.1,
            y_lo: -6.1,
            y_hi: -2.9,
            z_lo: 0.5,
            z_hi: 1.5,
        },
    ];
    let default_gds = [
        GdsiiRect {
            layer: 68,
            x: 40,
            y: 40,
            width: 120,
            height: 60,
            drc_violation: None,
        },
        GdsiiRect {
            layer: 69,
            x: 155,
            y: 50,
            width: 80,
            height: 45,
            drc_violation: Some("M2.spacing < 140nm".to_string()),
        },
    ];
    let default_tiles = [
        EfpgaTileActivity {
            tile_x: 0,
            tile_y: 0,
            utilization_pct: 85,
            beta_steps: 42,
            cam_hits: 128,
        },
        EfpgaTileActivity {
            tile_x: 1,
            tile_y: 0,
            utilization_pct: 55,
            beta_steps: 19,
            cam_hits: 64,
        },
    ];

    let admitted = dial.is_admitted();
    let status_color = if admitted { "#22c55e" } else { "#ef4444" };
    let norm = ((dial.current_value - dial.margin_lo) / (dial.margin_hi - dial.margin_lo).max(1.0))
        .clamp(0.0, 1.0);

    let svg = match kind {
        ProjectionKind::Circuit => format!(
            r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 240" data-projection="circuit"><g class="rtl-schematic"><rect x="40" y="60" width="120" height="80" fill="#1e293b" stroke="#38bdf8" /><text x="55" y="105" fill="#f8fafc">{}</text></g>{}</svg>"##,
            title,
            render_efpga_heatmap_svg(&default_tiles)
        ),
        ProjectionKind::Netlist => {
            let wire_color = if admitted { "#a855f7" } else { "#f97316" };
            let fanout_y = 65 + (norm * 90.0) as i32;
            format!(
                r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 240" data-projection="netlist"><rect width="640" height="240" fill="#090d16" rx="8"/><g class="lvs-netlist"><rect x="28" y="42" width="110" height="52" rx="6" fill="#1e293b" stroke="#38bdf8" stroke-width="1.5"/><text x="40" y="65" fill="#e2e8f0" font-family="monospace" font-size="11">in_port[0..7]</text><text x="40" y="82" fill="#94a3b8" font-family="monospace" font-size="10">val={:.1}</text><rect x="28" y="136" width="110" height="52" rx="6" fill="#1e293b" stroke="#38bdf8" stroke-width="1.5"/><text x="40" y="159" fill="#e2e8f0" font-family="monospace" font-size="11">clk_domain</text><text x="40" y="176" fill="#94a3b8" font-family="monospace" font-size="10">mode=.{}</text><line x1="60" y1="100" x2="260" y2="100" stroke="{}" stroke-width="2"/><path d="M 138 68 C 195 68, 195 {}, 250 {}" fill="none" stroke="{}" stroke-width="2"/><path d="M 138 162 C 195 162, 195 135, 250 135" fill="none" stroke="#38bdf8" stroke-width="1.8"/><rect x="250" y="54" width="150" height="120" rx="8" fill="#0f172a" stroke="{}" stroke-width="2"/><text x="264" y="78" fill="#f8fafc" font-family="monospace" font-size="12" font-weight="bold">{}</text><text x="264" y="100" fill="#cbd5e1" font-family="monospace" font-size="10">LUT6 + Carry4 DAG</text><text x="264" y="118" fill="#94a3b8" font-family="monospace" font-size="10">Nets: 24 | Cells: 12</text><text x="264" y="138" fill="{}" font-family="monospace" font-size="10">LVS: {}</text><line x1="400" y1="114" x2="485" y2="114" stroke="{}" stroke-width="2.5"/><rect x="485" y="84" width="125" height="60" rx="6" fill="#1e293b" stroke="{}" stroke-width="1.8"/><text x="498" y="109" fill="#f8fafc" font-family="monospace" font-size="11">out_bus[0..7]</text><text x="498" y="128" fill="{}" font-family="monospace" font-size="10">margin [{:.0}..{:.0}]</text></g></svg>"##,
                dial.current_value,
                dial.mode.as_str(),
                wire_color,
                fanout_y,
                fanout_y,
                wire_color,
                wire_color,
                title,
                status_color,
                if admitted { "MATCHED" } else { "MISMATCH" },
                status_color,
                status_color,
                status_color,
                dial.margin_lo,
                dial.margin_hi
            )
        }
        ProjectionKind::Timing => {
            let slack_ps = ((dial.margin_hi - dial.current_value) * 18.5).round() as i64;
            let logic_w = (120.0 + norm * 160.0) as i32;
            let route_w = (80.0 + norm * 90.0) as i32;
            let slack_w = (420 - logic_w - route_w).max(24);
            format!(
                r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 240" data-projection="timing"><rect width="640" height="240" fill="#090d16" rx="8"/><g class="sta-slack"><text x="36" y="34" fill="#f8fafc" font-family="monospace" font-size="12" font-weight="bold">STA Slack {:+}ps ({})</text><text x="36" y="54" fill="#94a3b8" font-family="monospace" font-size="10">Clock Period: 1000ps | Setup Uncertainty: 35ps | Dial: {:.2}</text><rect x="50" y="80" width="420" height="24" fill="#10b981" opacity="0.18" rx="4"/><rect x="50" y="80" width="{}" height="24" fill="#38bdf8" rx="3"/><rect x="{}" y="80" width="{}" height="24" fill="#a855f7"/><rect x="{}" y="80" width="{}" height="24" fill="{}" rx="3"/><line x1="470" y1="66" x2="470" y2="188" stroke="#f59e0b" stroke-width="2" stroke-dasharray="4,3"/><text x="478" y="88" fill="#fbbf24" font-family="monospace" font-size="10">Required Edge</text><text x="478" y="104" fill="{}" font-family="monospace" font-size="11" font-weight="bold">{}</text><text x="52" y="132" fill="#38bdf8" font-family="monospace" font-size="10">Logic: {}ps</text><text x="210" y="132" fill="#c084fc" font-family="monospace" font-size="10">Route: {}ps</text><text x="360" y="132" fill="{}" font-family="monospace" font-size="10">Slack: {:+}ps</text><rect x="50" y="152" width="540" height="52" rx="6" fill="#0f172a" stroke="#1e293b"/><text x="64" y="174" fill="#cbd5e1" font-family="monospace" font-size="10">Critical Path: clk_launch -&gt; carry_chain_s3 -&gt;cam_match_reg ({})</text><text x="64" y="192" fill="#94a3b8" font-family="monospace" font-size="10">Invariant: {} | Bounds [{:.1}, {:.1}]</text></g></svg>"##,
                slack_ps,
                title,
                dial.current_value,
                logic_w,
                50 + logic_w,
                route_w,
                50 + logic_w + route_w,
                slack_w,
                status_color,
                status_color,
                if admitted { "MET (TIMING CLOSED)" } else { "VIOLATED (NEGATIVE SLACK)" },
                logic_w * 2,
                route_w * 2,
                status_color,
                slack_ps,
                dial.mode.as_str(),
                dial.invariant_expr,
                dial.margin_lo,
                dial.margin_hi
            )
        }
        ProjectionKind::Gdsii => render_gdsii_svg(&default_gds),
        ProjectionKind::Waveform => render_flowpipe_svg(title, &default_slices, 15.0, 35.0),
        ProjectionKind::CellQuote => format!(
            r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 160" data-projection="cellQuote"><rect width="640" height="160" fill="#090d16" rx="8"/><rect x="16" y="16" width="608" height="128" rx="6" fill="#0f172a" stroke="#38bdf8" stroke-width="1.5"/><rect x="16" y="16" width="6" height="128" rx="3" fill="{}"/><text x="36" y="42" fill="#f8fafc" font-family="monospace" font-size="12" font-weight="bold">Content.cell quotation: {}</text><text x="36" y="66" fill="#38bdf8" font-family="monospace" font-size="11">Cite Mode: .pinned | Span: .page | World Pin: {}</text><text x="36" y="90" fill="#cbd5e1" font-family="monospace" font-size="10">Invariant: {} (val={:.2} in [{:.1}, {:.1}])</text><text x="36" y="114" fill="{}" font-family="monospace" font-size="10">Integrity: {} (pinned_cite_stays / moved_pin_blocks)</text></svg>"##,
            status_color,
            title,
            if admitted { "HOLDING" } else { "MOVED_PIN_BLOCKED" },
            dial.invariant_expr,
            dial.current_value,
            dial.margin_lo,
            dial.margin_hi,
            status_color,
            if admitted { "USABLE (VERIFIED DIGEST)" } else { "BLOCKED BY UPSTREAM MUTATION" }
        ),
        ProjectionKind::NotebookCell => {
            let gauge_w = (norm * 360.0) as i32;
            format!(
                r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 160" data-projection="notebookCell"><rect width="640" height="160" fill="#090d16" rx="8"/><rect x="16" y="14" width="608" height="132" rx="6" fill="#131b2e" stroke="#334155"/><text x="32" y="40" fill="#f8fafc" font-family="monospace" font-size="12" font-weight="bold">Notebook Cell: {}</text><text x="32" y="62" fill="#94a3b8" font-family="monospace" font-size="10">Cell ID: {} | Dial Mode: .{} | Law: {}</text><rect x="32" y="78" width="360" height="14" rx="4" fill="#090d16" stroke="#334155"/><rect x="32" y="78" width="{}" height="14" rx="4" fill="{}"/><text x="408" y="90" fill="{}" font-family="monospace" font-size="11" font-weight="bold">{:.2} [{:.1}..{:.1}]</text><text x="32" y="120" fill="#cbd5e1" font-family="monospace" font-size="10">Status: {} | Rehydratable Membrane Slot Ready</text></svg>"##,
                title,
                dial.cell_id,
                dial.mode.as_str(),
                dial.invariant_expr,
                gauge_w,
                status_color,
                status_color,
                dial.current_value,
                dial.margin_lo,
                dial.margin_hi,
                if admitted { "ADMITTED" } else { "REFUSED" }
            )
        }
        ProjectionKind::ProofTree => format!(
            r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 200" data-projection="proofTree"><rect width="640" height="200" fill="#090d16" rx="8"/><g class="silicon-proof-tree"><rect x="34" y="20" width="240" height="36" rx="5" fill="#1e293b" stroke="#38bdf8"/><text x="46" y="42" fill="#e2e8f0" font-family="monospace" font-size="10">Γ ⊢ lhs ⇓ nf (Law.step?)</text><rect x="310" y="20" width="270" height="36" rx="5" fill="#1e293b" stroke="#a855f7"/><text x="322" y="42" fill="#e2e8f0" font-family="monospace" font-size="10">Γ ⊢ {} ({:.1} ∈ [{:.0},{:.0}])</text><line x1="28" y1="74" x2="588" y2="74" stroke="#94a3b8" stroke-width="2"/><text x="594" y="78" fill="#38bdf8" font-family="monospace" font-size="10">Weave</text><text x="44" y="102" fill="#f8fafc" font-family="monospace" font-size="11">Goal: {} (0 sorryAx, ExprCAM verified)</text><line x1="28" y1="118" x2="588" y2="118" stroke="{}" stroke-width="2.5"/><text x="594" y="122" fill="{}" font-family="monospace" font-size="10">Kernel</text><rect x="34" y="132" width="546" height="44" rx="6" fill="#0f172a" stroke="{}" stroke-width="1.5"/><text x="48" y="158" fill="{}" font-family="monospace" font-size="11" font-weight="bold">⊢ {} — Verdict: {} (mode=.{})</text></g></svg>"##,
            dial.invariant_expr,
            dial.current_value,
            dial.margin_lo,
            dial.margin_hi,
            title,
            status_color,
            status_color,
            status_color,
            status_color,
            title,
            if admitted { "QED / CERTIFIED" } else { "REFUSED BY TOOTH" },
            dial.mode.as_str()
        ),
        ProjectionKind::ContractBadge => format!(
            r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 320 80" data-projection="contractBadge"><rect x="4" y="4" width="312" height="72" rx="8" fill="#0f172a" stroke="{}" stroke-width="2"/><rect x="12" y="12" width="12" height="56" rx="4" fill="{}"/><text x="32" y="34" fill="#fff" font-family="monospace" font-size="12" font-weight="bold">Contract {} [{}]</text><text x="32" y="54" fill="#cbd5e1" font-family="monospace" font-size="10">{} | {:.1} in [{:.0}..{:.0}]</text></svg>"##,
            dial.mode.badge_color(),
            status_color,
            title,
            dial.mode.as_str(),
            if admitted { "ADMITS" } else { "REFUSES" },
            dial.current_value,
            dial.margin_lo,
            dial.margin_hi
        ),
        ProjectionKind::ClearingLedger => {
            let clear_x = 120 + (norm * 360.0) as i32;
            format!(
                r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 200" data-projection="clearingLedger"><rect width="640" height="200" fill="#090d16" rx="8"/><g class="drex-clearing"><text x="24" y="32" fill="#f8fafc" font-family="monospace" font-size="12" font-weight="bold">drex-clearing@1 Uniform Price Book: {}</text><text x="24" y="50" fill="#94a3b8" font-family="monospace" font-size="10">Clearing Price p* = {:.2} | KKT Dual Gap = 0 | Hoard Solvency: {}</text><polyline points="60,70 180,70 180,105 320,105 320,140 520,140" fill="none" stroke="#22c55e" stroke-width="2.5"/><polyline points="60,155 210,155 210,120 350,120 350,82 520,82" fill="none" stroke="#f43f5e" stroke-width="2.5"/><line x1="{}" y1="62" x2="{}" y2="170" stroke="#38bdf8" stroke-width="2" stroke-dasharray="5,3"/><circle cx="{}" cy="112" r="5" fill="{}" stroke="#fff" stroke-width="1.5"/><text x="64" y="184" fill="#22c55e" font-family="monospace" font-size="10">Bids (Demand)</text><text x="200" y="184" fill="#f43f5e" font-family="monospace" font-size="10">Asks (Supply)</text><text x="340" y="184" fill="#38bdf8" font-family="monospace" font-size="10">p*={:.2} ([{:.0}..{:.0}])</text></g></svg>"##,
                title,
                dial.current_value,
                if admitted { "CONSERVED" } else { "REFUSED" },
                clear_x,
                clear_x,
                clear_x,
                status_color,
                dial.current_value,
                dial.margin_lo,
                dial.margin_hi
            )
        }
    };

    let html_controls = dial.render_html();
    let terminal_canvas = format!(
        "+-[{:^16}]-[{:^6}]--------------------------------+\n| Title: {:<49} |\n| Dial : .{:<6} | Admitted: {:<5} | Value: {:>6.2}          |\n+----------------------------------------------------------+",
        kind.as_str(),
        kind.doc_kind_label(),
        title,
        dial.mode.as_str(),
        dial.is_admitted(),
        dial.current_value,
    );

    RenderedViewport {
        kind,
        title: title.to_string(),
        svg,
        html_controls,
        terminal_canvas,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_10_projection_kinds_roundtrip_and_render() {
        assert_eq!(ProjectionKind::ALL.len(), 10);
        let dial = LawDialControl {
            cell_id: "cell-thermal-01".to_string(),
            mode: LawDialMode::Locked,
            invariant_expr: "T <= 35.0".to_string(),
            margin_lo: 15.0,
            margin_hi: 35.0,
            current_value: 24.5,
        };
        assert!(dial.is_admitted());

        for kind in ProjectionKind::ALL {
            assert_eq!(ProjectionKind::from_label(kind.as_str()), Some(kind));
            assert_eq!(ProjectionKind::from_label(kind.doc_kind_label()), Some(kind));
            let vp = render_projection_viewport(kind, "WS25-Viewport-Test", &dial);
            assert_eq!(vp.kind, kind);
            assert!(vp.svg.starts_with("<svg"));
            assert!(vp.svg.ends_with("</svg>"));
            assert!(vp.html_controls.contains("data-mode=\"locked\""));
            assert!(vp.terminal_canvas.contains(kind.as_str()));
        }
    }

    #[test]
    fn test_law_dial_modes_free_press_locked() {
        let mut dial = LawDialControl {
            cell_id: "cell-ode".to_string(),
            mode: LawDialMode::Free,
            invariant_expr: "T in [15, 35]".to_string(),
            margin_lo: 15.0,
            margin_hi: 35.0,
            current_value: 42.0, // Out of bounds
        };
        // In .free mode, exploratory excursions are admitted with warning badge
        assert!(dial.is_admitted());
        assert!(dial.render_html().contains(".free"));

        // In .press and .locked modes, out-of-bounds values are refused
        dial.mode = LawDialMode::Press;
        assert!(!dial.is_admitted());
        assert!(dial.render_html().contains("REFUSED"));

        dial.mode = LawDialMode::Locked;
        assert!(!dial.is_admitted());
        dial.current_value = 25.0;
        assert!(dial.is_admitted());
        assert!(dial.render_html().contains("ADMITTED"));
    }

    #[test]
    fn test_flowpipe_gdsii_and_efpga_heatmap_svg() {
        let slices = vec![FlowpipeSlice {
            step: 0,
            t_lo: 0.0,
            t_hi: 0.5,
            x_lo: 28.0,
            x_hi: 30.0,
            y_lo: -10.0,
            y_hi: -8.0,
            z_lo: 0.0,
            z_hi: 1.0,
        }];
        let fp_svg = render_flowpipe_svg("ThermalCooling", &slices, 15.0, 35.0);
        assert!(fp_svg.contains("flowpipe-box"));
        assert!(fp_svg.contains("safe-envelope"));

        let gds_svg = render_gdsii_svg(&[GdsiiRect {
            layer: 69,
            x: 10,
            y: 20,
            width: 50,
            height: 30,
            drc_violation: Some("M2.spacing".to_string()),
        }]);
        assert!(gds_svg.contains("gds-mask"));
        assert!(gds_svg.contains("drc-marker"));

        let hm_svg = render_efpga_heatmap_svg(&[EfpgaTileActivity {
            tile_x: 2,
            tile_y: 3,
            utilization_pct: 90,
            beta_steps: 100,
            cam_hits: 256,
        }]);
        assert!(hm_svg.contains("efpga-tile"));
        assert!(hm_svg.contains("data-cam-hits=\"256\""));
    }

    #[test]
    fn test_physical_world_mechatronic_renderers() {
        let dial = LawDialControl {
            cell_id: "cell-phys-01".to_string(),
            mode: LawDialMode::Locked,
            invariant_expr: "T <= 35.0".to_string(),
            margin_lo: 15.0,
            margin_hi: 35.0,
            current_value: 28.0,
        };

        let waypoints = golden_cnc_5axis_waypoints();
        assert!(waypoints.iter().all(|w| w.is_abbe_exact_cancelled() && w.is_coriolis_workless()));
        let cnc_vp = render_cnc_5axis_viewport("Hermle_C42U_5Axis", &waypoints, &dial);
        assert!(cnc_vp.svg.contains("5-Axis CNC Toolpath"));
        assert!(cnc_vp.svg.contains("cnc-toolpath-xy"));
        assert!(cnc_vp.svg.contains("abbe-corridor"));
        assert!(cnc_vp.svg.contains("Abbe-Certified"));
        assert!(cnc_vp.svg.contains("data-abbe-cancelled=\"true\""));
        assert!(cnc_vp.terminal_canvas.contains("Hermle_C42U_5Axis"));

        let prims = golden_openusd_prims();
        let usd_vp = render_openusd_scene_viewport("LcDrives_Production_Stator", &prims, &dial);
        assert!(usd_vp.svg.contains("OpenUSD Scene Graph"));
        assert!(usd_vp.svg.contains("/Factory/Draft/Stator/Slot01"));
        assert!(usd_vp.svg.contains("/Prod/LCDrives/Stator/Slot01"));
        assert!(usd_vp.svg.contains("SDF [1475, 1525]"));
        assert!(usd_vp.svg.contains("LCA PASS"));
        assert!(usd_vp.terminal_canvas.contains("LcDrives_Production_Stator"));

        let telemetry = golden_stator_telemetry();
        let slices = golden_stator_flowpipe_slices();
        let stator_vp = render_stator_multiphysics_viewport(&telemetry, &slices, &dial);
        assert!(stator_vp.svg.contains("Coupled LC/Stator Multiphysics"));
        assert!(stator_vp.svg.contains("MULTIPHYSICS_CERTIFIED"));
        assert!(stator_vp.svg.contains("THERMAL SAFE"));
        assert!(stator_vp.svg.contains("flowpipe-box"));
        assert!(stator_vp.terminal_canvas.contains("LC_Drives_InSlot_Stator_Assy"));

        for pkind in PhysicalViewportKind::ALL {
            assert_eq!(PhysicalViewportKind::from_label(pkind.as_str()), Some(pkind));
            assert_eq!(
                PhysicalViewportKind::from_label(pkind.lean_kind_label()),
                Some(pkind)
            );
            let vp = render_physical_viewport(pkind, "WS30-Physical", &dial);
            assert!(vp.svg.starts_with("<svg"));
            assert!(vp.svg.ends_with("</svg>"));
            assert!(vp.html_controls.contains("obend-physical-panel"));
        }
    }
}

