//! Streaming `.vcd`, `.stl`, `.ngc`, `.smt2`, and `.sv` artifact parsers plus the PIDE
//! `ObendSession` elaboration and law-affordance client.

pub mod apps;
pub mod evaluator;

pub use apps::{
    discover_apps, discover_apps_in_root, find_workspace_root, inspect_app_in_root,
    parse_ngc_text, parse_obend_layer_source, parse_smt2_text, parse_stl_bytes, parse_sv_summary,
    parse_vcd_file, parse_vcd_reader, render_vcd_waveform_svg, validate_app_slug, vcd_bits_to_hex,
    AppArtifactDetail, AppArtifactSummary, AppObendLayerSource, AppRtlModuleSummary,
    AppSmt2LecSpec, AppVcdDigest, CamArtifactBundle, NgcArtifactStats, StlArtifactStats,
    VcdSignalSummary, WorkspaceAppsReport,
};
pub use evaluator::{
    ClaimSummary, DeclarationSummary, ElaborationSummary, LawAffordanceReport, LawSummary,
    LeafBookSummary, NotebookCell, NotebookRunner,
};
