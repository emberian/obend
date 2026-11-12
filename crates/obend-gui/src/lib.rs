//! Streaming `.vcd`, `.stl`, `.ngc`, `.smt2`, and `.sv` artifact parsers plus the PIDE
//! `ObendSession` dependency-aware `.obnb` workbook runner, bidirectional lens scrubber, and
//! CAE/PDE/PCB/FEEC/6DOF/ZK multi-projection cards.

pub mod apps;
pub mod evaluator;

pub use apps::{
    discover_apps, discover_apps_in_root, find_workspace_root, inspect_app_in_root,
    parse_ngc_text, parse_obend_layer_source, parse_smt2_text, parse_stl_bytes, parse_sv_summary,
    parse_vcd_file, parse_vcd_reader, render_vcd_waveform_svg, validate_app_slug, vcd_bits_to_hex,
    AppArtifactDetail, AppArtifactSummary, AppObendLayerSource, AppRtlModuleSummary,
    AppSmt2LecSpec, AppVcdDigest, CamArtifactBundle, FeecSimplicialFemCard,
    FrustumRedactedViewCard, NgcArtifactStats, PcbMultiphysicsDfmCard, PdeConservationCard,
    ProjectionCard, StlArtifactStats, VcdSignalSummary, Vehicle6DofTrajectoryCard,
    VerifiedProofBadge, WorkspaceAppsReport, ZkCustodyReceiptCard,
};
pub use evaluator::{
    extract_wikilink_owners, hex_encode_32, sha256_bytes, ClaimSummary, DeclarationSummary,
    ElaborationSummary, LawAffordanceReport, LawSummary, LeafBookSummary, NotebookCell,
    NotebookRunner, WorkbookExecutionReport,
};
