pub mod apps;
pub mod evaluator;
pub mod fpga;
pub mod server;
pub mod viewport;

pub use apps::{
    find_workspace_root, get_flagship_app_detail, get_flagship_app_detail_in_root,
    list_flagship_apps, list_flagship_apps_in_root, parse_ngc_text, parse_smt2_text,
    parse_stl_bytes, parse_vcd_file, parse_vcd_reader, render_vcd_waveform_svg, vcd_bits_to_hex,
    AppObendLayerSource, AppRtlModuleSummary, AppSmt2LecSpec, AppVcdDigest, FidgetCamArtifacts,
    FlagshipAppDescriptor, FlagshipAppDetailResponse, FlagshipAppSummary,
    FlagshipAppsListResponse, NgcArtifactStats, StlArtifactStats, VcdSignalSummary, FLAGSHIP_APPS,
};
pub use evaluator::{NotebookCell, NotebookRunner};
pub use fpga::{
    build_demo_obcam_wire_frame, execute_fpga_dpr_swap, execute_fpga_step, query_fpga_ila,
    query_fpga_telemetry, FpgaDprSwapRequest, FpgaDprSwapResponse, FpgaIlaSnapshot,
    FpgaStepRequest, FpgaStepResponse, FpgaTelemetryResponse, IlaNamedSignal,
};
pub use server::{
    evaluate_multi_field_admitted, obend_cell_pop_lean, obend_cell_weave_cert,
    suggest_multi_field_admits, DialRequest, DialResponse, EvalRequest, EvalResponse,
    FieldRepairDelta, FieldRepairSuggestion, LeanBridgeRequest, LeanBridgeResponse, LeanGoalView,
    NotebookStateResponse, WorkbenchCellState, WorkbenchCommand, WorkbenchEngine, WorkbenchEvent,
    WorkbenchServer, WovenCertificate,
};
pub use viewport::{
    golden_cnc_5axis_waypoints, golden_openusd_prims, golden_stator_flowpipe_slices,
    golden_stator_telemetry, render_cnc_5axis_ansi, render_cnc_5axis_toolpath_svg,
    render_cnc_5axis_viewport, render_efpga_heatmap_svg, render_flowpipe_svg, render_gdsii_svg,
    render_openusd_scene_ansi, render_openusd_scene_svg, render_openusd_scene_viewport,
    render_physical_viewport, render_projection_viewport, render_stator_multiphysics_ansi,
    render_stator_multiphysics_svg, render_stator_multiphysics_viewport, Cnc5AxisWaypoint,
    EfpgaTileActivity, FlowpipeSlice, GdsiiRect, LawDialControl, LawDialMode, OpenUsdPrimNode,
    PhysicalViewportKind, ProjectionKind, RenderedViewport, StatorChannelTelemetry,
};
