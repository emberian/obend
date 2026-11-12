//! Streaming `.vcd` waveform parser & SVG renderer, binary/ASCII `.stl` mesh inspector,
//! 5-axis `.ngc` G-code toolpath analyzer, `.smt2` / `.sv` / `.obend` structural parsers,
//! and dynamic workspace `apps/` directory discovery.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};

/// Summary of an application directory discovered under `<workspace>/apps/<slug>`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppArtifactSummary {
    pub slug: String,
    pub obend_layer_count: usize,
    pub obend_files: Vec<String>,
    pub sv_files: Vec<String>,
    pub smt2_lec_present: bool,
    pub smt2_files: Vec<String>,
    pub vcd_present: bool,
    pub vcd_build_status: String,
    pub vcd_signal_count: usize,
    pub vcd_total_transitions: u64,
    pub cam_artifacts_present: bool,
}

/// Summary report across all subdirectories in `<workspace>/apps/`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkspaceAppsReport {
    pub apps_root: String,
    pub total_apps: usize,
    pub vcd_present_count: usize,
    pub lec_present_count: usize,
    pub apps: Vec<AppArtifactSummary>,
}

/// Discovered `.obend` source layer inside `apps/<slug>/`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppObendLayerSource {
    pub filename: String,
    pub rel_path: String,
    pub size_bytes: u64,
    pub line_count: usize,
    pub imports: Vec<String>,
    pub specs: Vec<String>,
    pub claims: Vec<String>,
    pub laws: Vec<String>,
    pub source: String,
}

/// Discovered `.smt2` `QF_BV` Logical Equivalence Checking (LEC) specification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppSmt2LecSpec {
    pub filename: String,
    pub rel_path: String,
    pub size_bytes: u64,
    pub line_count: usize,
    pub logic: Option<String>,
    pub declare_const_count: usize,
    pub define_fun_count: usize,
    pub assert_count: usize,
    pub check_sat_count: usize,
    pub source: String,
}

/// Discovered synthesizable SystemVerilog `.sv` RTL module summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppRtlModuleSummary {
    pub filename: String,
    pub rel_path: String,
    pub size_bytes: u64,
    pub line_count: usize,
    pub module_names: Vec<String>,
    pub always_ff_count: usize,
}

/// Per-signal transition & timeline summary extracted from a `.vcd` waveform file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcdSignalSummary {
    pub name: String,
    pub scope: String,
    pub width: usize,
    pub transitions: u64,
    pub initial_value_hex: String,
    pub last_value_hex: String,
    pub samples: Vec<(u64, String)>,
}

/// `.vcd` waveform digest (`build_status = "not_built"` when no VCD file is present).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppVcdDigest {
    pub present: bool,
    pub build_status: String,
    pub rel_path: Option<String>,
    pub size_bytes: u64,
    pub version: Option<String>,
    pub timescale: Option<String>,
    pub timestamp_count: usize,
    pub start_time: u64,
    pub end_time: u64,
    pub signal_count: usize,
    pub total_transitions: u64,
    pub signals: Vec<VcdSignalSummary>,
    pub waveform_svg: Option<String>,
}

/// Binary/ASCII `.stl` 3D triangle mesh statistics.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StlArtifactStats {
    pub rel_path: String,
    pub size_bytes: u64,
    pub format: String,
    pub header_text: String,
    pub triangle_count: u32,
    pub binary_size_consistent: bool,
    pub bbox_min: [f32; 3],
    pub bbox_max: [f32; 3],
}

/// 5-axis `.ngc` G-code toolpath statistics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NgcArtifactStats {
    pub rel_path: String,
    pub size_bytes: u64,
    pub line_count: usize,
    pub rapid_g00_moves: usize,
    pub linear_g01_moves: usize,
    pub no_gouge_verified_points: usize,
    pub min_tool_sdf: Option<i64>,
    pub max_tool_sdf: Option<i64>,
    pub spindle_rpm: Option<u32>,
    pub preview_lines: Vec<String>,
}

/// Combined CAD/CAM buildout artifact report (`.stl` + `.ngc`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CamArtifactBundle {
    pub build_status: String,
    pub stl: Option<StlArtifactStats>,
    pub ngc: Option<NgcArtifactStats>,
}

/// Detailed artifact inspection report for `<workspace>/apps/<slug>`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AppArtifactDetail {
    pub slug: String,
    pub top_obend_file: Option<String>,
    pub obend_layers: Vec<AppObendLayerSource>,
    pub lec_specs: Vec<AppSmt2LecSpec>,
    pub rtl_modules: Vec<AppRtlModuleSummary>,
    pub firmware_files: Vec<String>,
    pub vcd_digest: AppVcdDigest,
    pub cam_artifacts: Option<CamArtifactBundle>,
}

/// Locate the Objective Bend repository workspace root.
pub fn find_workspace_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(root) = manifest_dir.parent().and_then(|p| p.parent()) {
        if root.join("apps").exists() {
            return root.to_path_buf();
        }
    }
    for candidate in [".", "..", "../.."] {
        let p = Path::new(candidate);
        if p.join("apps").exists() {
            return p.to_path_buf();
        }
    }
    PathBuf::from(".")
}

/// Validate a `<slug>` directory name against path traversal or empty values.
pub fn validate_app_slug(raw_slug: &str) -> Result<&str, String> {
    let trimmed = raw_slug.trim().trim_matches('/');
    if trimmed.is_empty()
        || trimmed.contains("..")
        || trimmed.contains('/')
        || trimmed.contains('\\')
    {
        return Err(format!("Invalid app slug: `{raw_slug}`"));
    }
    Ok(trimmed)
}

/// Discover all application directories in the active workspace (`<workspace>/apps/*`).
pub fn discover_apps() -> WorkspaceAppsReport {
    discover_apps_in_root(&find_workspace_root())
}

/// Discover all application directories relative to `workspace_root`.
pub fn discover_apps_in_root(workspace_root: &Path) -> WorkspaceAppsReport {
    let apps_dir = workspace_root.join("apps");
    let mut slugs = Vec::new();
    if let Ok(entries) = fs::read_dir(&apps_dir) {
        for ent in entries.flatten() {
            let p = ent.path();
            if p.is_dir() {
                let name = ent.file_name().to_string_lossy().into_owned();
                if !name.starts_with('.') {
                    slugs.push(name);
                }
            }
        }
    }
    slugs.sort();

    let mut apps = Vec::with_capacity(slugs.len());
    let mut vcd_present_count = 0usize;
    let mut lec_present_count = 0usize;

    for slug in &slugs {
        let detail = build_app_detail(workspace_root, slug, false);
        if detail.vcd_digest.present {
            vcd_present_count += 1;
        }
        if !detail.lec_specs.is_empty() {
            lec_present_count += 1;
        }
        let cam_artifacts_present = detail
            .cam_artifacts
            .as_ref()
            .map(|c| c.stl.is_some() || c.ngc.is_some())
            .unwrap_or(false);
        apps.push(AppArtifactSummary {
            slug: slug.clone(),
            obend_layer_count: detail.obend_layers.len(),
            obend_files: detail
                .obend_layers
                .iter()
                .map(|l| l.filename.clone())
                .collect(),
            sv_files: detail
                .rtl_modules
                .iter()
                .map(|m| m.filename.clone())
                .collect(),
            smt2_lec_present: !detail.lec_specs.is_empty(),
            smt2_files: detail
                .lec_specs
                .iter()
                .map(|s| s.filename.clone())
                .collect(),
            vcd_present: detail.vcd_digest.present,
            vcd_build_status: detail.vcd_digest.build_status,
            vcd_signal_count: detail.vcd_digest.signal_count,
            vcd_total_transitions: detail.vcd_digest.total_transitions,
            cam_artifacts_present,
        });
    }

    WorkspaceAppsReport {
        apps_root: apps_dir.display().to_string(),
        total_apps: apps.len(),
        vcd_present_count,
        lec_present_count,
        apps,
    }
}

/// Inspect `<workspace_root>/apps/<slug>` and parse its `.obend`, `.smt2`, `.sv`, `.vcd`, `.stl`, and `.ngc` artifacts.
pub fn inspect_app_in_root(
    workspace_root: &Path,
    raw_slug: &str,
    include_svg: bool,
) -> Result<AppArtifactDetail, String> {
    let slug = validate_app_slug(raw_slug)?;
    let app_dir = workspace_root.join("apps").join(slug);
    if !app_dir.is_dir() {
        return Err(format!("App directory does not exist: `{}`", app_dir.display()));
    }
    Ok(build_app_detail(workspace_root, slug, include_svg))
}

fn build_app_detail(workspace_root: &Path, slug: &str, include_svg: bool) -> AppArtifactDetail {
    let app_dir = workspace_root.join("apps").join(slug);

    let mut obend_paths = collect_files_with_ext(&app_dir, "obend", 2);
    obend_paths.sort();

    let mut obend_layers = Vec::with_capacity(obend_paths.len());
    for p in &obend_paths {
        if let Ok(source) = fs::read_to_string(p) {
            let meta_size = fs::metadata(p).map(|m| m.len()).unwrap_or(source.len() as u64);
            let filename = p
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_string();
            let rel_path = to_rel_slash(workspace_root, p);
            obend_layers.push(parse_obend_layer_source(
                filename, rel_path, meta_size, source,
            ));
        }
    }

    let top_obend_file = obend_layers
        .iter()
        .find(|l| {
            l.filename.contains("Top")
                || l.filename.contains("Composed")
                || l.filename.contains("Bundle")
        })
        .or_else(|| obend_layers.last())
        .map(|l| l.rel_path.clone());

    let mut smt2_paths = collect_files_with_ext(&app_dir, "smt2", 3);
    smt2_paths.sort();
    let mut lec_specs = Vec::with_capacity(smt2_paths.len());
    for p in &smt2_paths {
        if let Ok(source) = fs::read_to_string(p) {
            let meta_size = fs::metadata(p).map(|m| m.len()).unwrap_or(source.len() as u64);
            let filename = p
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_string();
            let rel_path = to_rel_slash(workspace_root, p);
            lec_specs.push(parse_smt2_text(filename, rel_path, meta_size, source));
        }
    }

    let mut sv_paths = collect_files_with_ext(&app_dir, "sv", 3);
    sv_paths.sort();
    let mut rtl_modules = Vec::with_capacity(sv_paths.len());
    for p in &sv_paths {
        if let Ok(source) = fs::read_to_string(p) {
            let meta_size = fs::metadata(p).map(|m| m.len()).unwrap_or(source.len() as u64);
            let filename = p
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_string();
            let rel_path = to_rel_slash(workspace_root, p);
            rtl_modules.push(parse_sv_summary(filename, rel_path, meta_size, &source));
        }
    }

    let mut firmware_files = Vec::new();
    let fw_dir = app_dir.join("firmware");
    if fw_dir.is_dir() {
        if let Ok(entries) = fs::read_dir(&fw_dir) {
            for ent in entries.flatten() {
                let p = ent.path();
                if p.is_file() {
                    firmware_files.push(to_rel_slash(workspace_root, &p));
                }
            }
        }
        firmware_files.sort();
    }

    let mut vcd_candidates = collect_files_with_ext(&app_dir, "vcd", 3);
    vcd_candidates.sort();
    let vcd_digest = if let Some(vcd_path) = vcd_candidates.first() {
        let rel = to_rel_slash(workspace_root, vcd_path);
        match parse_vcd_file(vcd_path, Some(rel), include_svg) {
            Ok(d) => d,
            Err(_) => empty_vcd_digest("corrupt_or_unreadable"),
        }
    } else {
        empty_vcd_digest("not_built")
    };

    let stl_candidates = collect_files_with_ext(&app_dir, "stl", 4);
    let ngc_candidates = collect_files_with_ext(&app_dir, "ngc", 4);
    let cam_artifacts = if !stl_candidates.is_empty() || !ngc_candidates.is_empty() {
        let stl = stl_candidates.first().and_then(|p| {
            let bytes = fs::read(p).ok()?;
            Some(parse_stl_bytes(to_rel_slash(workspace_root, p), &bytes))
        });
        let ngc = ngc_candidates.first().and_then(|p| {
            let text = fs::read_to_string(p).ok()?;
            let size_bytes = fs::metadata(p).map(|m| m.len()).unwrap_or(text.len() as u64);
            Some(parse_ngc_text(
                to_rel_slash(workspace_root, p),
                size_bytes,
                &text,
            ))
        });
        let build_status = match (&stl, &ngc) {
            (Some(_), Some(_)) => "built",
            (Some(_), None) | (None, Some(_)) => "partial",
            (None, None) => "not_built",
        }
        .to_string();
        Some(CamArtifactBundle {
            build_status,
            stl,
            ngc,
        })
    } else {
        None
    };

    AppArtifactDetail {
        slug: slug.to_string(),
        top_obend_file,
        obend_layers,
        lec_specs,
        rtl_modules,
        firmware_files,
        vcd_digest,
        cam_artifacts,
    }
}

fn empty_vcd_digest(status: &str) -> AppVcdDigest {
    AppVcdDigest {
        present: false,
        build_status: status.to_string(),
        rel_path: None,
        size_bytes: 0,
        version: None,
        timescale: None,
        timestamp_count: 0,
        start_time: 0,
        end_time: 0,
        signal_count: 0,
        total_transitions: 0,
        signals: Vec::new(),
        waveform_svg: None,
    }
}

fn collect_files_with_ext(dir: &Path, ext: &str, max_depth: usize) -> Vec<PathBuf> {
    let mut out = Vec::new();
    collect_files_rec(dir, ext, 0, max_depth, &mut out);
    out
}

fn collect_files_rec(
    dir: &Path,
    ext: &str,
    depth: usize,
    max_depth: usize,
    out: &mut Vec<PathBuf>,
) {
    if depth > max_depth || !dir.is_dir() {
        return;
    }
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for ent in entries.flatten() {
        let p = ent.path();
        let name = ent.file_name();
        let name_s = name.to_string_lossy();
        if name_s == "obj_dir" || name_s.starts_with('.') {
            continue;
        }
        if p.is_dir() {
            collect_files_rec(&p, ext, depth + 1, max_depth, out);
        } else if p
            .extension()
            .and_then(|e| e.to_str())
            .map(|e| e.eq_ignore_ascii_case(ext))
            .unwrap_or(false)
        {
            out.push(p);
        }
    }
}

fn to_rel_slash(root: &Path, target: &Path) -> String {
    target
        .strip_prefix(root)
        .unwrap_or(target)
        .to_string_lossy()
        .replace('\\', "/")
}

/// Parse an `.obend` layer file and extract imports, specs, claims, and laws.
pub fn parse_obend_layer_source(
    filename: String,
    rel_path: String,
    size_bytes: u64,
    source: String,
) -> AppObendLayerSource {
    let mut imports = Vec::new();
    let mut specs = Vec::new();
    let mut claims = Vec::new();
    let mut laws = Vec::new();
    let mut line_count = 0usize;

    for raw_line in source.lines() {
        line_count += 1;
        let t = raw_line.trim();
        if let Some(rest) = t.strip_prefix("import ") {
            imports.push(rest.trim().to_string());
        } else if let Some(rest) = t.strip_prefix("spec ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("")
                .trim();
            if !name.is_empty() {
                specs.push(name.to_string());
            }
        } else if let Some(rest) = t.strip_prefix("claim ") {
            let name = rest
                .split(|c: char| c == '(' || c == ':' || c.is_whitespace())
                .next()
                .unwrap_or("")
                .trim();
            if !name.is_empty() {
                claims.push(name.to_string());
            }
        } else if let Some(rest) = t.strip_prefix("law ") {
            let name = rest
                .split(|c: char| c == ':' || c.is_whitespace())
                .next()
                .unwrap_or("")
                .trim();
            if !name.is_empty() {
                laws.push(name.to_string());
            }
        }
    }

    AppObendLayerSource {
        filename,
        rel_path,
        size_bytes,
        line_count,
        imports,
        specs,
        claims,
        laws,
        source,
    }
}

/// Parse an SMT-LIB2 (`.smt2`) LEC specification and extract structural metrics.
pub fn parse_smt2_text(
    filename: String,
    rel_path: String,
    size_bytes: u64,
    source: String,
) -> AppSmt2LecSpec {
    let mut logic = None;
    let mut declare_const_count = 0usize;
    let mut define_fun_count = 0usize;
    let mut assert_count = 0usize;
    let mut check_sat_count = 0usize;
    let mut line_count = 0usize;

    for raw_line in source.lines() {
        line_count += 1;
        let code = raw_line.split(';').next().unwrap_or("").trim();
        if code.is_empty() {
            continue;
        }
        if let Some(after) = code.strip_prefix("(set-logic ") {
            let l = after.trim_end_matches(')').trim();
            if !l.is_empty() {
                logic = Some(l.to_string());
            }
        }
        declare_const_count += code.matches("(declare-const ").count()
            + code.matches("(declare-fun ").count();
        define_fun_count += code.matches("(define-fun ").count();
        assert_count += code.matches("(assert ").count() + usize::from(code == "(assert");
        check_sat_count += code.matches("(check-sat)").count();
    }

    AppSmt2LecSpec {
        filename,
        rel_path,
        size_bytes,
        line_count,
        logic,
        declare_const_count,
        define_fun_count,
        assert_count,
        check_sat_count,
        source,
    }
}

/// Parse a SystemVerilog `.sv` source file and extract module names and `always_ff` counts.
pub fn parse_sv_summary(
    filename: String,
    rel_path: String,
    size_bytes: u64,
    source: &str,
) -> AppRtlModuleSummary {
    let mut module_names = Vec::new();
    let mut always_ff_count = 0usize;
    let mut line_count = 0usize;

    for line in source.lines() {
        line_count += 1;
        let code = line.split("//").next().unwrap_or("").trim();
        if let Some(rest) = code.strip_prefix("module ") {
            let m = rest
                .split(|c: char| c.is_whitespace() || c == '(' || c == '#' || c == ';')
                .next()
                .unwrap_or("")
                .trim();
            if !m.is_empty() {
                module_names.push(m.to_string());
            }
        }
        always_ff_count += code.matches("always_ff").count();
    }

    AppRtlModuleSummary {
        filename,
        rel_path,
        size_bytes,
        line_count,
        module_names,
        always_ff_count,
    }
}

/// Convert a VCD binary bit-string (arbitrary width, e.g. 1..512 bits) into compact `"0x..."` hex.
pub fn vcd_bits_to_hex(bits: &[u8]) -> String {
    if bits.is_empty() {
        return "0x0".to_string();
    }
    if bits
        .iter()
        .any(|&b| matches!(b, b'x' | b'X' | b'z' | b'Z'))
    {
        let has_z = bits.iter().any(|&b| b == b'z' || b == b'Z');
        return if has_z {
            "0xZ".to_string()
        } else {
            "0xX".to_string()
        };
    }

    // Strip leading '0's while keeping at least 1 bit
    let first_one = bits.iter().position(|&b| b != b'0').unwrap_or(bits.len() - 1);
    let trimmed = &bits[first_one..];
    let rem = trimmed.len() % 4;
    let mut hex = String::with_capacity(2 + (trimmed.len() + 3) / 4);
    hex.push_str("0x");

    if rem > 0 {
        let mut nib = 0u8;
        for &b in &trimmed[..rem] {
            nib = (nib << 1) | u8::from(b == b'1');
        }
        let _ = write!(&mut hex, "{nib:x}");
    }
    for chunk in trimmed[rem..].chunks_exact(4) {
        let mut nib = 0u8;
        for &b in chunk {
            nib = (nib << 1) | u8::from(b == b'1');
        }
        let _ = write!(&mut hex, "{nib:x}");
    }
    hex
}

struct VcdCodeTrack {
    primary_name: String,
    primary_scope: String,
    width: usize,
    has_initial: bool,
    initial_bits: Vec<u8>,
    last_bits: Vec<u8>,
    transitions: u64,
    samples: Vec<(u64, String)>,
}

/// Parse a `.vcd` file from disk using a fast streaming byte-slice scanner.
pub fn parse_vcd_file(
    path: &Path,
    rel_path: Option<String>,
    include_svg: bool,
) -> Result<AppVcdDigest, String> {
    let file = File::open(path).map_err(|e| format!("open VCD {:?}: {e}", path))?;
    let size_bytes = file.metadata().map(|m| m.len()).unwrap_or(0);
    let reader = BufReader::with_capacity(64 * 1024, file);
    parse_vcd_reader(reader, rel_path, size_bytes, include_svg)
}

/// Streaming VCD waveform parser supporting scalar (`0`/`1`/`x`/`z`), arbitrary-width vector (`b...`),
/// and real (`r...`) changes with bounded per-signal sample capture.
pub fn parse_vcd_reader<R: BufRead>(
    mut reader: R,
    rel_path: Option<String>,
    size_bytes: u64,
    include_svg: bool,
) -> Result<AppVcdDigest, String> {
    let mut version: Option<String> = None;
    let mut timescale: Option<String> = None;
    let mut in_header = true;
    let mut pending_tag: Option<&'static str> = None;
    let mut pending_val = String::new();
    let mut scope_stack: Vec<String> = Vec::new();

    let mut code_map: HashMap<Vec<u8>, usize> = HashMap::new();
    let mut tracks: Vec<VcdCodeTrack> = Vec::new();
    let mut declared_signal_count = 0usize;

    let mut timestamp_count = 0usize;
    let mut start_time = 0u64;
    let mut end_time = 0u64;
    let mut current_time = 0u64;
    let mut saw_first_ts = false;

    let mut line_buf = Vec::with_capacity(512);
    loop {
        line_buf.clear();
        let n = reader
            .read_until(b'\n', &mut line_buf)
            .map_err(|e| format!("read VCD error: {e}"))?;
        if n == 0 {
            break;
        }
        let line = trim_ascii(&line_buf);
        if line.is_empty() {
            continue;
        }

        if in_header {
            let s = String::from_utf8_lossy(line);
            let st = s.trim();

            if let Some(tag) = pending_tag {
                if let Some(before_end) = st.strip_suffix("$end") {
                    if !before_end.trim().is_empty() {
                        if !pending_val.is_empty() {
                            pending_val.push(' ');
                        }
                        pending_val.push_str(before_end.trim());
                    }
                    let final_v = pending_val.trim().to_string();
                    if !final_v.is_empty() {
                        if tag == "version" {
                            version = Some(final_v);
                        } else if tag == "timescale" {
                            timescale = Some(final_v);
                        }
                    }
                    pending_val.clear();
                    pending_tag = None;
                } else {
                    if !pending_val.is_empty() {
                        pending_val.push(' ');
                    }
                    pending_val.push_str(st);
                }
                continue;
            }

            if st.starts_with("$enddefinitions") {
                in_header = false;
                continue;
            }
            if let Some(rest) = st.strip_prefix("$version") {
                if let Some(inner) = rest.strip_suffix("$end") {
                    let v = inner.trim();
                    if !v.is_empty() {
                        version = Some(v.to_string());
                    }
                } else {
                    pending_tag = Some("version");
                    pending_val = rest.trim().to_string();
                }
                continue;
            }
            if let Some(rest) = st.strip_prefix("$timescale") {
                if let Some(inner) = rest.strip_suffix("$end") {
                    let v = inner.trim();
                    if !v.is_empty() {
                        timescale = Some(v.to_string());
                    }
                } else {
                    pending_tag = Some("timescale");
                    pending_val = rest.trim().to_string();
                }
                continue;
            }
            if let Some(rest) = st.strip_prefix("$scope") {
                let inner = rest.strip_suffix("$end").unwrap_or(rest).trim();
                let mut toks = inner.split_whitespace();
                let _kind = toks.next();
                if let Some(scope_name) = toks.next() {
                    scope_stack.push(scope_name.to_string());
                }
                continue;
            }
            if st.starts_with("$upscope") {
                scope_stack.pop();
                continue;
            }
            if let Some(rest) = st.strip_prefix("$var") {
                let inner = rest.strip_suffix("$end").unwrap_or(rest).trim();
                let toks: Vec<&str> = inner.split_whitespace().collect();
                // `$var <type> <width> <id_code> <reference> [bit-select] $end`
                if toks.len() >= 4 {
                    let width = toks[1].parse::<usize>().unwrap_or(1);
                    let id_code = toks[2].as_bytes();
                    let sig_name = toks[3].to_string();
                    let cur_scope = scope_stack.join(".");
                    declared_signal_count += 1;

                    if let Some(&idx) = code_map.get(id_code) {
                        // Prefer shorter/non-internal signal name (e.g. `pc_out` over `w_16`)
                        let existing_internal = tracks[idx].primary_name.starts_with("w_");
                        let new_internal = sig_name.starts_with("w_");
                        if existing_internal && !new_internal {
                            tracks[idx].primary_name = sig_name;
                            tracks[idx].primary_scope = cur_scope;
                        }
                    } else {
                        let idx = tracks.len();
                        code_map.insert(id_code.to_vec(), idx);
                        tracks.push(VcdCodeTrack {
                            primary_name: sig_name,
                            primary_scope: cur_scope,
                            width,
                            has_initial: false,
                            initial_bits: Vec::new(),
                            last_bits: Vec::new(),
                            transitions: 0,
                            samples: Vec::with_capacity(24),
                        });
                    }
                }
                continue;
            }
        } else {
            // Value-change dump section
            match line[0] {
                b'#' => {
                    if let Some(ts) = parse_u64_ascii(&line[1..]) {
                        current_time = ts;
                        timestamp_count += 1;
                        if !saw_first_ts {
                            start_time = ts;
                            saw_first_ts = true;
                        }
                        end_time = ts;
                    }
                }
                b'$' => {
                    // `$dumpvars`, `$end`, `$comment`, etc.
                }
                b'0' | b'1' | b'x' | b'X' | b'z' | b'Z' => {
                    let bit = line[0].to_ascii_lowercase();
                    let id_code = trim_ascii(&line[1..]);
                    if let Some(&idx) = code_map.get(id_code) {
                        record_track_bits(&mut tracks[idx], current_time, &[bit]);
                    }
                }
                b'b' | b'B' => {
                    let rest = &line[1..];
                    if let Some(ws_pos) = rest.iter().position(|b| b.is_ascii_whitespace()) {
                        let raw_bits = &rest[..ws_pos];
                        let id_code = trim_ascii(&rest[ws_pos + 1..]);
                        if let Some(&idx) = code_map.get(id_code) {
                            let norm = normalize_bit_slice(raw_bits);
                            record_track_bits(&mut tracks[idx], current_time, norm);
                        }
                    }
                }
                b'r' | b'R' => {
                    let rest = &line[1..];
                    if let Some(ws_pos) = rest.iter().position(|b| b.is_ascii_whitespace()) {
                        let raw_real = &rest[..ws_pos];
                        let id_code = trim_ascii(&rest[ws_pos + 1..]);
                        if let Some(&idx) = code_map.get(id_code) {
                            let tr = &mut tracks[idx];
                            if !tr.has_initial {
                                tr.has_initial = true;
                                tr.initial_bits.extend_from_slice(raw_real);
                                tr.last_bits.extend_from_slice(raw_real);
                                tr.samples.push((
                                    current_time,
                                    String::from_utf8_lossy(raw_real).into_owned(),
                                ));
                            } else if tr.last_bits.as_slice() != raw_real {
                                tr.transitions += 1;
                                tr.last_bits.clear();
                                tr.last_bits.extend_from_slice(raw_real);
                                if tr.samples.len() < 24 {
                                    tr.samples.push((
                                        current_time,
                                        String::from_utf8_lossy(raw_real).into_owned(),
                                    ));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    let total_transitions: u64 = tracks.iter().map(|t| t.transitions).sum();
    let unique_signal_count = tracks.len().max(usize::from(declared_signal_count > 0));

    // Sort signals so architectural / high-activity non-internal ports come first
    let mut summaries: Vec<VcdSignalSummary> = tracks
        .into_iter()
        .map(|t| {
            let init_hex = if t.initial_bits.contains(&b'.') {
                String::from_utf8_lossy(&t.initial_bits).into_owned()
            } else {
                vcd_bits_to_hex(&t.initial_bits)
            };
            let last_hex = if t.last_bits.contains(&b'.') {
                String::from_utf8_lossy(&t.last_bits).into_owned()
            } else {
                vcd_bits_to_hex(&t.last_bits)
            };
            VcdSignalSummary {
                name: t.primary_name,
                scope: t.primary_scope,
                width: t.width,
                transitions: t.transitions,
                initial_value_hex: init_hex,
                last_value_hex: last_hex,
                samples: t.samples,
            }
        })
        .collect();

    summaries.sort_by(|a, b| {
        let a_internal = a.name.starts_with("w_");
        let b_internal = b.name.starts_with("w_");
        a_internal
            .cmp(&b_internal)
            .then_with(|| b.transitions.cmp(&a.transitions))
            .then_with(|| a.name.cmp(&b.name))
    });

    // Keep top 24 signals in JSON payload so multi-hundred-wire netlists remain compact
    summaries.truncate(24);

    let waveform_svg = if include_svg && !summaries.is_empty() {
        Some(render_vcd_waveform_svg(
            &summaries,
            start_time,
            end_time,
            timescale.as_deref().unwrap_or("1ps"),
        ))
    } else {
        None
    };

    Ok(AppVcdDigest {
        present: true,
        build_status: "built".to_string(),
        rel_path,
        size_bytes,
        version,
        timescale,
        timestamp_count,
        start_time,
        end_time,
        signal_count: unique_signal_count,
        total_transitions,
        signals: summaries,
        waveform_svg,
    })
}

#[inline]
fn trim_ascii(bytes: &[u8]) -> &[u8] {
    let start = bytes
        .iter()
        .position(|b| !b.is_ascii_whitespace())
        .unwrap_or(bytes.len());
    let end = bytes
        .iter()
        .rposition(|b| !b.is_ascii_whitespace())
        .map(|i| i + 1)
        .unwrap_or(start);
    &bytes[start..end]
}

#[inline]
fn normalize_bit_slice(raw: &[u8]) -> &[u8] {
    if raw.is_empty() {
        return b"0";
    }
    let pos = raw.iter().position(|&b| b != b'0').unwrap_or(raw.len() - 1);
    &raw[pos..]
}

#[inline]
fn parse_u64_ascii(bytes: &[u8]) -> Option<u64> {
    if bytes.is_empty() {
        return None;
    }
    let mut val = 0u64;
    for &b in bytes {
        if !b.is_ascii_digit() {
            break;
        }
        val = val.saturating_mul(10).saturating_add((b - b'0') as u64);
    }
    Some(val)
}

#[inline]
fn record_track_bits(tr: &mut VcdCodeTrack, current_time: u64, norm_bits: &[u8]) {
    if !tr.has_initial {
        tr.has_initial = true;
        tr.initial_bits.extend_from_slice(norm_bits);
        tr.last_bits.extend_from_slice(norm_bits);
        tr.samples.push((current_time, vcd_bits_to_hex(norm_bits)));
    } else if tr.last_bits.as_slice() != norm_bits {
        tr.transitions += 1;
        tr.last_bits.clear();
        tr.last_bits.extend_from_slice(norm_bits);
        if tr.samples.len() < 24 {
            tr.samples.push((current_time, vcd_bits_to_hex(norm_bits)));
        }
    }
}

/// Render an interactive dark-theme SVG digital waveform diagram from extracted `.vcd` signal samples.
pub fn render_vcd_waveform_svg(
    signals: &[VcdSignalSummary],
    start_time: u64,
    end_time: u64,
    timescale: &str,
) -> String {
    let rows: Vec<&VcdSignalSummary> = signals.iter().take(8).collect();
    let row_h = 34usize;
    let top_pad = 34usize;
    let height = top_pad + rows.len() * row_h + 16;
    let width = 880usize;
    let label_x = 12usize;
    let wave_x0 = 230.0f64;
    let wave_x1 = 856.0f64;
    let wave_w = wave_x1 - wave_x0;

    // Focus the horizontal time axis on the sampled window so dense multi-thousand-cycle VCDs stay legible
    let max_sample_t = rows
        .iter()
        .flat_map(|s| s.samples.iter().map(|&(t, _)| t))
        .max()
        .unwrap_or(end_time);
    let view_end = if max_sample_t > start_time {
        max_sample_t.saturating_add(((max_sample_t - start_time) / 8).max(2))
    } else {
        end_time.max(start_time + 10)
    };
    let span = (view_end.saturating_sub(start_time)).max(1) as f64;

    let mut svg = String::with_capacity(4096);
    let _ = write!(
        &mut svg,
        r##"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" width="{width}" height="{height}" data-projection="vcd-waveform-digest">"##
    );
    let _ = write!(
        &mut svg,
        r##"<rect x="0" y="0" width="{width}" height="{height}" rx="8" fill="#070b12" stroke="#1e293b"/>"##
    );
    let _ = write!(
        &mut svg,
        r##"<text x="{label_x}" y="21" fill="#94a3b8" font-family="monospace" font-size="11">VCD LOGIC ANALYZER (timescale: {ts} | window: #{t0}..#{t1} | full end: #{tend})</text>"##,
        ts = xml_escape(timescale),
        t0 = start_time,
        t1 = view_end,
        tend = end_time
    );

    // Vertical grid ticks
    for tick in 0..=4 {
        let gx = wave_x0 + (tick as f64 / 4.0) * wave_w;
        let gt = start_time + ((tick as f64 / 4.0) * span).round() as u64;
        let _ = write!(
            &mut svg,
            r##"<line x1="{gx:.1}" y1="28" x2="{gx:.1}" y2="{h}" stroke="#162032" stroke-dasharray="3,3"/>"##,
            h = height - 8
        );
        let _ = write!(
            &mut svg,
            r##"<text x="{gx:.1}" y="21" fill="#64748b" font-family="monospace" font-size="9.5" text-anchor="end">#{gt}</text>"##
        );
    }

    for (r_idx, sig) in rows.iter().enumerate() {
        let y_top = (top_pad + r_idx * row_h) as f64;
        let y_hi = y_top + 6.0;
        let y_mid = y_top + 15.0;
        let y_lo = y_top + 24.0;

        let short_name = if sig.name.len() > 20 {
            format!("{}…", &sig.name[..19])
        } else {
            sig.name.clone()
        };
        let _ = write!(
            &mut svg,
            r##"<text x="{label_x}" y="{yt:.1}" fill="#e2e8f0" font-family="monospace" font-size="11">{name}[{w}]</text>"##,
            yt = y_mid + 3.0,
            name = xml_escape(&short_name),
            w = sig.width
        );
        let _ = write!(
            &mut svg,
            r##"<text x="220" y="{yt:.1}" fill="#38bdf8" font-family="monospace" font-size="9.5" text-anchor="end">{tr}Δ</text>"##,
            yt = y_mid + 3.0,
            tr = sig.transitions
        );

        if sig.samples.is_empty() {
            continue;
        }

        if sig.width == 1 {
            let mut path_d = String::new();
            for (s_idx, &(t, ref val)) in sig.samples.iter().enumerate() {
                let x = (wave_x0 + ((t.saturating_sub(start_time)) as f64 / span) * wave_w)
                    .clamp(wave_x0, wave_x1);
                let y = if val == "0x1" || val == "1" {
                    y_hi
                } else {
                    y_lo
                };
                if s_idx == 0 {
                    let _ = write!(&mut path_d, "M {wave_x0:.1} {y:.1} L {x:.1} {y:.1}");
                } else {
                    let prev_y = if sig.samples[s_idx - 1].1 == "0x1"
                        || sig.samples[s_idx - 1].1 == "1"
                    {
                        y_hi
                    } else {
                        y_lo
                    };
                    let _ = write!(&mut path_d, " L {x:.1} {prev_y:.1} L {x:.1} {y:.1}");
                }
                if s_idx + 1 == sig.samples.len() {
                    let _ = write!(&mut path_d, " L {wave_x1:.1} {y:.1}");
                }
            }
            let _ = write!(
                &mut svg,
                r##"<path d="{path_d}" fill="none" stroke="#4ade80" stroke-width="1.6"/>"##
            );
        } else {
            // Multi-bit bus envelope boxes
            for (s_idx, &(t, ref val)) in sig.samples.iter().enumerate() {
                let x0 = (wave_x0 + ((t.saturating_sub(start_time)) as f64 / span) * wave_w)
                    .clamp(wave_x0, wave_x1);
                let next_t = sig
                    .samples
                    .get(s_idx + 1)
                    .map(|&(nt, _)| nt)
                    .unwrap_or(view_end);
                let x1 = (wave_x0 + ((next_t.saturating_sub(start_time)) as f64 / span) * wave_w)
                    .clamp(x0 + 2.0, wave_x1);
                let box_w = (x1 - x0).max(2.0);
                let stroke = if val == "0x0" { "#334155" } else { "#38bdf8" };
                let fill = if val == "0x0" {
                    "#0f172a"
                } else {
                    "rgba(56,189,248,0.13)"
                };
                let _ = write!(
                    &mut svg,
                    r##"<rect x="{x0:.1}" y="{y_hi:.1}" width="{box_w:.1}" height="18" rx="3" fill="{fill}" stroke="{stroke}" stroke-width="1"/>"##
                );
                if box_w >= 46.0 {
                    let max_chars = ((box_w - 8.0) / 6.2) as usize;
                    let disp = if val.len() > max_chars && max_chars > 3 {
                        format!("{}…", &val[..max_chars - 1])
                    } else {
                        val.clone()
                    };
                    let _ = write!(
                        &mut svg,
                        r##"<text x="{tx:.1}" y="{ty:.1}" fill="#bae6fd" font-family="monospace" font-size="9.5">{disp}</text>"##,
                        tx = x0 + 4.0,
                        ty = y_mid + 3.0,
                        disp = xml_escape(&disp)
                    );
                }
            }
        }
    }

    svg.push_str("</svg>");
    svg
}

fn xml_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Parse binary or ASCII `.stl` mesh bytes into `StlArtifactStats`.
pub fn parse_stl_bytes(rel_path: String, bytes: &[u8]) -> StlArtifactStats {
    let size_bytes = bytes.len() as u64;
    if bytes.len() >= 84 {
        let tri_count = u32::from_le_bytes([bytes[80], bytes[81], bytes[82], bytes[83]]);
        let expected_len = 84u64.saturating_add((tri_count as u64).saturating_mul(50));
        let looks_ascii = bytes.starts_with(b"solid ") && expected_len != size_bytes;

        if !looks_ascii {
            let header_end = bytes[..80]
                .iter()
                .position(|&b| b == 0)
                .unwrap_or(80);
            let header_text = String::from_utf8_lossy(&bytes[..header_end])
                .trim()
                .to_string();

            let mut min_v = [f32::INFINITY; 3];
            let mut max_v = [f32::NEG_INFINITY; 3];
            let max_tris = ((bytes.len() - 84) / 50).min(tri_count as usize);
            for i in 0..max_tris {
                let base = 84 + i * 50 + 12; // skip 12-byte normal vector
                for v_idx in 0..3 {
                    for axis in 0..3 {
                        let off = base + v_idx * 12 + axis * 4;
                        let val = f32::from_le_bytes([
                            bytes[off],
                            bytes[off + 1],
                            bytes[off + 2],
                            bytes[off + 3],
                        ]);
                        if val.is_finite() {
                            if val < min_v[axis] {
                                min_v[axis] = val;
                            }
                            if val > max_v[axis] {
                                max_v[axis] = val;
                            }
                        }
                    }
                }
            }
            if max_tris == 0 || !min_v[0].is_finite() {
                min_v = [0.0; 3];
                max_v = [0.0; 3];
            }

            return StlArtifactStats {
                rel_path,
                size_bytes,
                format: "binary".to_string(),
                header_text,
                triangle_count: tri_count,
                binary_size_consistent: expected_len == size_bytes,
                bbox_min: min_v,
                bbox_max: max_v,
            };
        }
    }

    // Fallback: ASCII STL or truncated header
    let text = String::from_utf8_lossy(bytes);
    let mut tri_count = 0u32;
    let mut min_v = [f32::INFINITY; 3];
    let mut max_v = [f32::NEG_INFINITY; 3];
    let first_line = text.lines().next().unwrap_or("").trim().to_string();

    for line in text.lines() {
        let t = line.trim();
        if t.starts_with("facet normal") {
            tri_count = tri_count.saturating_add(1);
        } else if let Some(rest) = t.strip_prefix("vertex ") {
            let mut coords = rest.split_whitespace();
            if let (Some(xs), Some(ys), Some(zs)) = (coords.next(), coords.next(), coords.next()) {
                if let (Ok(x), Ok(y), Ok(z)) =
                    (xs.parse::<f32>(), ys.parse::<f32>(), zs.parse::<f32>())
                {
                    for (axis, val) in [(0, x), (1, y), (2, z)] {
                        if val.is_finite() {
                            min_v[axis] = min_v[axis].min(val);
                            max_v[axis] = max_v[axis].max(val);
                        }
                    }
                }
            }
        }
    }
    if !min_v[0].is_finite() {
        min_v = [0.0; 3];
        max_v = [0.0; 3];
    }

    StlArtifactStats {
        rel_path,
        size_bytes,
        format: if text.trim_start().starts_with("solid") {
            "ascii".to_string()
        } else {
            "truncated".to_string()
        },
        header_text: first_line,
        triangle_count: tri_count,
        binary_size_consistent: false,
        bbox_min: min_v,
        bbox_max: max_v,
    }
}

/// Parse 5-axis `.ngc` G-code toolpath text into `NgcArtifactStats`.
pub fn parse_ngc_text(rel_path: String, size_bytes: u64, text: &str) -> NgcArtifactStats {
    let mut line_count = 0usize;
    let mut rapid_g00_moves = 0usize;
    let mut linear_g01_moves = 0usize;
    let mut no_gouge_verified_points = 0usize;
    let mut min_tool_sdf: Option<i64> = None;
    let mut max_tool_sdf: Option<i64> = None;
    let mut spindle_rpm: Option<u32> = None;
    let mut preview_lines = Vec::new();

    for line in text.lines() {
        line_count += 1;
        let t = line.trim();
        if preview_lines.len() < 12 && !t.is_empty() {
            preview_lines.push(t.to_string());
        }
        if t.starts_with("G00 ") || t.starts_with("G0 ") {
            rapid_g00_moves += 1;
        } else if t.starts_with("G01 ") || t.starts_with("G1 ") {
            linear_g01_moves += 1;
        }
        if t.contains("NO_GOUGE=1") {
            no_gouge_verified_points += 1;
        }
        if let Some(pos) = t.find("TOOL_SDF=") {
            let after = &t[pos + "TOOL_SDF=".len()..];
            let num_s: String = after
                .chars()
                .take_while(|c| c.is_ascii_digit() || *c == '-')
                .collect();
            if let Ok(sdf) = num_s.parse::<i64>() {
                min_tool_sdf = Some(min_tool_sdf.map_or(sdf, |m| m.min(sdf)));
                max_tool_sdf = Some(max_tool_sdf.map_or(sdf, |m| m.max(sdf)));
            }
        }
        if spindle_rpm.is_none() && t.starts_with('S') && t.contains("M03") {
            let digits: String = t[1..].chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(rpm) = digits.parse::<u32>() {
                spindle_rpm = Some(rpm);
            }
        }
    }

    NgcArtifactStats {
        rel_path,
        size_bytes,
        line_count,
        rapid_g00_moves,
        linear_g01_moves,
        no_gouge_verified_points,
        min_tool_sdf,
        max_tool_sdf,
        spindle_rpm,
        preview_lines,
    }
}

// ============================================================================
// Houyhnhnm Ch. 7 Multi-Projection Cards (CAE / PCB / FEEC / PDE / 6DOF / ZK)
// ============================================================================

/// Read-only verified proof badge attached to a projection card (`scrub_readOnly_refused`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifiedProofBadge {
    pub badge_field: String,
    pub judge_format: String,
    pub verified: bool,
    pub commitment_hex: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PcbMultiphysicsDfmCard {
    pub cell_key: String,
    pub trace_width_um: u64,
    pub clearance_um: u64,
    pub copper_weight_oz: u64,
    /// Read-only computed characteristic impedance (Ohms)
    pub impedance_ohm: u64,
    /// Read-only computed TEMPEST shielding margin (dB)
    pub tempest_margin_db: u64,
    pub drc_badge: VerifiedProofBadge,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FeecSimplicialFemCard {
    pub cell_key: String,
    pub polynomial_order: u64,
    pub mesh_refinement: u64,
    /// Read-only Prager-Synge hypercircle duality gap (ppm)
    pub prager_synge_gap_ppm: u64,
    /// Read-only simplicial cohomology Betti invariant `beta_1`
    pub cohomology_betti_1: u64,
    pub feec_badge: VerifiedProofBadge,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PdeConservationCard {
    pub cell_key: String,
    pub cfl_milli: u64,
    pub grid_cells: u64,
    /// Read-only discrete Lax-Friedrichs entropy residual (ppb)
    pub entropy_residual_ppb: u64,
    pub hyperbolic_badge: VerifiedProofBadge,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Vehicle6DofTrajectoryCard {
    pub cell_key: String,
    pub thrust_n: u64,
    pub mass_kg: u64,
    pub horizon_steps: u64,
    /// Read-only Lie-group SE(3) symplectic energy drift (ppm)
    pub energy_drift_ppm: u64,
    pub se3_badge: VerifiedProofBadge,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZkCustodyReceiptCard {
    pub cell_key: String,
    pub epoch_limit: u64,
    pub threshold_k: u64,
    pub merkle_root_hex: String,
    pub custody_badge: VerifiedProofBadge,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrustumRedactedViewCard {
    pub cell_key: String,
    pub viewer_clearance: String,
    pub max_depth: u64,
    pub redacted_cell_count: usize,
    pub visible_cell_count: usize,
    pub commitment_badge: VerifiedProofBadge,
}

/// First-class Houyhnhnm multi-projection workbook card supporting bidirectional parameter
/// scrubbing ("No Dead Pixels") while protecting read-only verified proof badges.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionCard {
    PcbMultiphysicsDfm(PcbMultiphysicsDfmCard),
    FeecSimplicialFem(FeecSimplicialFemCard),
    PdeConservation(PdeConservationCard),
    Vehicle6DofTrajectory(Vehicle6DofTrajectoryCard),
    ZkCustodyReceipt(ZkCustodyReceiptCard),
    FrustumRedactedView(FrustumRedactedViewCard),
}

impl ProjectionCard {
    pub fn kind_label(&self) -> &'static str {
        match self {
            Self::PcbMultiphysicsDfm(_) => "pcbMultiphysicsDfm",
            Self::FeecSimplicialFem(_) => "feecSimplicialFem",
            Self::PdeConservation(_) => "pdeConservation",
            Self::Vehicle6DofTrajectory(_) => "vehicle6DofTrajectory",
            Self::ZkCustodyReceipt(_) => "zkCustodyReceipt",
            Self::FrustumRedactedView(_) => "frustumRedactedView",
        }
    }

    pub fn judge_format(&self) -> &str {
        match self {
            Self::PcbMultiphysicsDfm(c) => &c.drc_badge.judge_format,
            Self::FeecSimplicialFem(c) => &c.feec_badge.judge_format,
            Self::PdeConservation(c) => &c.hyperbolic_badge.judge_format,
            Self::Vehicle6DofTrajectory(c) => &c.se3_badge.judge_format,
            Self::ZkCustodyReceipt(c) => &c.custody_badge.judge_format,
            Self::FrustumRedactedView(c) => &c.commitment_badge.judge_format,
        }
    }

    /// Scrub a numeric parameter in-place, updating derived display readouts while deterministically
    /// refusing any edit to read-only verified proof badges (`scrub_readOnly_refused`).
    pub fn scrub_field(&mut self, field_name: &str, new_val: u64) -> Result<(), String> {
        if field_name == "receiptBadge" {
            return Err("Refused scrub on read-only field 'receiptBadge'".to_string());
        }
        match self {
            Self::PcbMultiphysicsDfm(c) => match field_name {
                "drcVerified" | "impedanceOhm" | "tempestMarginDb" => {
                    Err(format!("Refused scrub on read-only badge field '{field_name}'"))
                }
                "traceWidthUm" => {
                    c.trace_width_um = new_val.max(1);
                    c.impedance_ohm = (8_500 / c.trace_width_um.max(25)).clamp(25, 120);
                    Ok(())
                }
                "clearanceUm" => {
                    c.clearance_um = new_val;
                    c.tempest_margin_db = 40 + (c.clearance_um / 20);
                    Ok(())
                }
                "copperWeightOz" => {
                    c.copper_weight_oz = new_val.max(1);
                    Ok(())
                }
                other => Err(format!("Unknown PCB projection field '{other}'")),
            },
            Self::FeecSimplicialFem(c) => match field_name {
                "pragerSyngeGap" | "cohomologyBetti" => {
                    Err(format!("Refused scrub on read-only badge field '{field_name}'"))
                }
                "polynomialOrder" => {
                    c.polynomial_order = new_val.max(1);
                    c.prager_synge_gap_ppm = 1_000 / (c.polynomial_order * c.mesh_refinement.max(1));
                    Ok(())
                }
                "meshRefinement" => {
                    c.mesh_refinement = new_val.max(1);
                    c.prager_synge_gap_ppm = 1_000 / (c.polynomial_order.max(1) * c.mesh_refinement);
                    Ok(())
                }
                other => Err(format!("Unknown FEEC projection field '{other}'")),
            },
            Self::PdeConservation(c) => match field_name {
                "entropyResidual" | "hyperbolicCert" => {
                    Err(format!("Refused scrub on read-only badge field '{field_name}'"))
                }
                "cflMilli" => {
                    c.cfl_milli = new_val;
                    c.hyperbolic_badge.verified = new_val <= 1_000;
                    Ok(())
                }
                "gridCells" => {
                    c.grid_cells = new_val.max(1);
                    Ok(())
                }
                other => Err(format!("Unknown PDE projection field '{other}'")),
            },
            Self::Vehicle6DofTrajectory(c) => match field_name {
                "se3SymplecticCert" | "energyDriftPpm" => {
                    Err(format!("Refused scrub on read-only badge field '{field_name}'"))
                }
                "thrustN" => {
                    c.thrust_n = new_val;
                    Ok(())
                }
                "massKg" => {
                    c.mass_kg = new_val.max(1);
                    Ok(())
                }
                "horizonSteps" => {
                    c.horizon_steps = new_val.max(1);
                    Ok(())
                }
                other => Err(format!("Unknown 6DOF trajectory projection field '{other}'")),
            },
            Self::ZkCustodyReceipt(c) => match field_name {
                "merkleRoot" | "custodyProof" => {
                    Err(format!("Refused scrub on read-only badge field '{field_name}'"))
                }
                "epochLimit" => {
                    c.epoch_limit = new_val;
                    Ok(())
                }
                "thresholdK" => {
                    c.threshold_k = new_val.max(1);
                    Ok(())
                }
                other => Err(format!("Unknown ZK custody projection field '{other}'")),
            },
            Self::FrustumRedactedView(c) => match field_name {
                "commitmentRoot" | "redactionProof" => {
                    Err(format!("Refused scrub on read-only badge field '{field_name}'"))
                }
                "maxDepth" => {
                    c.max_depth = new_val;
                    Ok(())
                }
                other => Err(format!("Unknown frustum redaction projection field '{other}'")),
            },
        }
    }

    /// Render a compact SVG status card summarizing scrubbable sliders and verified kernel badges.
    pub fn render_svg_card(&self) -> String {
        let kind = self.kind_label();
        let fmt = self.judge_format();
        let detail = match self {
            Self::PcbMultiphysicsDfm(c) => format!(
                "trace={}um clearance={}um Z0={}ohm TEMPEST={}dB verified={}",
                c.trace_width_um,
                c.clearance_um,
                c.impedance_ohm,
                c.tempest_margin_db,
                c.drc_badge.verified
            ),
            Self::FeecSimplicialFem(c) => format!(
                "order=p{} mesh={} gap={}ppm betti1={} verified={}",
                c.polynomial_order,
                c.mesh_refinement,
                c.prager_synge_gap_ppm,
                c.cohomology_betti_1,
                c.feec_badge.verified
            ),
            Self::PdeConservation(c) => format!(
                "CFL=0.{:03} cells={} residual={}ppb verified={}",
                c.cfl_milli,
                c.grid_cells,
                c.entropy_residual_ppb,
                c.hyperbolic_badge.verified
            ),
            Self::Vehicle6DofTrajectory(c) => format!(
                "thrust={}N mass={}kg steps={} drift={}ppm verified={}",
                c.thrust_n, c.mass_kg, c.horizon_steps, c.energy_drift_ppm, c.se3_badge.verified
            ),
            Self::ZkCustodyReceipt(c) => format!(
                "epochLimit={} threshold={} root={} verified={}",
                c.epoch_limit,
                c.threshold_k,
                &c.merkle_root_hex[..c.merkle_root_hex.len().min(12)],
                c.custody_badge.verified
            ),
            Self::FrustumRedactedView(c) => format!(
                "clearance={} depth={} visible={} redacted={} verified={}",
                c.viewer_clearance,
                c.max_depth,
                c.visible_cell_count,
                c.redacted_cell_count,
                c.commitment_badge.verified
            ),
        };
        format!(
            "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"72\" data-kind=\"{kind}\" data-judge=\"{fmt}\"><rect width=\"520\" height=\"72\" rx=\"6\" fill=\"#111827\"/><text x=\"12\" y=\"26\" fill=\"#e5e7eb\">{kind} [{fmt}]</text><text x=\"12\" y=\"52\" fill=\"#93c5fd\">{detail}</text></svg>"
        )
    }
}
