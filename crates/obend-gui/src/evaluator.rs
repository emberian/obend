//! PIDE `ObendSession` elaboration, dependency-aware incremental dirty-cone `.obnb` workbook
//! execution, bidirectional parameter scrubbing, claim/law inspection, and law affordance client
//! backed by the Lean `Obend.FFI.Bridge` kernel library.

use obend_ffi::error::ObendError;
use obend_ffi::session::ObendSession;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

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

/// Report of a dependency-aware incremental `.obnb` workbook execution pass.
#[derive(Debug, Clone)]
pub struct WorkbookExecutionReport {
    pub dirty_cone: Vec<String>,
    pub clean_reused: Vec<String>,
    pub cell_digests: BTreeMap<String, [u8; 32]>,
    pub cell_digest_hex: BTreeMap<String, String>,
    pub results: Vec<(String, Result<ElaborationSummary, ObendError>)>,
}

#[derive(Debug, Clone)]
struct CachedCellEntry {
    input_digest: [u8; 32],
    digest_hex: String,
    outcome: Result<ElaborationSummary, ObendError>,
    eval_count: usize,
}

#[derive(Debug, Clone)]
struct CellLensState {
    kind: String,
    scrubbable_params: BTreeMap<String, u64>,
    readonly_badges: BTreeSet<String>,
}

/// Pure FIPS 180-4 SHA-256 digest (`[u8; 32]`, full 256-bit carrier).
pub fn sha256_bytes(data: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(data.len() + 72);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.as_chunks::<64>().0 {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[i * 4],
                chunk[i * 4 + 1],
                chunk[i * 4 + 2],
                chunk[i * 4 + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (idx, word) in h.iter().enumerate() {
        out[idx * 4..idx * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

pub fn hex_encode_32(digest: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in digest {
        let _ = write!(&mut s, "{b:02x}");
    }
    s
}

/// Extract `[[wikilink]]` and `![[embed#Heading]]` / `![[embed#^block]]` owner keys from text.
pub fn extract_wikilink_owners(text: &str) -> Vec<String> {
    let mut owners = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0usize;
    while i + 3 < bytes.len() {
        if bytes[i] == b'[' && bytes[i + 1] == b'[' {
            let start = i + 2;
            let mut end = start;
            while end + 1 < bytes.len()
                && !(bytes[end] == b']' && bytes[end + 1] == b']')
                && bytes[end] != b'\n'
            {
                end += 1;
            }
            if end + 1 < bytes.len() && bytes[end] == b']' && bytes[end + 1] == b']' {
                if let Ok(inner) = std::str::from_utf8(&bytes[start..end]) {
                    let before_alias = inner.split('|').next().unwrap_or("").trim();
                    let owner = before_alias.split('#').next().unwrap_or("").trim();
                    if !owner.is_empty() && !owners.iter().any(|x| x == owner) {
                        owners.push(owner.to_string());
                    }
                }
                i = end + 2;
                continue;
            }
        }
        i += 1;
    }
    owners
}

/// Extract upstream cell/module/section references declared in a cell's `.obend` source or comments:
/// - `# @depends: id1, id2`
/// - `import ./ModName.obend`
/// - `[[Owner]]` / `![[Owner#Heading]]` / `![[Owner#^block]]`
fn extract_cell_dependencies(
    source: &str,
    module_to_cell_id: &HashMap<String, String>,
) -> (Vec<String>, Vec<String>) {
    let mut cell_deps: Vec<String> = Vec::new();
    let mut cite_owners = extract_wikilink_owners(source);

    for line in source.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("# @depends:") {
            for item in rest.split(',') {
                let dep = item.trim();
                if !dep.is_empty() && !cell_deps.iter().any(|x| x == dep) {
                    cell_deps.push(dep.to_string());
                }
            }
        } else if let Some(rest) = t.strip_prefix("import ") {
            let path_tok = rest.split_whitespace().next().unwrap_or("").trim();
            if let Some(mod_stem) = path_tok
                .strip_prefix("./")
                .and_then(|s| s.strip_suffix(".obend"))
            {
                if let Some(cid) = module_to_cell_id.get(mod_stem) {
                    if !cell_deps.iter().any(|x| x == cid) {
                        cell_deps.push(cid.clone());
                    }
                }
            }
        }
    }

    // Any wikilink owner matching a cell ID is also treated as a direct cell dependency
    for owner in &cite_owners {
        if !cell_deps.iter().any(|x| x == owner) {
            // Checked against known cell IDs by caller
        }
    }
    cite_owners.dedup();
    (cell_deps, cite_owners)
}

fn extract_declared_module_name(source: &str) -> Option<String> {
    for line in source.lines() {
        if let Some(rest) = line.trim().strip_prefix("# @module:") {
            let name = rest.trim();
            if !name.is_empty() {
                return Some(name.to_string());
            }
        }
    }
    None
}

fn default_readonly_badges_for_kind(kind: &str) -> BTreeSet<String> {
    let badges: &[&str] = match kind {
        "prose" => &["wordCountBadge", "receiptBadge"],
        "obendCode" => &["typeBadge", "proofBadge", "receiptBadge"],
        "casSymbolic" => &["groebnerCert", "proofBadge", "receiptBadge"],
        "leanBridge" => &["kernelVerified", "proofBadge", "receiptBadge"],
        "lawContract" => &["confluenceDial", "proofBadge", "receiptBadge"],
        "deosAffordance" => &["simplexTier", "proofBadge", "receiptBadge"],
        "hardwareSchematic" => &["cdcClean", "rtlSynthCert", "receiptBadge"],
        "hardwareTiming" => &["wnsPs", "staSignoffCert", "receiptBadge"],
        "hardwareLayout" => &["drcClean", "pnrCert", "receiptBadge"],
        "ledgerSeat" => &["conservationCert", "proofBadge", "receiptBadge"],
        "pdeConservation" => &["entropyResidual", "hyperbolicCert", "receiptBadge"],
        "feecSimplicialFem" => &["pragerSyngeGap", "cohomologyBetti", "receiptBadge"],
        "pcbMultiphysicsDfm" => &[
            "drcVerified",
            "impedanceOhm",
            "tempestMarginDb",
            "receiptBadge",
        ],
        "vehicle6DofTrajectory" => &["se3SymplecticCert", "energyDriftPpm", "receiptBadge"],
        "zkCustodyReceipt" => &["merkleRoot", "custodyProof", "receiptBadge"],
        "frustumRedactedView" => &["commitmentRoot", "redactionProof", "receiptBadge"],
        _ => &["proofBadge", "receiptBadge"],
    };
    badges.iter().map(|s| (*s).to_string()).collect()
}

pub struct NotebookRunner {
    session: ObendSession,
    cache: HashMap<String, CachedCellEntry>,
    sections: BTreeMap<String, String>,
    lenses: HashMap<String, CellLensState>,
}

impl NotebookRunner {
    pub fn new() -> Result<Self, ObendError> {
        Ok(Self {
            session: ObendSession::new()?,
            cache: HashMap::new(),
            sections: BTreeMap::new(),
            lenses: HashMap::new(),
        })
    }

    pub fn session_mut(&mut self) -> &mut ObendSession {
        &mut self.session
    }

    /// Update or insert a literate markdown section (`[[section_key]]` / `![[section_key#Heading]]`).
    /// Downstream cells citing this section directly or transitively will be invalidated on the next run.
    pub fn set_section(&mut self, section_key: &str, markdown: &str) {
        self.sections
            .insert(section_key.to_string(), markdown.to_string());
    }

    /// Number of times `cell_id` has actually invoked the Lean kernel elaborator.
    pub fn cell_eval_count(&self, cell_id: &str) -> usize {
        self.cache.get(cell_id).map_or(0, |c| c.eval_count)
    }

    /// Cached 256-bit SHA-256 effective input/dependency digest for `cell_id`.
    pub fn cell_digest(&self, cell_id: &str) -> Option<[u8; 32]> {
        self.cache.get(cell_id).map(|c| c.input_digest)
    }

    /// Register scrubbable parameters and read-only proof badges for a projection cell.
    pub fn register_cell_lens(
        &mut self,
        cell_id: &str,
        kind: &str,
        scrubbable_params: BTreeMap<String, u64>,
        extra_readonly_badges: &[&str],
    ) {
        let mut readonly_badges = default_readonly_badges_for_kind(kind);
        for b in extra_readonly_badges {
            readonly_badges.insert((*b).to_string());
        }
        self.lenses.insert(
            cell_id.to_string(),
            CellLensState {
                kind: kind.to_string(),
                scrubbable_params,
                readonly_badges,
            },
        );
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

    /// Drive the Lean kernel's unified `WorkbookEngine` (`obend_workbook_step_json`).
    pub fn step_kernel_workbook_json(&mut self, req: &Value) -> Result<Value, ObendError> {
        let payload = serde_json::to_vec(req).map_err(|e| {
            ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string())
        })?;
        let resp_bytes = self.session.step_workbook(&payload)?;
        serde_json::from_slice(&resp_bytes)
            .map_err(|e| ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string()))
    }

    /// Drive the Lean kernel's Putnam/Foster lens scrubber (`obend_workbook_scrub_cell_json`).
    pub fn scrub_kernel_cell_json(&mut self, req: &Value) -> Result<Value, ObendError> {
        let payload = serde_json::to_vec(req).map_err(|e| {
            ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string())
        })?;
        let resp_bytes = self.session.scrub_projection_cell(&payload)?;
        serde_json::from_slice(&resp_bytes)
            .map_err(|e| ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string()))
    }

    /// Compute the memoized transitive 256-bit SHA-256 digest of a literate markdown section
    /// (`O(V + E)` on arbitrary diamond wikilink DAGs; cycle-safe on self/mutual citations).
    pub fn section_transitive_digest(&self, owner: &str) -> [u8; 32] {
        let mut visiting = HashSet::new();
        let mut memo = HashMap::new();
        compute_section_transitive_digest_map(&self.sections, owner, &mut visiting, &mut memo).0
    }

    /// Execute a `.obnb` cell slice incrementally over `Backlinks ∪ CellDeps`:
    /// - Rejects empty or duplicate `cell.id`s, ambiguous duplicate `# @module:` declarations,
    ///   dependency cycles, and self-citations fail-closed (`ObendError::EvalFailed`).
    /// - Recomputes **only** cells in the dirty cone whose 256-bit effective input/dependency
    ///   digest changed, reusing clean cells' cached `ElaborationSummary` and 256-bit digests.
    pub fn execute_workbook_incremental(
        &mut self,
        cells: &[NotebookCell],
    ) -> WorkbookExecutionReport {
        let n = cells.len();
        let mut id_counts: HashMap<&str, usize> = HashMap::with_capacity(n);
        let mut mod_counts: HashMap<String, usize> = HashMap::new();
        let mut declared_mods: Vec<Option<String>> = Vec::with_capacity(n);

        for cell in cells {
            *id_counts.entry(cell.id.as_str()).or_insert(0) += 1;
            let m = extract_declared_module_name(&cell.source);
            if let Some(ref mname) = m {
                *mod_counts.entry(mname.clone()).or_insert(0) += 1;
            }
            declared_mods.push(m);
        }

        let mut invalid_reason: Vec<Option<String>> = vec![None; n];
        let mut id_to_idx: HashMap<String, usize> = HashMap::with_capacity(n);
        let mut mod_to_id: HashMap<String, String> = HashMap::new();

        for (idx, cell) in cells.iter().enumerate() {
            if cell.id.trim().is_empty() {
                invalid_reason[idx] = Some("Workbook cell has empty cell.id (refused)".to_string());
                continue;
            }
            if id_counts.get(cell.id.as_str()).copied().unwrap_or(0) > 1 {
                self.cache.remove(&cell.id);
                invalid_reason[idx] = Some(format!(
                    "Duplicate workbook cell.id '{}' refused (status aliasing forbidden)",
                    cell.id
                ));
                continue;
            }
            if let Some(ref mname) = declared_mods[idx] {
                if mod_counts.get(mname).copied().unwrap_or(0) > 1 {
                    self.cache.remove(&cell.id);
                    invalid_reason[idx] = Some(format!(
                        "Duplicate workbook # @module '{}' on cell '{}' refused",
                        mname, cell.id
                    ));
                    continue;
                }
                mod_to_id.insert(mname.clone(), cell.id.clone());
            }
            id_to_idx.insert(cell.id.clone(), idx);
        }

        let mut direct_cell_deps: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut cell_section_cites: Vec<Vec<String>> = vec![Vec::new(); n];
        let mut has_self_or_forward_cycle: Vec<bool> = vec![false; n];

        for (idx, cell) in cells.iter().enumerate() {
            if invalid_reason[idx].is_some() {
                continue;
            }
            let (mut raw_deps, cites) = extract_cell_dependencies(&cell.source, &mod_to_id);
            // Detect imports targeting a duplicated # @module name
            for line in cell.source.lines() {
                if let Some(rest) = line.trim().strip_prefix("import ") {
                    let path_tok = rest.split_whitespace().next().unwrap_or("").trim();
                    if let Some(mod_stem) = path_tok
                        .strip_prefix("./")
                        .and_then(|s| s.strip_suffix(".obend"))
                    {
                        if mod_counts.get(mod_stem).copied().unwrap_or(0) > 1 {
                            invalid_reason[idx] = Some(format!(
                                "Cell '{}' imports ambiguous duplicated module '{}'",
                                cell.id, mod_stem
                            ));
                        }
                    }
                }
            }
            for owner in &cites {
                if id_counts.contains_key(owner.as_str()) && !raw_deps.iter().any(|x| x == owner) {
                    raw_deps.push(owner.clone());
                }
            }
            for dep_id in &raw_deps {
                if dep_id == &cell.id {
                    has_self_or_forward_cycle[idx] = true;
                } else if id_counts.get(dep_id.as_str()).copied().unwrap_or(0) > 1 {
                    invalid_reason[idx] = Some(format!(
                        "Cell '{}' depends on duplicated cell.id '{}'",
                        cell.id, dep_id
                    ));
                } else if let Some(&dep_idx) = id_to_idx.get(dep_id) {
                    if invalid_reason[dep_idx].is_some() {
                        invalid_reason[idx] = Some(format!(
                            "Cell '{}' depends on invalid upstream cell '{}'",
                            cell.id, dep_id
                        ));
                    } else {
                        direct_cell_deps[idx].push(dep_idx);
                    }
                }
            }
            cell_section_cites[idx] = cites;
        }

        // Topological sort (Kahn's algorithm) to evaluate upstream producers before downstream readers
        // and detect any cycle in `CellDeps ∪ CellWikilinks`.
        let mut indegree = vec![0usize; n];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];
        for u in 0..n {
            if invalid_reason[u].is_some() {
                continue;
            }
            for &p in &direct_cell_deps[u] {
                dependents[p].push(u);
                indegree[u] += 1;
            }
        }
        let mut queue: std::collections::VecDeque<usize> = (0..n)
            .filter(|&i| {
                invalid_reason[i].is_none() && indegree[i] == 0 && !has_self_or_forward_cycle[i]
            })
            .collect();
        let mut topo_order: Vec<usize> = Vec::with_capacity(n);
        while let Some(u) = queue.pop_front() {
            topo_order.push(u);
            for &v in &dependents[u] {
                indegree[v] -= 1;
                if indegree[v] == 0 && invalid_reason[v].is_none() && !has_self_or_forward_cycle[v]
                {
                    queue.push_back(v);
                }
            }
        }

        let mut in_topo = vec![false; n];
        for &idx in &topo_order {
            in_topo[idx] = true;
        }

        let mut effective_digests: Vec<[u8; 32]> = vec![[0u8; 32]; n];
        let mut dirty_cone = Vec::new();
        let mut clean_reused = Vec::new();
        let mut section_memo: HashMap<String, [u8; 32]> = HashMap::new();

        for &idx in &topo_order {
            let cell = &cells[idx];
            let mut hasher_input = Vec::new();
            hasher_input.extend_from_slice(b"obend.cell.v1:");
            hasher_input.extend_from_slice(cell.id.as_bytes());
            hasher_input.push(b':');
            hasher_input.extend_from_slice(cell.kind.as_bytes());
            hasher_input.push(0);
            hasher_input.extend_from_slice(cell.source.as_bytes());
            hasher_input.push(0);

            if let Some(lens) = self.lenses.get(&cell.id) {
                for (k, v) in &lens.scrubbable_params {
                    hasher_input.extend_from_slice(&(k.len() as u64).to_be_bytes());
                    hasher_input.extend_from_slice(k.as_bytes());
                    hasher_input.extend_from_slice(&v.to_be_bytes());
                }
            }
            for &dep_idx in &direct_cell_deps[idx] {
                hasher_input.extend_from_slice(b"dep:");
                hasher_input.extend_from_slice(&effective_digests[dep_idx]);
            }
            for sec_owner in &cell_section_cites[idx] {
                if !id_counts.contains_key(sec_owner.as_str()) {
                    let mut vis = HashSet::new();
                    let sec_d = compute_section_transitive_digest_map(
                        &self.sections,
                        sec_owner,
                        &mut vis,
                        &mut section_memo,
                    )
                    .0;
                    hasher_input.extend_from_slice(b"cite:");
                    hasher_input.extend_from_slice(&sec_d);
                }
            }

            let digest = sha256_bytes(&hasher_input);
            effective_digests[idx] = digest;

            let is_clean = self
                .cache
                .get(&cell.id)
                .is_some_and(|entry| entry.input_digest == digest);

            if is_clean {
                clean_reused.push(cell.id.clone());
            } else {
                dirty_cone.push(cell.id.clone());
                let prev_count = self.cell_eval_count(&cell.id);
                let outcome = self.elaborate_obend(&cell.source);
                self.cache.insert(
                    cell.id.clone(),
                    CachedCellEntry {
                        input_digest: digest,
                        digest_hex: hex_encode_32(&digest),
                        outcome,
                        eval_count: prev_count + 1,
                    },
                );
            }
        }

        let mut cell_digests = BTreeMap::new();
        let mut cell_digest_hex = BTreeMap::new();
        let mut results = Vec::with_capacity(n);

        for (idx, cell) in cells.iter().enumerate() {
            if let Some(ref reason) = invalid_reason[idx] {
                dirty_cone.push(cell.id.clone());
                let inv_err = Err(ObendError::WithDetail(
                    Box::new(ObendError::EvalFailed),
                    reason.clone(),
                ));
                let inv_digest = sha256_bytes(format!("invalid::{idx}::{}", cell.id).as_bytes());
                cell_digests.insert(cell.id.clone(), inv_digest);
                cell_digest_hex.insert(cell.id.clone(), hex_encode_32(&inv_digest));
                results.push((cell.id.clone(), inv_err));
            } else if !in_topo[idx] {
                dirty_cone.push(cell.id.clone());
                let cyc_err = Err(ObendError::WithDetail(
                    Box::new(ObendError::EvalFailed),
                    format!(
                        "Workbook DAG cycle or self-citation refused at cell '{}'",
                        cell.id
                    ),
                ));
                let cyc_digest = sha256_bytes(format!("cyclic::{}", cell.id).as_bytes());
                cell_digests.insert(cell.id.clone(), cyc_digest);
                cell_digest_hex.insert(cell.id.clone(), hex_encode_32(&cyc_digest));
                results.push((cell.id.clone(), cyc_err));
            } else {
                let entry = self.cache.get(&cell.id).expect("cached in topo sweep");
                cell_digests.insert(cell.id.clone(), entry.input_digest);
                cell_digest_hex.insert(cell.id.clone(), entry.digest_hex.clone());
                results.push((cell.id.clone(), entry.outcome.clone()));
            }
        }

        WorkbookExecutionReport {
            dirty_cone,
            clean_reused,
            cell_digests,
            cell_digest_hex,
            results,
        }
    }

    /// Scrub a bidirectional parameter on `cell_id` ("No Dead Pixels"), updating its `.obend` source
    /// binding and recomputing **only** the reachable downstream dirty cone.
    /// Attempts to scrub a read-only proof badge or duplicate-ID workbook fail closed.
    pub fn scrub_cell_parameter(
        &mut self,
        cells: &mut [NotebookCell],
        cell_id: &str,
        field_name: &str,
        new_value: u64,
    ) -> Result<WorkbookExecutionReport, ObendError> {
        validate_workbook_cells(cells)?;

        let cell_pos = cells.iter().position(|c| c.id == cell_id).ok_or_else(|| {
            ObendError::WithDetail(
                Box::new(ObendError::EvalFailed),
                format!("Unknown cell '{cell_id}'"),
            )
        })?;
        let kind = cells[cell_pos].kind.clone();
        let badges = self
            .lenses
            .get(cell_id)
            .map(|l| l.readonly_badges.clone())
            .unwrap_or_else(|| default_readonly_badges_for_kind(&kind));

        if badges.contains(field_name) {
            return Err(ObendError::WithDetail(
                Box::new(ObendError::TurnRefused),
                format!("Refused scrub on read-only verified proof badge '{field_name}'"),
            ));
        }

        let lens = self.lenses.get_mut(cell_id).ok_or_else(|| {
            ObendError::WithDetail(
                Box::new(ObendError::EvalFailed),
                format!("Cell '{cell_id}' has no registered projection lens"),
            )
        })?;
        if !lens.scrubbable_params.contains_key(field_name) {
            return Err(ObendError::WithDetail(
                Box::new(ObendError::EvalFailed),
                format!(
                    "Unknown scrubbable parameter '{field_name}' on {} cell '{cell_id}'",
                    lens.kind
                ),
            ));
        }
        lens.scrubbable_params
            .insert(field_name.to_string(), new_value);

        cells[cell_pos].source =
            rewrite_obend_parameter(&cells[cell_pos].source, field_name, new_value);

        Ok(self.execute_workbook_incremental(cells))
    }

    /// Execute a sequence of notebook cells using dependency-aware dirty-cone caching,
    /// returning structured elaboration reports per cell ID.
    pub fn execute_cells(
        &mut self,
        cells: &[NotebookCell],
    ) -> Vec<(String, Result<ElaborationSummary, ObendError>)> {
        self.execute_workbook_incremental(cells).results
    }
}

/// Validate that every `NotebookCell` has a non-empty, unique `id`.
pub fn validate_workbook_cells(cells: &[NotebookCell]) -> Result<(), ObendError> {
    let mut seen = HashSet::with_capacity(cells.len());
    for cell in cells {
        if cell.id.trim().is_empty() {
            return Err(ObendError::WithDetail(
                Box::new(ObendError::EvalFailed),
                "Workbook cell has empty cell.id".to_string(),
            ));
        }
        if !seen.insert(cell.id.as_str()) {
            return Err(ObendError::WithDetail(
                Box::new(ObendError::EvalFailed),
                format!("Duplicate workbook cell.id '{}' refused", cell.id),
            ));
        }
    }
    Ok(())
}

fn compute_section_transitive_digest_map(
    sections: &BTreeMap<String, String>,
    owner: &str,
    visiting: &mut HashSet<String>,
    memo: &mut HashMap<String, [u8; 32]>,
) -> ([u8; 32], bool) {
    if visiting.contains(owner) {
        return (sha256_bytes(format!("cycle::{owner}").as_bytes()), true);
    }
    if let Some(&cached) = memo.get(owner) {
        return (cached, false);
    }

    visiting.insert(owner.to_string());
    let mut depended_on_active = false;
    let mut buf = Vec::new();
    if let Some(md) = sections.get(owner) {
        buf.extend_from_slice(b"sec:present:");
        buf.extend_from_slice(&(owner.len() as u64).to_be_bytes());
        buf.extend_from_slice(owner.as_bytes());
        buf.extend_from_slice(&(md.len() as u64).to_be_bytes());
        buf.extend_from_slice(md.as_bytes());
        for cited in extract_wikilink_owners(md) {
            let (child, child_active) =
                compute_section_transitive_digest_map(sections, &cited, visiting, memo);
            depended_on_active |= child_active;
            buf.extend_from_slice(&child);
        }
    } else {
        buf.extend_from_slice(b"sec:missing:");
        buf.extend_from_slice(&(owner.len() as u64).to_be_bytes());
        buf.extend_from_slice(owner.as_bytes());
    }
    visiting.remove(owner);

    let digest = sha256_bytes(&buf);
    if !depended_on_active {
        memo.insert(owner.to_string(), digest);
    }
    (digest, depended_on_active)
}

fn is_valid_obend_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn is_ident_boundary_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn split_code_and_comment(line: &str) -> (&str, &str) {
    let bytes = line.as_bytes();
    let mut i = 0;
    let mut in_str = false;
    let mut escaped = false;
    while i < bytes.len() {
        if escaped {
            escaped = false;
            i += 1;
            continue;
        }
        if in_str && bytes[i] == b'\\' {
            escaped = true;
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_str = !in_str;
            i += 1;
            continue;
        }
        if !in_str {
            if bytes[i] == b'#' {
                return (&line[..i], &line[i..]);
            }
            if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
                return (&line[..i], &line[i..]);
            }
        }
        i += 1;
    }
    (line, "")
}

fn rewrite_numeric_rhs(rhs_raw: &str, new_value: u64) -> Option<String> {
    let lead_len = rhs_raw.len() - rhs_raw.trim_start().len();
    let lead = &rhs_raw[..lead_len];
    let trimmed_end = rhs_raw[lead_len..].trim_end();
    let trail = &rhs_raw[lead_len + trimmed_end.len()..];

    let (core, semi) = if let Some(stripped) = trimmed_end.strip_suffix(';') {
        (stripped.trim_end(), ";")
    } else {
        (trimmed_end, "")
    };
    if core.is_empty() {
        return None;
    }
    let (digits_part, nat_suffix) = if let Some(d) = core.strip_suffix('n') {
        (d, "n")
    } else {
        (core, "")
    };
    let digits_clean = digits_part.strip_prefix('-').unwrap_or(digits_part);
    if digits_clean.is_empty() || !digits_clean.chars().all(|c| c.is_ascii_digit() || c == '_') {
        return None;
    }
    if !digits_clean.chars().any(|c| c.is_ascii_digit()) {
        return None;
    }
    Some(format!("{lead}{new_value}{nat_suffix}{semi}{trail}"))
}

enum LineRewriteOutcome {
    Unchanged,
    Replaced(String),
    MatchNextIndentedBody(String),
}

fn try_rewrite_executable_line(line: &str, field_name: &str, new_value: u64) -> LineRewriteOutcome {
    if field_name.is_empty() {
        return LineRewriteOutcome::Unchanged;
    }
    let trimmed_all = line.trim();
    if trimmed_all.is_empty() || trimmed_all.starts_with('#') || trimmed_all.starts_with("--") {
        return LineRewriteOutcome::Unchanged;
    }
    let (code_part, comment_part) = split_code_and_comment(line);
    let indent_len = code_part.len() - code_part.trim_start().len();
    let indent = &code_part[..indent_len];
    let code = code_part.trim_start();

    // 1. Check `let <field_name> ...`, `def <field_name> ...`, or `<field_name> := / = ...`
    let (kw_prefix, after_kw) = if let Some(rest) = code.strip_prefix("let ") {
        let ws = rest.len() - rest.trim_start().len();
        (&code[..4 + ws], rest.trim_start())
    } else if let Some(rest) = code.strip_prefix("def ") {
        let ws = rest.len() - rest.trim_start().len();
        (&code[..4 + ws], rest.trim_start())
    } else if let Some(rest) = code.strip_prefix("pub def ") {
        let ws = rest.len() - rest.trim_start().len();
        (&code[..8 + ws], rest.trim_start())
    } else {
        ("", code)
    };

    if let Some(after_ident) = after_kw.strip_prefix(field_name) {
        let boundary_ok = after_ident
            .chars()
            .next()
            .is_none_or(|c| !is_ident_boundary_char(c));
        if boundary_ok {
            // Check `def <field_name>() -> <Type>:` (ObjectiveBend zero-arg def)
            let trimmed_after = after_ident.trim_start();
            if kw_prefix.contains("def") && trimmed_after.starts_with("()") {
                if let Some(colon_pos) = after_ident.rfind(':') {
                    let after_colon = &after_ident[colon_pos + 1..];
                    if after_colon.trim().is_empty() {
                        return LineRewriteOutcome::MatchNextIndentedBody(line.to_string());
                    }
                    if let Some(new_rhs) = rewrite_numeric_rhs(after_colon, new_value) {
                        return LineRewriteOutcome::Replaced(format!(
                            "{indent}{kw_prefix}{field_name}{}{new_rhs}{comment_part}",
                            &after_ident[..=colon_pos]
                        ));
                    }
                }
            }

            // Check `:=` or `=` assignment (excluding `==`, `!=`, `<=`, `>=`)
            if let Some(walrus_idx) = after_ident.find(":=") {
                let lhs_tail = &after_ident[..walrus_idx + 2];
                let rhs = &after_ident[walrus_idx + 2..];
                if let Some(new_rhs) = rewrite_numeric_rhs(rhs, new_value) {
                    return LineRewriteOutcome::Replaced(format!(
                        "{indent}{kw_prefix}{field_name}{lhs_tail}{new_rhs}{comment_part}"
                    ));
                }
            } else {
                let bytes = after_ident.as_bytes();
                for idx in 0..bytes.len() {
                    if bytes[idx] == b'=' {
                        let prev = if idx > 0 { bytes[idx - 1] } else { b' ' };
                        let next = if idx + 1 < bytes.len() {
                            bytes[idx + 1]
                        } else {
                            b' '
                        };
                        if prev != b'='
                            && prev != b'!'
                            && prev != b'<'
                            && prev != b'>'
                            && prev != b':'
                            && next != b'='
                            && next != b'>'
                        {
                            let lhs_tail = &after_ident[..=idx];
                            let rhs = &after_ident[idx + 1..];
                            if let Some(new_rhs) = rewrite_numeric_rhs(rhs, new_value) {
                                return LineRewriteOutcome::Replaced(format!(
                                    "{indent}{kw_prefix}{field_name}{lhs_tail}{new_rhs}{comment_part}"
                                ));
                            }
                            break;
                        }
                    }
                }
            }
        }
    }

    // 2. Check record field literal `{..., <field_name>: <digits>[n], ...}`
    let mut quoted = false;
    let mut escaped = false;
    let outside: Vec<bool> = code_part
        .bytes()
        .map(|b| {
            let visible = !quoted && b != b'"';
            if escaped {
                escaped = false;
            } else if quoted && b == b'\\' {
                escaped = true;
            } else if b == b'"' {
                quoted = !quoted;
            }
            visible
        })
        .collect();
    if code_part
        .bytes()
        .enumerate()
        .any(|(i, b)| b == b'{' && outside[i])
        && code_part
            .bytes()
            .enumerate()
            .any(|(i, b)| b == b'}' && outside[i])
    {
        let mut out = String::with_capacity(code_part.len() + 8);
        let mut cursor = 0usize;
        let mut changed = false;
        while let Some(rel) = code_part[cursor..].find(field_name) {
            let start = cursor + rel;
            let end = start + field_name.len();
            let prev_ok = start == 0
                || !code_part[..start]
                    .chars()
                    .next_back()
                    .is_some_and(is_ident_boundary_char);
            let rest = &code_part[end..];
            let rest_ws = rest.len() - rest.trim_start().len();
            let after_ws = &rest[rest_ws..];
            if outside[start] && prev_ok && after_ws.starts_with(':') && !after_ws.starts_with(":=")
            {
                let val_region = &after_ws[1..];
                let delim_pos = val_region.find([',', '}']).unwrap_or(val_region.len());
                let candidate = &val_region[..delim_pos];
                if let Some(new_val) = rewrite_numeric_rhs(candidate, new_value) {
                    out.push_str(&code_part[cursor..end + rest_ws + 1]);
                    out.push_str(&new_val);
                    cursor = end + rest_ws + 1 + delim_pos;
                    changed = true;
                    continue;
                }
            }
            out.push_str(&code_part[cursor..end]);
            cursor = end;
        }
        if changed {
            out.push_str(&code_part[cursor..]);
            out.push_str(comment_part);
            return LineRewriteOutcome::Replaced(out);
        }
    }

    LineRewriteOutcome::Unchanged
}

/// Rewrite executable `.obend` bindings (`k := v`, `let k = v`, `def k = v`,
/// `def k() -> Nat:\n  vn`, `{..., k: vn, ...}`) AND `# @param <field_name>=...` in place.
/// For `ObjectiveBend` modules that carried only `# @param` without a live binding, emits an
/// executable `def <field_name>() -> Nat:` binding so kernel elaboration reflects scrubbed values.
pub fn rewrite_obend_parameter(source: &str, field_name: &str, new_value: u64) -> String {
    if field_name.is_empty() {
        return source.to_string();
    }
    let marker_prefix = format!("# @param {field_name}=");
    let mut replaced_marker = false;
    let mut replaced_binding = false;
    let mut pending_def_body = false;
    let is_objective_bend = source
        .lines()
        .any(|l| l.trim().starts_with("edition ObjectiveBend"));

    let mut updated_lines: Vec<String> = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with(&marker_prefix) {
            replaced_marker = true;
            updated_lines.push(format!("# @param {field_name}={new_value}"));
            continue;
        }

        if pending_def_body
            && !trimmed.is_empty()
            && !trimmed.starts_with('#')
            && !trimmed.starts_with("--")
        {
            pending_def_body = false;
            let (code_part, comment_part) = split_code_and_comment(line);
            if let Some(rewritten) = rewrite_numeric_rhs(code_part, new_value) {
                replaced_binding = true;
                updated_lines.push(format!("{rewritten}{comment_part}"));
                continue;
            }
        }

        match try_rewrite_executable_line(line, field_name, new_value) {
            LineRewriteOutcome::Unchanged => updated_lines.push(line.to_string()),
            LineRewriteOutcome::Replaced(new_line) => {
                replaced_binding = true;
                updated_lines.push(new_line);
            }
            LineRewriteOutcome::MatchNextIndentedBody(hdr_line) => {
                pending_def_body = true;
                updated_lines.push(hdr_line);
            }
        }
    }

    if !replaced_marker {
        updated_lines.push(format!("# @param {field_name}={new_value}"));
    }
    if !replaced_binding && is_objective_bend && is_valid_obend_ident(field_name) {
        updated_lines.push(format!("def {field_name}() -> Nat:"));
        updated_lines.push(format!("  {new_value}n"));
    }

    updated_lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn parameter_rewrite_ignores_empty_names_and_strings() {
        let source = r#"let label = "{traceWidthUm: 150n}""#;
        assert_eq!(rewrite_obend_parameter(source, "", 9), source);
        assert!(matches!(
            try_rewrite_executable_line(source, "traceWidthUm", 9),
            LineRewriteOutcome::Unchanged
        ));
        let mixed = r#"let x = {label: "\\\"{traceWidthUm: 150n}", traceWidthUm: 200n}"#;
        let updated = rewrite_obend_parameter(mixed, "traceWidthUm", 9);
        assert!(updated.contains("traceWidthUm: 150n"));
        assert!(updated.contains("traceWidthUm: 9n"));
    }

    #[test]
    fn test_rewrite_obend_parameter_idempotent_put_put() {
        let src = "module M\n# @param traceWidthUm=120\ndef x = 1\n";
        let once = rewrite_obend_parameter(src, "traceWidthUm", 160);
        assert!(once.contains("# @param traceWidthUm=160"));
        assert!(!once.contains("# @param traceWidthUm=120"));
        assert!(once.contains("def x = 1"));
        let twice = rewrite_obend_parameter(&once, "traceWidthUm", 200);
        assert_eq!(twice.matches("# @param traceWidthUm=").count(), 1);
        assert!(twice.contains("# @param traceWidthUm=200"));
    }

    #[test]
    fn test_rewrite_obend_parameter_rewrites_executable_bindings() {
        // 1. `k := v` and `let k = v` and `def k = v`
        let src_assign = "traceWidthUm := 120\nlet clearanceUm = 80\ndef layers : Nat := 4n\ntraceWidthUmOther := 999\n";
        let r1 = rewrite_obend_parameter(src_assign, "traceWidthUm", 175);
        assert!(r1.contains("traceWidthUm := 175\n"));
        assert!(r1.contains("traceWidthUmOther := 999\n"));

        let r2 = rewrite_obend_parameter(&r1, "clearanceUm", 95);
        assert!(r2.contains("let clearanceUm = 95\n"));

        let r3 = rewrite_obend_parameter(&r2, "layers", 6);
        assert!(r3.contains("def layers : Nat := 6n\n"));

        // 2. ObjectiveBend multiline `def k() -> Nat:\n  150n` + record literal `{k: 150n}`
        let src_ob = "edition ObjectiveBend 1\ndef traceWidthUm() -> Nat:\n  150n\ndef rec() -> Board:\n  {traceWidthUm: 150n, other: 7n}\n";
        let rob1 = rewrite_obend_parameter(src_ob, "traceWidthUm", 240);
        assert!(rob1.contains("def traceWidthUm() -> Nat:\n  240n\n"));
        assert!(rob1.contains("{traceWidthUm: 240n, other: 7n}"));
        assert_eq!(rob1.matches("def traceWidthUm()").count(), 1);

        // 3. Legacy `# @param`-only ObjectiveBend cell gains executable `def` idempotently
        let legacy_ob =
            "edition ObjectiveBend 1\n# @param traceWidthUm=150\ndef unrelated() -> Nat:\n  1n\n";
        let promoted_1 = rewrite_obend_parameter(legacy_ob, "traceWidthUm", 220);
        assert!(promoted_1.contains("def traceWidthUm() -> Nat:\n  220n\n"));
        let promoted_2 = rewrite_obend_parameter(&promoted_1, "traceWidthUm", 310);
        assert!(promoted_2.contains("def traceWidthUm() -> Nat:\n  310n\n"));
        assert_eq!(promoted_2.matches("def traceWidthUm()").count(), 1);
    }

    #[test]
    fn test_diamond_dag_30_layers_memoized_linear_time() {
        // 30-layer diamond DAG: L0 -> {A1, B1} -> L1 -> {A2, B2} -> ... -> L30
        // Unmemoized tree traversal visits L30 2^30 = 1,073,741,824 times and hangs;
        // memoized `compute_section_transitive_digest_map` visits each of the 91 nodes once.
        let mut sections = BTreeMap::new();
        sections.insert("L30".to_string(), "Leaf payload v1".to_string());
        for d in (0..30).rev() {
            let next = format!("L{}", d + 1);
            let left = format!("A{}", d + 1);
            let right = format!("B{}", d + 1);
            sections.insert(left.clone(), format!("Left hop {d} -> [[{next}]]"));
            sections.insert(right.clone(), format!("Right hop {d} -> ![[{next}#sec]]"));
            sections.insert(
                format!("L{d}"),
                format!("Diamond layer {d}: [[{left}]] and [[{right}]]"),
            );
        }

        let start = Instant::now();
        let mut vis = HashSet::new();
        let mut memo = HashMap::new();
        let (d1, cyc1) =
            compute_section_transitive_digest_map(&sections, "L0", &mut vis, &mut memo);
        let elapsed = start.elapsed();
        assert!(!cyc1);
        assert_eq!(memo.len(), 91);
        assert!(
            elapsed.as_millis() < 250,
            "30-layer diamond DAG must finish in milliseconds, took {elapsed:?}"
        );

        // Mutating the bottom leaf L30 propagates through all 30 diamond layers deterministically
        sections.insert("L30".to_string(), "Leaf payload v2".to_string());
        let mut vis2 = HashSet::new();
        let mut memo2 = HashMap::new();
        let (d2, cyc2) =
            compute_section_transitive_digest_map(&sections, "L0", &mut vis2, &mut memo2);
        assert!(!cyc2);
        assert_ne!(d1, d2);
    }

    #[test]
    fn test_validate_workbook_cells_rejects_duplicate_and_empty_ids() {
        let ok_cells = vec![
            NotebookCell {
                id: "c1".to_string(),
                kind: "obendCode".to_string(),
                source: String::new(),
                status: "ready".to_string(),
            },
            NotebookCell {
                id: "c2".to_string(),
                kind: "obendCode".to_string(),
                source: String::new(),
                status: "ready".to_string(),
            },
        ];
        assert!(validate_workbook_cells(&ok_cells).is_ok());

        let dup_cells = vec![
            NotebookCell {
                id: "dup".to_string(),
                kind: "obendCode".to_string(),
                source: "invalid".to_string(),
                status: "ready".to_string(),
            },
            NotebookCell {
                id: "dup".to_string(),
                kind: "obendCode".to_string(),
                source: "edition ObjectiveBend 1\ndef x() -> Nat:\n  1n\n".to_string(),
                status: "ready".to_string(),
            },
        ];
        assert!(validate_workbook_cells(&dup_cells).is_err());

        let empty_id_cells = vec![NotebookCell {
            id: "   ".to_string(),
            kind: "obendCode".to_string(),
            source: String::new(),
            status: "ready".to_string(),
        }];
        assert!(validate_workbook_cells(&empty_id_cells).is_err());

        if obend_ffi::kernel_is_native() {
            let mut runner = NotebookRunner::new().expect("init NotebookRunner");
            let report = runner.execute_workbook_incremental(&dup_cells);
            assert_eq!(report.results.len(), 2);
            assert!(
                report.results[0].1.is_err(),
                "failing cell must never inherit passing duplicate cell's status"
            );
            assert!(
                report.results[1].1.is_err(),
                "duplicated cell.id must be refused fail-closed"
            );
            assert_eq!(runner.cell_eval_count("dup"), 0);

            // Live scrub must change kernel elaboration sha256 (not just strip comments!)
            let mut p = BTreeMap::new();
            p.insert("traceW".to_string(), 150);
            runner.register_cell_lens("c_live", "pcbMultiphysicsDfm", p, &[]);
            let mut live_cells = vec![NotebookCell {
                id: "c_live".to_string(),
                kind: "pcbMultiphysicsDfm".to_string(),
                source: "edition ObjectiveBend 1\ndef traceW() -> Nat:\n  150n\n".to_string(),
                status: "ready".to_string(),
            }];
            let rep_before = runner.execute_workbook_incremental(&live_cells);
            let sha_before = rep_before.results[0]
                .1
                .as_ref()
                .expect("before elaborates")
                .sha256
                .clone();
            let rep_after = runner
                .scrub_cell_parameter(&mut live_cells, "c_live", "traceW", 275)
                .expect("scrub traceW");
            let sha_after = rep_after.results[0]
                .1
                .as_ref()
                .expect("after elaborates")
                .sha256
                .clone();
            assert_ne!(
                sha_before, sha_after,
                "parameter scrub must update executable .obend AST and kernel elaboration sha256"
            );
        }
    }
}
