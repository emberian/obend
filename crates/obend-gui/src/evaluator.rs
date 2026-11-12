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

    for chunk in padded.chunks_exact(64) {
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
        serde_json::from_slice(&resp_bytes).map_err(|e| {
            ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string())
        })
    }

    /// Drive the Lean kernel's Putnam/Foster lens scrubber (`obend_workbook_scrub_cell_json`).
    pub fn scrub_kernel_cell_json(&mut self, req: &Value) -> Result<Value, ObendError> {
        let payload = serde_json::to_vec(req).map_err(|e| {
            ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string())
        })?;
        let resp_bytes = self.session.scrub_projection_cell(&payload)?;
        serde_json::from_slice(&resp_bytes).map_err(|e| {
            ObendError::WithDetail(Box::new(ObendError::DecodeFailed), e.to_string())
        })
    }

    fn compute_section_transitive_digest(
        &self,
        owner: &str,
        visiting: &mut HashSet<String>,
    ) -> [u8; 32] {
        if !visiting.insert(owner.to_string()) {
            return sha256_bytes(format!("cycle::{owner}").as_bytes());
        }
        let mut buf = Vec::new();
        if let Some(md) = self.sections.get(owner) {
            buf.extend_from_slice(b"sec:present:");
            buf.extend_from_slice(&(owner.len() as u64).to_be_bytes());
            buf.extend_from_slice(owner.as_bytes());
            buf.extend_from_slice(&(md.len() as u64).to_be_bytes());
            buf.extend_from_slice(md.as_bytes());
            for cited in extract_wikilink_owners(md) {
                let child = self.compute_section_transitive_digest(&cited, visiting);
                buf.extend_from_slice(&child);
            }
        } else {
            buf.extend_from_slice(b"sec:missing:");
            buf.extend_from_slice(&(owner.len() as u64).to_be_bytes());
            buf.extend_from_slice(owner.as_bytes());
        }
        visiting.remove(owner);
        sha256_bytes(&buf)
    }

    /// Execute a `.obnb` cell slice incrementally over `Backlinks ∪ CellDeps`:
    /// - Rejects dependency cycles and self-citations fail-closed (`ObendError::EvalFailed`).
    /// - Recomputes **only** cells in the dirty cone whose 256-bit effective input/dependency
    ///   digest changed, reusing clean cells' cached `ElaborationSummary` and 256-bit digests.
    pub fn execute_workbook_incremental(
        &mut self,
        cells: &[NotebookCell],
    ) -> WorkbookExecutionReport {
        let mut id_to_idx: HashMap<String, usize> = HashMap::new();
        let mut mod_to_id: HashMap<String, String> = HashMap::new();
        for (idx, cell) in cells.iter().enumerate() {
            id_to_idx.insert(cell.id.clone(), idx);
            if let Some(mname) = extract_declared_module_name(&cell.source) {
                mod_to_id.insert(mname, cell.id.clone());
            }
        }

        let mut direct_cell_deps: Vec<Vec<usize>> = vec![Vec::new(); cells.len()];
        let mut cell_section_cites: Vec<Vec<String>> = vec![Vec::new(); cells.len()];
        let mut has_self_or_forward_cycle: Vec<bool> = vec![false; cells.len()];

        for (idx, cell) in cells.iter().enumerate() {
            let (mut raw_deps, cites) = extract_cell_dependencies(&cell.source, &mod_to_id);
            for owner in &cites {
                if id_to_idx.contains_key(owner) && !raw_deps.iter().any(|x| x == owner) {
                    raw_deps.push(owner.clone());
                }
            }
            for dep_id in &raw_deps {
                if dep_id == &cell.id {
                    has_self_or_forward_cycle[idx] = true;
                } else if let Some(&dep_idx) = id_to_idx.get(dep_id) {
                    direct_cell_deps[idx].push(dep_idx);
                }
            }
            cell_section_cites[idx] = cites;
        }

        // Topological sort (Kahn's algorithm) to evaluate upstream producers before downstream readers
        // and detect any cycle in `CellDeps ∪ CellWikilinks`.
        let n = cells.len();
        let mut indegree = vec![0usize; n];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];
        for u in 0..n {
            for &p in &direct_cell_deps[u] {
                dependents[p].push(u);
                indegree[u] += 1;
            }
        }
        let mut queue: std::collections::VecDeque<usize> = (0..n)
            .filter(|&i| indegree[i] == 0 && !has_self_or_forward_cycle[i])
            .collect();
        let mut topo_order: Vec<usize> = Vec::with_capacity(n);
        while let Some(u) = queue.pop_front() {
            topo_order.push(u);
            for &v in &dependents[u] {
                indegree[v] -= 1;
                if indegree[v] == 0 && !has_self_or_forward_cycle[v] {
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
                if !id_to_idx.contains_key(sec_owner) {
                    let mut vis = HashSet::new();
                    let sec_d = self.compute_section_transitive_digest(sec_owner, &mut vis);
                    hasher_input.extend_from_slice(b"cite:");
                    hasher_input.extend_from_slice(&sec_d);
                }
            }

            let digest = sha256_bytes(&hasher_input);
            effective_digests[idx] = digest;

            let is_clean = self
                .cache
                .get(&cell.id)
                .map_or(false, |entry| entry.input_digest == digest);

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
            if !in_topo[idx] {
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
    /// Attempts to scrub a read-only proof badge fail closed (`ObendError::TurnRefused`).
    pub fn scrub_cell_parameter(
        &mut self,
        cells: &mut [NotebookCell],
        cell_id: &str,
        field_name: &str,
        new_value: u64,
    ) -> Result<WorkbookExecutionReport, ObendError> {
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

/// Update `# @param <field_name>=...` in place or append a canonical parameter pin comment.
pub fn rewrite_obend_parameter(source: &str, field_name: &str, new_value: u64) -> String {
    let marker_prefix = format!("# @param {field_name}=");
    let mut replaced = false;
    let mut updated_lines: Vec<String> = source
        .lines()
        .map(|line| {
            if line.trim().starts_with(&marker_prefix) {
                replaced = true;
                format!("# @param {field_name}={new_value}")
            } else {
                line.to_string()
            }
        })
        .collect();
    if !replaced {
        updated_lines.push(format!("# @param {field_name}={new_value}"));
    }
    updated_lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
