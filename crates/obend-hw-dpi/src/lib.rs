#![forbid(unsafe_code)]
//! Isolated pure-Rust length-framed binary DPI RPC engine mirroring
//! `Obend.Hardware.OspcSignalFabric` and the 4-tile OSPC hardware prover
//! (`Obend.Hardware.OspcProver`).
//!
//! Wire invariants (byte-for-byte identical to `lean/Obend/Hardware/OspcSignalFabric.lean`):
//! - Domain separator: `"OBEND.OSPC.HW.DPI/v1"`
//! - Header (12 bytes): `[0x4F, 0x44, 0x50, 0x49]` (`"ODPI"`), version `0x01`,
//!   `ClockDomain` tag (`0x00` proverCore, `0x01` hostDpi, `0x02` fabricCfg),
//!   msg kind (`0x01` StepCycleReq, `0x81` StepCycleResp), flags (`rst` bit for req, `0` for resp),
//!   big-endian `u32` payload length (`78` for req, `75` for resp).
//! - Total canonical frame sizes: `90` bytes (`OspcDpiReq`), `87` bytes (`OspcDpiResp`).
//! - Zero `unsafe`, zero network dependencies, strict canonical bit-width validation.

use std::io::{self, Read, Write};

/// Domain separator mirrored from `Obend.Hardware.OspcSignalFabric.OSPC_HW_DPI_DOMAIN`.
pub const OSPC_HW_DPI_DOMAIN: &str = "OBEND.OSPC.HW.DPI/v1";

/// Canonical 4-byte magic `"ODPI"`.
pub const ODPI_MAGIC: [u8; 4] = [0x4F, 0x44, 0x50, 0x49];
/// Canonical protocol version `1`.
pub const ODPI_VERSION: u8 = 0x01;
/// Message kind for `StepCycleReq`.
pub const ODPI_KIND_STEP_REQ: u8 = 0x01;
/// Message kind for `StepCycleResp`.
pub const ODPI_KIND_STEP_RESP: u8 = 0x81;

/// Fixed envelope and payload sizes (bytes).
pub const ODPI_HEADER_LEN: usize = 12;
pub const ODPI_REQ_PAYLOAD_LEN: usize = 78;
pub const ODPI_RESP_PAYLOAD_LEN: usize = 75;
pub const ODPI_REQ_FRAME_LEN: usize = ODPI_HEADER_LEN + ODPI_REQ_PAYLOAD_LEN;
pub const ODPI_RESP_FRAME_LEN: usize = ODPI_HEADER_LEN + ODPI_RESP_PAYLOAD_LEN;

/// Clock domain wire tags mirroring `Obend.Hardware.OspcSignalFabric.ClockDomain`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClockDomain {
    ProverCore,
    HostDpi,
    FabricCfg,
}

impl ClockDomain {
    pub const fn to_tag(self) -> u8 {
        match self {
            ClockDomain::ProverCore => 0x00,
            ClockDomain::HostDpi => 0x01,
            ClockDomain::FabricCfg => 0x02,
        }
    }

    pub const fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0x00 => Some(ClockDomain::ProverCore),
            0x01 => Some(ClockDomain::HostDpi),
            0x02 => Some(ClockDomain::FabricCfg),
            _ => None,
        }
    }
}

/// Refusal clauses mirroring `Obend.Hardware.OspcSignalFabric.OspcDpiError`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OspcDpiError {
    BadMagic,
    BadVersion,
    BadDomainTag,
    BadMsgKind,
    BadFlags,
    LengthMismatch,
    NonCanonicalField,
    DomainViolation,
    SequenceMismatch,
    DeltaNetLinearityViolation,
}

/// Host-to-hardware isolated DPI request mirroring `OspcDpiReq`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OspcDpiReq {
    pub domain: ClockDomain,
    pub seq_no: u32,
    pub rst: bool,
    // Tile 0 (`tile0_exprcam_face4`)
    pub tile0_op_sel: u8,     // 2 bits (< 4)
    pub tile0_in_lo64: u64,   // 64 bits
    pub tile0_in_hi17: u32,   // 17 bits (< 2^17)
    pub tile0_cam_we: u8,     // 1 bit (< 2)
    pub tile0_cam_addr: u8,   // 8 bits
    pub tile0_cam_wdata: u64, // 64 bits
    pub tile0_cam_qtag: u64,  // 64 bits
    // Tile 1 (`tile1_discrtree_lut`)
    pub tile1_step_en: u8,     // 1 bit (< 2)
    pub tile1_sym_tag: u8,     // 6 bits (< 64)
    pub tile1_lut_we: u8,      // 1 bit (< 2)
    pub tile1_lut_waddr: u16,  // 12 bits (< 4096)
    pub tile1_lut_wdata: u64,  // 64 bits
    // Tile 2 (`tile2_deltanet_redex`)
    pub tile2_redex_en: u8,    // 1 bit (< 2)
    pub tile2_peer_word: u64,  // 64 bits
    pub tile2_port_we: u8,     // 1 bit (< 2)
    pub tile2_port_addr: u8,   // 8 bits
    pub tile2_port_wdata: u64, // 64 bits
    // Tile 3 (`tile3_stream_lrat`)
    pub tile3_step_en: u8,       // 1 bit (< 2)
    pub tile3_clause_we: u8,     // 1 bit (< 2)
    pub tile3_clause_addr: u8,   // 8 bits
    pub tile3_clause_wdata: u64, // 64 bits
}

/// Hardware-to-host isolated DPI response mirroring `OspcDpiResp`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OspcDpiResp {
    pub domain: ClockDomain,
    pub seq_no: u32,
    pub cycle_count: u32,
    pub tile0_face_lo64: u64,
    pub tile0_face_hi17: u32, // 17 bits (< 2^17)
    pub tile0_entails: u8,    // 1 bit
    pub tile0_cam_hit: u8,    // 1 bit
    pub tile1_trie_state: u8, // 6 bits (< 64)
    pub tile1_logup_hits: u32,
    pub tile1_hit_valid: u8,  // 1 bit
    pub tile2_redex_valid: u8, // 1 bit
    pub tile2_redex_count: u32,
    pub tile2_linear_ok: u8,  // 1 bit
    pub tile3_conflict: u8,   // 1 bit
    pub tile3_assign_pos: u32,
    pub tile3_assign_neg: u32,
    pub receipt_limb0: u64,
    pub receipt_limb1: u64,
    pub receipt_limb2: u64,
    pub receipt_limb3: u64,
}

fn check_canonical_req(req: &OspcDpiReq) -> Result<(), OspcDpiError> {
    if req.tile0_op_sel >= 4
        || req.tile0_in_hi17 >= (1 << 17)
        || req.tile0_cam_we >= 2
        || req.tile1_step_en >= 2
        || req.tile1_sym_tag >= 64
        || req.tile1_lut_we >= 2
        || req.tile1_lut_waddr >= 4096
        || req.tile2_redex_en >= 2
        || req.tile2_port_we >= 2
        || req.tile3_step_en >= 2
        || req.tile3_clause_we >= 2
    {
        return Err(OspcDpiError::NonCanonicalField);
    }
    Ok(())
}

fn check_canonical_resp(resp: &OspcDpiResp) -> Result<(), OspcDpiError> {
    if resp.tile0_face_hi17 >= (1 << 17)
        || resp.tile0_entails >= 2
        || resp.tile0_cam_hit >= 2
        || resp.tile1_trie_state >= 64
        || resp.tile1_hit_valid >= 2
        || resp.tile2_redex_valid >= 2
        || resp.tile2_linear_ok >= 2
        || resp.tile3_conflict >= 2
    {
        return Err(OspcDpiError::NonCanonicalField);
    }
    Ok(())
}

/// Encode `OspcDpiReq` into its exact 90-byte canonical big-endian `"ODPI"` v1 frame.
pub fn encode_req(req: &OspcDpiReq) -> Result<Vec<u8>, OspcDpiError> {
    check_canonical_req(req)?;
    let mut out = Vec::with_capacity(ODPI_REQ_FRAME_LEN);
    out.extend_from_slice(&ODPI_MAGIC);
    out.push(ODPI_VERSION);
    out.push(req.domain.to_tag());
    out.push(ODPI_KIND_STEP_REQ);
    out.push(if req.rst { 1 } else { 0 });
    out.extend_from_slice(&(ODPI_REQ_PAYLOAD_LEN as u32).to_be_bytes());
    out.extend_from_slice(&req.seq_no.to_be_bytes());
    out.push(req.tile0_op_sel);
    out.extend_from_slice(&req.tile0_in_lo64.to_be_bytes());
    out.extend_from_slice(&req.tile0_in_hi17.to_be_bytes());
    out.push(req.tile0_cam_we);
    out.push(req.tile0_cam_addr);
    out.extend_from_slice(&req.tile0_cam_wdata.to_be_bytes());
    out.extend_from_slice(&req.tile0_cam_qtag.to_be_bytes());
    out.push(req.tile1_step_en);
    out.push(req.tile1_sym_tag);
    out.push(req.tile1_lut_we);
    out.extend_from_slice(&req.tile1_lut_waddr.to_be_bytes());
    out.extend_from_slice(&req.tile1_lut_wdata.to_be_bytes());
    out.push(req.tile2_redex_en);
    out.extend_from_slice(&req.tile2_peer_word.to_be_bytes());
    out.push(req.tile2_port_we);
    out.push(req.tile2_port_addr);
    out.extend_from_slice(&req.tile2_port_wdata.to_be_bytes());
    out.push(req.tile3_step_en);
    out.push(req.tile3_clause_we);
    out.push(req.tile3_clause_addr);
    out.extend_from_slice(&req.tile3_clause_wdata.to_be_bytes());
    debug_assert_eq!(out.len(), ODPI_REQ_FRAME_LEN);
    Ok(out)
}

fn read_u8(buf: &[u8], off: &mut usize) -> Result<u8, OspcDpiError> {
    if *off >= buf.len() {
        return Err(OspcDpiError::LengthMismatch);
    }
    let v = buf[*off];
    *off += 1;
    Ok(v)
}

fn read_u16_be(buf: &[u8], off: &mut usize) -> Result<u16, OspcDpiError> {
    if *off + 2 > buf.len() {
        return Err(OspcDpiError::LengthMismatch);
    }
    let v = u16::from_be_bytes([buf[*off], buf[*off + 1]]);
    *off += 2;
    Ok(v)
}

fn read_u32_be(buf: &[u8], off: &mut usize) -> Result<u32, OspcDpiError> {
    if *off + 4 > buf.len() {
        return Err(OspcDpiError::LengthMismatch);
    }
    let v = u32::from_be_bytes([buf[*off], buf[*off + 1], buf[*off + 2], buf[*off + 3]]);
    *off += 4;
    Ok(v)
}

fn read_u64_be(buf: &[u8], off: &mut usize) -> Result<u64, OspcDpiError> {
    if *off + 8 > buf.len() {
        return Err(OspcDpiError::LengthMismatch);
    }
    let v = u64::from_be_bytes([
        buf[*off],
        buf[*off + 1],
        buf[*off + 2],
        buf[*off + 3],
        buf[*off + 4],
        buf[*off + 5],
        buf[*off + 6],
        buf[*off + 7],
    ]);
    *off += 8;
    Ok(v)
}

/// Decode an exact-length 90-byte canonical `"ODPI"` v1 `OspcDpiReq` frame.
pub fn decode_req(buf: &[u8]) -> Result<OspcDpiReq, OspcDpiError> {
    if buf.len() < 8 {
        return Err(OspcDpiError::LengthMismatch);
    }
    if buf[0..4] != ODPI_MAGIC {
        return Err(OspcDpiError::BadMagic);
    }
    if buf[4] != ODPI_VERSION {
        return Err(OspcDpiError::BadVersion);
    }
    let domain = ClockDomain::from_tag(buf[5]).ok_or(OspcDpiError::BadDomainTag)?;
    if buf[6] != ODPI_KIND_STEP_REQ {
        return Err(OspcDpiError::BadMsgKind);
    }
    let flags = buf[7];
    if flags != 0 && flags != 1 {
        return Err(OspcDpiError::BadFlags);
    }
    let mut off = 8;
    let payload_len = read_u32_be(buf, &mut off)?;
    if payload_len as usize != ODPI_REQ_PAYLOAD_LEN || buf.len() != ODPI_REQ_FRAME_LEN {
        return Err(OspcDpiError::LengthMismatch);
    }
    let req = OspcDpiReq {
        domain,
        seq_no: read_u32_be(buf, &mut off)?,
        rst: flags == 1,
        tile0_op_sel: read_u8(buf, &mut off)?,
        tile0_in_lo64: read_u64_be(buf, &mut off)?,
        tile0_in_hi17: read_u32_be(buf, &mut off)?,
        tile0_cam_we: read_u8(buf, &mut off)?,
        tile0_cam_addr: read_u8(buf, &mut off)?,
        tile0_cam_wdata: read_u64_be(buf, &mut off)?,
        tile0_cam_qtag: read_u64_be(buf, &mut off)?,
        tile1_step_en: read_u8(buf, &mut off)?,
        tile1_sym_tag: read_u8(buf, &mut off)?,
        tile1_lut_we: read_u8(buf, &mut off)?,
        tile1_lut_waddr: read_u16_be(buf, &mut off)?,
        tile1_lut_wdata: read_u64_be(buf, &mut off)?,
        tile2_redex_en: read_u8(buf, &mut off)?,
        tile2_peer_word: read_u64_be(buf, &mut off)?,
        tile2_port_we: read_u8(buf, &mut off)?,
        tile2_port_addr: read_u8(buf, &mut off)?,
        tile2_port_wdata: read_u64_be(buf, &mut off)?,
        tile3_step_en: read_u8(buf, &mut off)?,
        tile3_clause_we: read_u8(buf, &mut off)?,
        tile3_clause_addr: read_u8(buf, &mut off)?,
        tile3_clause_wdata: read_u64_be(buf, &mut off)?,
    };
    check_canonical_req(&req)?;
    Ok(req)
}

/// Encode `OspcDpiResp` into its exact 87-byte canonical big-endian `"ODPI"` v1 frame.
pub fn encode_resp(resp: &OspcDpiResp) -> Result<Vec<u8>, OspcDpiError> {
    check_canonical_resp(resp)?;
    let mut out = Vec::with_capacity(ODPI_RESP_FRAME_LEN);
    out.extend_from_slice(&ODPI_MAGIC);
    out.push(ODPI_VERSION);
    out.push(resp.domain.to_tag());
    out.push(ODPI_KIND_STEP_RESP);
    out.push(0x00);
    out.extend_from_slice(&(ODPI_RESP_PAYLOAD_LEN as u32).to_be_bytes());
    out.extend_from_slice(&resp.seq_no.to_be_bytes());
    out.extend_from_slice(&resp.cycle_count.to_be_bytes());
    out.extend_from_slice(&resp.tile0_face_lo64.to_be_bytes());
    out.extend_from_slice(&resp.tile0_face_hi17.to_be_bytes());
    out.push(resp.tile0_entails);
    out.push(resp.tile0_cam_hit);
    out.push(resp.tile1_trie_state);
    out.extend_from_slice(&resp.tile1_logup_hits.to_be_bytes());
    out.push(resp.tile1_hit_valid);
    out.push(resp.tile2_redex_valid);
    out.extend_from_slice(&resp.tile2_redex_count.to_be_bytes());
    out.push(resp.tile2_linear_ok);
    out.push(resp.tile3_conflict);
    out.extend_from_slice(&resp.tile3_assign_pos.to_be_bytes());
    out.extend_from_slice(&resp.tile3_assign_neg.to_be_bytes());
    out.extend_from_slice(&resp.receipt_limb0.to_be_bytes());
    out.extend_from_slice(&resp.receipt_limb1.to_be_bytes());
    out.extend_from_slice(&resp.receipt_limb2.to_be_bytes());
    out.extend_from_slice(&resp.receipt_limb3.to_be_bytes());
    debug_assert_eq!(out.len(), ODPI_RESP_FRAME_LEN);
    Ok(out)
}

/// Decode an exact-length 87-byte canonical `"ODPI"` v1 `OspcDpiResp` frame.
pub fn decode_resp(buf: &[u8]) -> Result<OspcDpiResp, OspcDpiError> {
    if buf.len() < 8 {
        return Err(OspcDpiError::LengthMismatch);
    }
    if buf[0..4] != ODPI_MAGIC {
        return Err(OspcDpiError::BadMagic);
    }
    if buf[4] != ODPI_VERSION {
        return Err(OspcDpiError::BadVersion);
    }
    let domain = ClockDomain::from_tag(buf[5]).ok_or(OspcDpiError::BadDomainTag)?;
    if buf[6] != ODPI_KIND_STEP_RESP {
        return Err(OspcDpiError::BadMsgKind);
    }
    if buf[7] != 0 {
        return Err(OspcDpiError::BadFlags);
    }
    let mut off = 8;
    let payload_len = read_u32_be(buf, &mut off)?;
    if payload_len as usize != ODPI_RESP_PAYLOAD_LEN || buf.len() != ODPI_RESP_FRAME_LEN {
        return Err(OspcDpiError::LengthMismatch);
    }
    let resp = OspcDpiResp {
        domain,
        seq_no: read_u32_be(buf, &mut off)?,
        cycle_count: read_u32_be(buf, &mut off)?,
        tile0_face_lo64: read_u64_be(buf, &mut off)?,
        tile0_face_hi17: read_u32_be(buf, &mut off)?,
        tile0_entails: read_u8(buf, &mut off)?,
        tile0_cam_hit: read_u8(buf, &mut off)?,
        tile1_trie_state: read_u8(buf, &mut off)?,
        tile1_logup_hits: read_u32_be(buf, &mut off)?,
        tile1_hit_valid: read_u8(buf, &mut off)?,
        tile2_redex_valid: read_u8(buf, &mut off)?,
        tile2_redex_count: read_u32_be(buf, &mut off)?,
        tile2_linear_ok: read_u8(buf, &mut off)?,
        tile3_conflict: read_u8(buf, &mut off)?,
        tile3_assign_pos: read_u32_be(buf, &mut off)?,
        tile3_assign_neg: read_u32_be(buf, &mut off)?,
        receipt_limb0: read_u64_be(buf, &mut off)?,
        receipt_limb1: read_u64_be(buf, &mut off)?,
        receipt_limb2: read_u64_be(buf, &mut off)?,
        receipt_limb3: read_u64_be(buf, &mut off)?,
    };
    check_canonical_resp(&resp)?;
    Ok(resp)
}

/// Deterministic 4-tile hardware simulator matching `tile0_exprcam_face4`, `tile1_discrtree_lut`,
/// `tile2_deltanet_redex`, and `tile3_stream_lrat` in `Obend.Hardware.OspcProver`.
#[derive(Debug, Clone)]
pub struct Ospc4TileHardwareSim {
    // Tile 0: ExprCAM (256 x 64-bit write-first BRAM) + FaceIdeal4 regs
    pub face_lo64: u64,
    pub face_hi17: u32,
    pub cam_q: u64,
    pub cam_bank: [u64; 256],
    // Tile 1: DiscrTreeLUT (4096 x 64-bit read-first BRAM) + trie_state / logup_hits
    pub trie_state: u8,
    pub logup_hits: u32,
    pub trie_q: u64,
    pub trie_lut: Vec<u64>,
    // Tile 2: DeltaNet port bank (256 x 64-bit write-first BRAM) + redex_count / linear_ok
    pub redex_count: u32,
    pub linear_ok: u8,
    pub port_q: u64,
    pub port_bank: [u64; 256],
    // Tile 3: StreamLRAT clause bank (256 x 64-bit write-first BRAM) + assign_pos/neg/conflict
    pub assign_pos: u32,
    pub assign_neg: u32,
    pub conflict_latched: u8,
    pub clause_q: u64,
    pub clause_bank: [u64; 256],
    // Protocol counters
    pub expected_seq: u32,
    pub cycle_count: u32,
}

impl Default for Ospc4TileHardwareSim {
    fn default() -> Self {
        Self::new()
    }
}

impl Ospc4TileHardwareSim {
    pub fn new() -> Self {
        Self {
            face_lo64: 0,
            face_hi17: 0,
            cam_q: 0,
            cam_bank: [0; 256],
            trie_state: 0,
            logup_hits: 0,
            trie_q: 0,
            trie_lut: vec![0; 4096],
            redex_count: 0,
            linear_ok: 1, // matches `initOspcTiles` tile 2 reg 1 = 1#64
            port_q: 0,
            port_bank: [0; 256],
            assign_pos: 0,
            assign_neg: 0,
            conflict_latched: 0,
            clause_q: 0,
            clause_bank: [0; 256],
            expected_seq: 0,
            cycle_count: 0,
        }
    }

    fn summary_words(&self) -> [u64; 4] {
        [
            self.face_lo64 ^ (self.face_hi17 as u64),
            (self.trie_state as u64) | ((self.logup_hits as u64) << 6),
            (self.redex_count as u64) | ((self.linear_ok as u64) << 32),
            (self.assign_pos as u64) | ((self.assign_neg as u64) << 32),
        ]
    }

    /// Deterministic domain-separated 256-bit state digest over the 4 tile summary words
    /// and cycle counter (tagged with `OSPC_HW_DPI_DOMAIN`).
    fn compute_receipt_limbs(&self) -> [u64; 4] {
        let s = self.summary_words();
        let mut h = [
            0x6a09_e667_f3bc_c908u64 ^ (self.cycle_count as u64),
            0xbb67_ae85_84ca_a73bu64 ^ s[0],
            0x3c6e_f372_fe94_f82bu64 ^ s[1],
            0xa54f_f53a_5f1d_36f1u64 ^ s[2] ^ s[3].rotate_left(17),
        ];
        for (idx, &b) in OSPC_HW_DPI_DOMAIN.as_bytes().iter().enumerate() {
            let lane = idx & 3;
            h[lane] = h[lane].wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(b as u64);
            h[lane] ^= h[(lane + 1) & 3].rotate_right(23);
        }
        for i in 0..4 {
            h[i] ^= s[i].rotate_left((13 * (i + 1)) as u32);
            h[i] = h[i].wrapping_mul(0xbf58_476d_1ce4_e5b9);
            h[i] ^= h[i] >> 31;
        }
        h
    }

    /// Execute one isolated DPI request frame and return the canonical 87-byte response frame.
    pub fn step_frame(&mut self, raw_req: &[u8]) -> Result<Vec<u8>, OspcDpiError> {
        let req = decode_req(raw_req)?;
        if req.domain != ClockDomain::HostDpi {
            return Err(OspcDpiError::DomainViolation);
        }
        if req.seq_no != self.expected_seq {
            return Err(OspcDpiError::SequenceMismatch);
        }

        // --- Pre-edge combinational outputs (matching `evalMemModuleOutputs`) ---
        let entails_lo = (self.face_lo64 & !req.tile0_in_lo64) == 0;
        let entails_hi = (self.face_hi17 & (req.tile0_in_hi17 ^ 0x1FFFF)) == 0;
        let tile0_entails: u8 = if entails_lo && entails_hi { 1 } else { 0 };
        let tile0_cam_hit: u8 = if self.cam_q == req.tile0_cam_qtag { 1 } else { 0 };

        let t1_entry_valid: u8 = if self.trie_q > 0 { 1 } else { 0 };
        let tile1_hit_valid: u8 = req.tile1_step_en & t1_entry_valid;

        let a_node = (self.port_q & 0xFFFF) as u16;
        let a_pkind = ((self.port_q >> 16) & 0x3) as u8;
        let a_tnode = ((self.port_q >> 18) & 0xFFFF) as u16;
        let a_lin = ((self.port_q >> 36) & 0x1) as u8;
        let b_node = (req.tile2_peer_word & 0xFFFF) as u16;
        let b_pkind = ((req.tile2_peer_word >> 16) & 0x3) as u8;
        let b_tnode = ((req.tile2_peer_word >> 18) & 0xFFFF) as u16;
        let b_lin = ((req.tile2_peer_word >> 36) & 0x1) as u8;
        let sym_ok = (a_tnode == b_node) && (b_tnode == a_node);
        let princ_ok = (a_pkind == 0) && (b_pkind == 0);
        let lin_pair: u8 = a_lin & b_lin;
        let tile2_redex_valid: u8 =
            if req.tile2_redex_en == 1 && sym_ok && princ_ok && lin_pair == 1 {
                1
            } else {
                0
            };

        let next_linear_ok: u8 = if req.rst {
            1
        } else {
            self.linear_ok & (if req.tile2_redex_en == 1 { lin_pair } else { 1 })
        };
        if next_linear_ok != 1 {
            return Err(OspcDpiError::DeltaNetLinearityViolation);
        }

        // --- Next-state computation for all 4 tiles (matching `stepMemModule`) ---
        // Tile 0
        let (next_face_lo64, next_face_hi17) = if req.rst {
            (0u64, 0u32)
        } else {
            match req.tile0_op_sel {
                1 => (self.face_lo64 & req.tile0_in_lo64, self.face_hi17 & req.tile0_in_hi17),
                2 => (self.face_lo64 | req.tile0_in_lo64, self.face_hi17 | req.tile0_in_hi17),
                3 => (req.tile0_in_lo64, req.tile0_in_hi17),
                _ => (self.face_lo64, self.face_hi17),
            }
        };
        let cam_addr = req.tile0_cam_addr as usize;
        if req.tile0_cam_we == 1 {
            self.cam_bank[cam_addr] = req.tile0_cam_wdata;
        }
        let next_cam_q = self.cam_bank[cam_addr]; // write-first

        // Tile 1
        let t1_raddr = (((self.trie_state as usize) << 6) | (req.tile1_sym_tag as usize)) & 0xFFF;
        let next_trie_q = self.trie_lut[t1_raddr]; // read-first
        if req.tile1_lut_we == 1 {
            self.trie_lut[(req.tile1_lut_waddr as usize) & 0xFFF] = req.tile1_lut_wdata;
        }
        let (next_trie_state, next_logup_hits) = if req.rst {
            (0u8, 0u32)
        } else {
            let ts = if req.tile1_step_en == 1 {
                (self.trie_q & 0x3F) as u8
            } else {
                self.trie_state
            };
            let lh = self.logup_hits.wrapping_add(tile1_hit_valid as u32);
            (ts, lh)
        };

        // Tile 2
        let p_addr = req.tile2_port_addr as usize;
        if req.tile2_port_we == 1 {
            self.port_bank[p_addr] = req.tile2_port_wdata;
        }
        let next_port_q = self.port_bank[p_addr]; // write-first
        let next_redex_count = if req.rst {
            0u32
        } else {
            self.redex_count.wrapping_add(tile2_redex_valid as u32)
        };

        // Tile 3
        let c_pos = (self.clause_q & 0xFFFF_FFFF) as u32;
        let c_neg = ((self.clause_q >> 32) & 0xFFFF_FFFF) as u32;
        let rem_pos = c_pos & !self.assign_neg;
        let rem_neg = c_neg & !self.assign_pos;
        let pos_zero = rem_pos == 0;
        let neg_zero = rem_neg == 0;
        let is_conflict = pos_zero && neg_zero;
        let pos_pow2 = rem_pos > 0 && (rem_pos & rem_pos.wrapping_sub(1)) == 0;
        let neg_pow2 = rem_neg > 0 && (rem_neg & rem_neg.wrapping_sub(1)) == 0;
        let is_unit_pos = neg_zero && pos_pow2;
        let is_unit_neg = pos_zero && neg_pow2;
        let (next_assign_pos, next_assign_neg, next_conflict) = if req.rst {
            (0u32, 0u32, 0u8)
        } else {
            let ap = if req.tile3_step_en == 1 && is_unit_pos {
                self.assign_pos | rem_pos
            } else {
                self.assign_pos
            };
            let an = if req.tile3_step_en == 1 && is_unit_neg {
                self.assign_neg | rem_neg
            } else {
                self.assign_neg
            };
            let cf = self.conflict_latched | (if req.tile3_step_en == 1 && is_conflict { 1 } else { 0 });
            (ap, an, cf)
        };
        let c_addr = req.tile3_clause_addr as usize;
        if req.tile3_clause_we == 1 {
            self.clause_bank[c_addr] = req.tile3_clause_wdata;
        }
        let next_clause_q = self.clause_bank[c_addr]; // write-first

        // Commit state
        self.face_lo64 = next_face_lo64;
        self.face_hi17 = next_face_hi17;
        self.cam_q = next_cam_q;
        self.trie_state = next_trie_state;
        self.logup_hits = next_logup_hits;
        self.trie_q = next_trie_q;
        self.redex_count = next_redex_count;
        self.linear_ok = next_linear_ok;
        self.port_q = next_port_q;
        self.assign_pos = next_assign_pos;
        self.assign_neg = next_assign_neg;
        self.conflict_latched = next_conflict;
        self.clause_q = next_clause_q;
        self.expected_seq = self.expected_seq.wrapping_add(1);
        self.cycle_count = self.cycle_count.wrapping_add(1);

        let limbs = self.compute_receipt_limbs();
        let resp = OspcDpiResp {
            domain: ClockDomain::HostDpi,
            seq_no: req.seq_no,
            cycle_count: self.cycle_count,
            tile0_face_lo64: self.face_lo64,
            tile0_face_hi17: self.face_hi17,
            tile0_entails,
            tile0_cam_hit,
            tile1_trie_state: self.trie_state,
            tile1_logup_hits: self.logup_hits,
            tile1_hit_valid,
            tile2_redex_valid,
            tile2_redex_count: self.redex_count,
            tile2_linear_ok: self.linear_ok,
            tile3_conflict: self.conflict_latched,
            tile3_assign_pos: self.assign_pos,
            tile3_assign_neg: self.assign_neg,
            receipt_limb0: limbs[0],
            receipt_limb1: limbs[1],
            receipt_limb2: limbs[2],
            receipt_limb3: limbs[3],
        };
        encode_resp(&resp)
    }

    /// Serve a length-framed request/response stream over arbitrary `Read`/`Write` pipes until EOF.
    pub fn serve_stream<R: Read, W: Write>(&mut self, reader: &mut R, writer: &mut W) -> io::Result<usize> {
        let mut served = 0usize;
        let mut req_buf = [0u8; ODPI_REQ_FRAME_LEN];
        loop {
            match reader.read_exact(&mut req_buf) {
                Ok(()) => {
                    let resp_bytes = self.step_frame(&req_buf).map_err(|e| {
                        io::Error::new(io::ErrorKind::InvalidData, format!("odpi refusal: {e:?}"))
                    })?;
                    writer.write_all(&resp_bytes)?;
                    writer.flush()?;
                    served += 1;
                }
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                Err(e) => return Err(e),
            }
        }
        Ok(served)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_req(seq_no: u32) -> OspcDpiReq {
        OspcDpiReq {
            domain: ClockDomain::HostDpi,
            seq_no,
            rst: false,
            tile0_op_sel: 3, // load
            tile0_in_lo64: 0x0123_4567_89AB_CDEF,
            tile0_in_hi17: 0x1_5A5A,
            tile0_cam_we: 1,
            tile0_cam_addr: 7,
            tile0_cam_wdata: 0xDEAD_BEEF_CAFE_BABE,
            tile0_cam_qtag: 0xDEAD_BEEF_CAFE_BABE,
            tile1_step_en: 1,
            tile1_sym_tag: 0x15,
            tile1_lut_we: 1,
            tile1_lut_waddr: 0x015,
            tile1_lut_wdata: 0x0000_0000_0000_002A,
            tile2_redex_en: 0,
            tile2_peer_word: 0,
            tile2_port_we: 1,
            tile2_port_addr: 2,
            tile2_port_wdata: (1u64 << 36) | (4u64 << 18) | 3u64,
            tile3_step_en: 0,
            tile3_clause_we: 1,
            tile3_clause_addr: 1,
            tile3_clause_wdata: 0x0000_0000_0000_0001, // unit positive var 0
        }
    }

    #[test]
    fn req_and_resp_canonical_roundtrip() {
        let req = sample_req(0);
        let enc = encode_req(&req).expect("valid req encodes");
        assert_eq!(enc.len(), ODPI_REQ_FRAME_LEN);
        assert_eq!(&enc[0..4], &ODPI_MAGIC);
        assert_eq!(enc[4], ODPI_VERSION);
        assert_eq!(enc[5], ClockDomain::HostDpi.to_tag());
        assert_eq!(enc[6], ODPI_KIND_STEP_REQ);
        assert_eq!(decode_req(&enc), Ok(req));

        let resp = OspcDpiResp {
            domain: ClockDomain::HostDpi,
            seq_no: 42,
            cycle_count: 43,
            tile0_face_lo64: 0xF00D_FACE_1234_5678,
            tile0_face_hi17: 0x1_FFFF,
            tile0_entails: 1,
            tile0_cam_hit: 1,
            tile1_trie_state: 63,
            tile1_logup_hits: 99,
            tile1_hit_valid: 1,
            tile2_redex_valid: 1,
            tile2_redex_count: 5,
            tile2_linear_ok: 1,
            tile3_conflict: 0,
            tile3_assign_pos: 0x0000_0003,
            tile3_assign_neg: 0x0000_0004,
            receipt_limb0: 0x1111_2222_3333_4444,
            receipt_limb1: 0x5555_6666_7777_8888,
            receipt_limb2: 0x9999_AAAA_BBBB_CCCC,
            receipt_limb3: 0xDDDD_EEEE_FFFF_0000,
        };
        let enc_r = encode_resp(&resp).expect("valid resp encodes");
        assert_eq!(enc_r.len(), ODPI_RESP_FRAME_LEN);
        assert_eq!(decode_resp(&enc_r), Ok(resp));
    }

    #[test]
    fn codec_refuses_corrupt_magic_version_domain_length_and_noncanonical() {
        let mut raw = encode_req(&sample_req(0)).unwrap();

        let mut bad_magic = raw.clone();
        bad_magic[0] ^= 0xFF;
        assert_eq!(decode_req(&bad_magic), Err(OspcDpiError::BadMagic));

        let mut bad_ver = raw.clone();
        bad_ver[4] = 0x02;
        assert_eq!(decode_req(&bad_ver), Err(OspcDpiError::BadVersion));

        let mut bad_dom = raw.clone();
        bad_dom[5] = 0x7F;
        assert_eq!(decode_req(&bad_dom), Err(OspcDpiError::BadDomainTag));

        let mut bad_kind = raw.clone();
        bad_kind[6] = ODPI_KIND_STEP_RESP;
        assert_eq!(decode_req(&bad_kind), Err(OspcDpiError::BadMsgKind));

        let mut bad_flags = raw.clone();
        bad_flags[7] = 0x02;
        assert_eq!(decode_req(&bad_flags), Err(OspcDpiError::BadFlags));

        // Truncated & trailing bytes refused
        assert_eq!(decode_req(&raw[..40]), Err(OspcDpiError::LengthMismatch));
        raw.push(0x00);
        assert_eq!(decode_req(&raw), Err(OspcDpiError::LengthMismatch));

        // Non-canonical width field (`tile0_op_sel = 4 >= 2^2`) refused
        let mut non_canon = encode_req(&sample_req(0)).unwrap();
        non_canon[16] = 4;
        assert_eq!(decode_req(&non_canon), Err(OspcDpiError::NonCanonicalField));
    }

    #[test]
    fn server_refuses_domain_seq_and_linearity_violations() {
        let mut sim = Ospc4TileHardwareSim::new();

        // Wrong clock domain (`.fabricCfg` instead of `.hostDpi`) refused
        let mut bad_dom_req = sample_req(0);
        bad_dom_req.domain = ClockDomain::FabricCfg;
        let raw_bad_dom = encode_req(&bad_dom_req).unwrap();
        assert_eq!(sim.step_frame(&raw_bad_dom), Err(OspcDpiError::DomainViolation));

        // Wrong sequence number (`seq_no = 5 != 0`) refused
        let raw_bad_seq = encode_req(&sample_req(5)).unwrap();
        assert_eq!(sim.step_frame(&raw_bad_seq), Err(OspcDpiError::SequenceMismatch));

        // DeltaNet linearity violation (`redex_en = 1`, `lin_pair = 0`) refused
        let mut bad_lin = sample_req(0);
        bad_lin.tile2_redex_en = 1;
        bad_lin.tile2_peer_word = 0; // linearFlag1 = 0 -> lin_pair = 0
        let raw_bad_lin = encode_req(&bad_lin).unwrap();
        assert_eq!(
            sim.step_frame(&raw_bad_lin),
            Err(OspcDpiError::DeltaNetLinearityViolation)
        );
    }

    #[test]
    fn four_tile_multi_cycle_kat_and_isolated_stream() {
        // Cycle 0: load FaceIdeal4, write CAM slot 7, write DiscrTree LUT, write DeltaNet port 2, write LRAT unit clause (x1)
        let req0 = sample_req(0);
        // Cycle 1: meet FaceIdeal4 with mask, fire DeltaNet valid principal redex (node 3 <-> node 4, both linear=1),
        //          step StreamLRAT to propagate unit x1 (bit 0)
        let req1 = OspcDpiReq {
            domain: ClockDomain::HostDpi,
            seq_no: 1,
            rst: false,
            tile0_op_sel: 1, // meet
            tile0_in_lo64: 0x0000_FFFF_0000_FFFF,
            tile0_in_hi17: 0x0_0F0F,
            tile0_cam_we: 0,
            tile0_cam_addr: 7,
            tile0_cam_wdata: 0,
            tile0_cam_qtag: 0xDEAD_BEEF_CAFE_BABE,
            tile1_step_en: 1,
            tile1_sym_tag: 0x15,
            tile1_lut_we: 0,
            tile1_lut_waddr: 0,
            tile1_lut_wdata: 0,
            tile2_redex_en: 1,
            tile2_peer_word: (1u64 << 36) | (3u64 << 18) | 4u64, // node 4 -> target 3, kind=0, lin=1
            tile2_port_we: 0,
            tile2_port_addr: 2,
            tile2_port_wdata: 0,
            tile3_step_en: 1,
            tile3_clause_we: 0,
            tile3_clause_addr: 1,
            tile3_clause_wdata: 0,
        };

        let mut wire_in = encode_req(&req0).unwrap();
        wire_in.extend_from_slice(&encode_req(&req1).unwrap());

        let mut sim = Ospc4TileHardwareSim::new();
        let mut cursor = std::io::Cursor::new(wire_in);
        let mut wire_out = Vec::new();
        let served = sim.serve_stream(&mut cursor, &mut wire_out).expect("stream succeeds");
        assert_eq!(served, 2);
        assert_eq!(wire_out.len(), 2 * ODPI_RESP_FRAME_LEN);

        let r0 = decode_resp(&wire_out[0..ODPI_RESP_FRAME_LEN]).unwrap();
        assert_eq!(r0.seq_no, 0);
        assert_eq!(r0.cycle_count, 1);
        assert_eq!(r0.tile0_face_lo64, 0x0123_4567_89AB_CDEF);
        assert_eq!(r0.tile0_face_hi17, 0x1_5A5A);
        assert_eq!(r0.tile2_linear_ok, 1);

        let r1 = decode_resp(&wire_out[ODPI_RESP_FRAME_LEN..]).unwrap();
        assert_eq!(r1.seq_no, 1);
        assert_eq!(r1.cycle_count, 2);
        assert_eq!(r1.tile0_face_lo64, 0x0123_4567_89AB_CDEF & 0x0000_FFFF_0000_FFFF);
        assert_eq!(r1.tile0_face_hi17, 0x1_5A5A & 0x0_0F0F);
        assert_eq!(r1.tile0_cam_hit, 1);
        assert_eq!(r1.tile2_redex_valid, 1);
        assert_eq!(r1.tile2_redex_count, 1);
        assert_eq!(r1.tile2_linear_ok, 1);
        assert_eq!(r1.tile3_assign_pos, 0x0000_0001);
        assert_eq!(r1.tile3_conflict, 0);
    }
}
