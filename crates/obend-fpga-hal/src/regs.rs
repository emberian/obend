//! Unified BAR0 CSR Register Map (`0x0000..0x04FF`), 512-bit AXI4-Stream Beats,
//! and 7-Section `OBCAMv1` (`\0OBCAMV1`, `0x31564D4143424F00`) Wire Frame Codec.

use serde::{Deserialize, Serialize};

/// `"OBENDF20"` little-endian 64-bit magic (`0x303246444E45424F`).
pub const OBEND_MAGIC_F20: u64 = 0x3032_4644_4E45_424F;

/// Default version & capabilities word (`v1`, 4 zones, 32 ports, 512-bit DMA).
pub const OBEND_VERSION_CAPS_DEFAULT: u64 = 0x0001_0004_0020_0200;

/// `"\0OBCAMV1"` little-endian 64-bit wire magic (`0x31564D4143424F00`).
pub const OBCAM_WIRE_MAGIC: u64 = 0x3156_4D41_4342_4F00;

/// Total BAR0 + DMA shared memory aperture size (4 MiB).
pub const SHM_APERTURE_BYTES: usize = 4 * 1024 * 1024;

/// BAR0 CSR Aperture offsets (`0x0000..0x04FF`).
pub mod csr {
    // 0x0000..0x00FF: Global Control & DMA Ring Pointers
    pub const OBEND_MAGIC: usize = 0x0000;
    pub const OBEND_VERSION_CAPS: usize = 0x0008;
    pub const OBEND_CTRL: usize = 0x0010;
    pub const OBEND_CYCLE_COUNT: usize = 0x0018;
    pub const DMA_TX_RING: usize = 0x0020;
    pub const DMA_RX_RING: usize = 0x0028;
    pub const OBEND_DPR_SLOT_GUARD_PIN: usize = 0x0030;

    // 0x0100..0x03FF: 32 x 64-bit Input Ports, Output Ports & State Snapshot
    pub const OBEND_IN_PORT_BASE: usize = 0x0100;
    pub const OBEND_OUT_PORT_BASE: usize = 0x0200;
    pub const OBEND_STATE_SNAP_BASE: usize = 0x0300;

    // 0x0400..0x04FF: 4-Zone Silicon Elaborator Fabric CSRs
    pub const SILICON_CTRL_STATUS: usize = 0x0400;
    pub const TARGET_EXPR_H: usize = 0x0404;
    pub const TARGET_TYPE_H: usize = 0x0408;
    pub const TARGET_DECL_SYM: usize = 0x040C;
    pub const FUEL_BUDGET: usize = 0x0410;
    pub const RESULT_STATUS: usize = 0x0414;
    pub const PERF_CYCLES: usize = 0x0418;
    pub const PERF_CAM_HITS: usize = 0x041C;
    pub const PERF_CAM_ALLOCS: usize = 0x0420;
    pub const PERF_BYPASS_CNT: usize = 0x0424;
    pub const PERF_NOC_FLITS: usize = 0x0428;
    pub const PERF_LUT_HITS: usize = 0x042C;
    pub const ZONE3_MATCH_THM: usize = 0x0430;

    /// Byte offset of `OBEND_IN_PORT[idx]` (`idx in 0..32`).
    #[inline]
    pub const fn in_port_offset(idx: usize) -> usize {
        assert!(idx < 32);
        OBEND_IN_PORT_BASE + idx * 8
    }

    /// Byte offset of `OBEND_OUT_PORT[idx]` (`idx in 0..32`).
    #[inline]
    pub const fn out_port_offset(idx: usize) -> usize {
        assert!(idx < 32);
        OBEND_OUT_PORT_BASE + idx * 8
    }

    /// Byte offset of `OBEND_STATE_SNAP[idx]` (`idx in 0..32`, i.e., `OBEND_STATE_SNAP[0..31]`).
    #[inline]
    pub const fn state_snap_offset(idx: usize) -> usize {
        assert!(idx < 32);
        OBEND_STATE_SNAP_BASE + idx * 8
    }
}

/// Control bitmasks for `OBEND_CTRL` (`0x0010`).
pub mod ctrl_bits {
    pub const AP_START: u32 = 1 << 0;
    pub const AP_DONE: u32 = 1 << 1;
    pub const SOFT_RST: u32 = 1 << 2;
    pub const STEP_ONCE: u32 = 1 << 3;
    pub const DPR_ISOLATE_EN: u32 = 1 << 4;
    pub const DPR_FALLBACK_ACTIVE: u32 = 1 << 5;
}

/// 512-bit (64-byte) AXI4-Stream DMA Beat (`sh_pcis_*` / Verilator DMA ring).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AxiStream512Beat {
    pub tdata: [u8; 64],
    pub tkeep: u64,
    pub tlast: bool,
}

impl Default for AxiStream512Beat {
    fn default() -> Self {
        Self {
            tdata: [0u8; 64],
            tkeep: u64::MAX,
            tlast: false,
        }
    }
}

impl AxiStream512Beat {
    /// Construct a 512-bit beat from up to 64 bytes.
    pub fn from_slice(bytes: &[u8], tlast: bool) -> Self {
        let mut tdata = [0u8; 64];
        let n = bytes.len().min(64);
        tdata[..n].copy_from_slice(&bytes[..n]);
        let tkeep = if n == 64 {
            u64::MAX
        } else if n == 0 {
            0
        } else {
            (1u64 << n) - 1
        };
        Self {
            tdata,
            tkeep,
            tlast,
        }
    }

    /// Read a little-endian `u64` word `idx` (`0..8`) from `tdata`.
    pub fn word64(&self, idx: usize) -> u64 {
        assert!(idx < 8);
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&self.tdata[idx * 8..(idx + 1) * 8]);
        u64::from_le_bytes(buf)
    }

    /// Write a little-endian `u64` word `idx` (`0..8`) into `tdata`.
    pub fn set_word64(&mut self, idx: usize, val: u64) {
        assert!(idx < 8);
        self.tdata[idx * 8..(idx + 1) * 8].copy_from_slice(&val.to_le_bytes());
    }
}

/// 88-bit (11-byte) Packed Expression CAM Node Word (`PackedNodeWord88`) for Zone 1 `obend_zone1_expr_cam`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackedNodeWord88 {
    pub opcode: u8,
    pub binder_depth: u16,
    pub child0: u32,
    pub child1: u32,
}

impl PackedNodeWord88 {
    pub const BYTE_LEN: usize = 11;

    pub fn to_bytes(&self) -> [u8; 11] {
        let mut out = [0u8; 11];
        out[0] = self.opcode;
        out[1..3].copy_from_slice(&self.binder_depth.to_le_bytes());
        out[3..7].copy_from_slice(&self.child0.to_le_bytes());
        out[7..11].copy_from_slice(&self.child1.to_le_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < 11 {
            return None;
        }
        let opcode = bytes[0];
        let binder_depth = u16::from_le_bytes([bytes[1], bytes[2]]);
        let child0 = u32::from_le_bytes([bytes[3], bytes[4], bytes[5], bytes[6]]);
        let child1 = u32::from_le_bytes([bytes[7], bytes[8], bytes[9], bytes[10]]);
        Some(Self {
            opcode,
            binder_depth,
            child0,
            child1,
        })
    }

    /// Compute the 10-bit UltraRAM hash bucket matching `obend_zone1_expr_cam` (`silicon_elab_top.sv`).
    pub fn hash_bucket10(&self) -> u16 {
        let c0 = (self.child0 as u16) & 0x03FF;
        let c1 = (self.child1 as u16) & 0x03FF;
        c0 ^ c1 ^ (self.opcode as u16)
    }
}

/// 64-byte `OBCAMv1` Wire Header (`\0OBCAMV1`, magic `0x31564D4143424F00`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObcamWireHeader {
    pub magic: u64,
    pub target_expr_h: u32,
    pub target_type_h: u32,
    pub target_decl_sym: u32,
    pub fuel_budget: u32,
    pub section_counts: [u32; 7],
    pub flags: u32,
    pub payload_crc32: u32,
}

impl Default for ObcamWireHeader {
    fn default() -> Self {
        Self {
            magic: OBCAM_WIRE_MAGIC,
            target_expr_h: 1,
            target_type_h: 1,
            target_decl_sym: 1,
            fuel_budget: 1024,
            section_counts: [0; 7],
            flags: 0,
            payload_crc32: 0,
        }
    }
}

impl ObcamWireHeader {
    pub fn to_beat(&self, tlast: bool) -> AxiStream512Beat {
        let mut tdata = [0u8; 64];
        tdata[0..8].copy_from_slice(&self.magic.to_le_bytes());
        tdata[8..12].copy_from_slice(&self.target_expr_h.to_le_bytes());
        tdata[12..16].copy_from_slice(&self.target_type_h.to_le_bytes());
        tdata[16..20].copy_from_slice(&self.target_decl_sym.to_le_bytes());
        tdata[20..24].copy_from_slice(&self.fuel_budget.to_le_bytes());
        for (i, &c) in self.section_counts.iter().enumerate() {
            tdata[24 + i * 4..28 + i * 4].copy_from_slice(&c.to_le_bytes());
        }
        tdata[52..56].copy_from_slice(&self.flags.to_le_bytes());
        tdata[56..60].copy_from_slice(&self.payload_crc32.to_le_bytes());
        AxiStream512Beat {
            tdata,
            tkeep: u64::MAX,
            tlast,
        }
    }

    pub fn from_beat(beat: &AxiStream512Beat) -> Option<Self> {
        let magic = beat.word64(0);
        if magic != OBCAM_WIRE_MAGIC {
            return None;
        }
        let d = &beat.tdata;
        let target_expr_h = u32::from_le_bytes([d[8], d[9], d[10], d[11]]);
        let target_type_h = u32::from_le_bytes([d[12], d[13], d[14], d[15]]);
        let target_decl_sym = u32::from_le_bytes([d[16], d[17], d[18], d[19]]);
        let fuel_budget = u32::from_le_bytes([d[20], d[21], d[22], d[23]]);
        let mut section_counts = [0u32; 7];
        for i in 0..7 {
            let b = 24 + i * 4;
            section_counts[i] = u32::from_le_bytes([d[b], d[b + 1], d[b + 2], d[b + 3]]);
        }
        let flags = u32::from_le_bytes([d[52], d[53], d[54], d[55]]);
        let payload_crc32 = u32::from_le_bytes([d[56], d[57], d[58], d[59]]);
        Some(Self {
            magic,
            target_expr_h,
            target_type_h,
            target_decl_sym,
            fuel_budget,
            section_counts,
            flags,
            payload_crc32,
        })
    }
}

/// 7-Section `SiliconElabWireFrame` matching `Obend.Lower.SiliconElabFabric` (`OBCAMv1`):
/// 1. `cam_nodes`: 88-bit `PackedNodeWord88` expression arena entries (Zone 1)
/// 2. `env_decls`: `(sym_id, type_handle, value_handle)` environment table entries (Zone 4)
/// 3. `inductive_rules`: `(ind_sym, recursor_sym, num_params, num_indices)` entries (Zone 4)
/// 4. `quot_entries`: `[u32; 4]` quotient configuration handles (Zone 4)
/// 5. `discr_trie_entries`: `(key_tok0, key_tok1, thm_id)` discrimination tree LUT entries (Zone 3)
/// 6. `unify_worklist`: `(lhs_handle, rhs_handle)` unification goals (Zone 2)
/// 7. `infer_seeds`: `(expr_handle, inferred_type_handle)` bottom-up CAM seeds (Zone 4)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiliconElabWireFrame {
    pub header: ObcamWireHeader,
    pub cam_nodes: Vec<PackedNodeWord88>,
    pub env_decls: Vec<(u32, u32, u32)>,
    pub inductive_rules: Vec<(u32, u32, u16, u16)>,
    pub quot_entries: Vec<[u32; 4]>,
    pub discr_trie_entries: Vec<(u32, u32, u32)>,
    pub unify_worklist: Vec<(u32, u32)>,
    pub infer_seeds: Vec<(u32, u32)>,
}

impl SiliconElabWireFrame {
    pub fn new(
        target_expr_h: u32,
        target_type_h: u32,
        target_decl_sym: u32,
        fuel_budget: u32,
    ) -> Self {
        Self {
            header: ObcamWireHeader {
                magic: OBCAM_WIRE_MAGIC,
                target_expr_h,
                target_type_h,
                target_decl_sym,
                fuel_budget,
                section_counts: [0; 7],
                flags: 0,
                payload_crc32: 0,
            },
            cam_nodes: Vec::new(),
            env_decls: Vec::new(),
            inductive_rules: Vec::new(),
            quot_entries: Vec::new(),
            discr_trie_entries: Vec::new(),
            unify_worklist: Vec::new(),
            infer_seeds: Vec::new(),
        }
    }

    /// Encode this 7-section `SiliconElabWireFrame` into a sequence of 512-bit `AxiStream512Beat` DMA beats.
    pub fn to_axi_beats(&self) -> Vec<AxiStream512Beat> {
        let mut payload = Vec::new();
        for node in &self.cam_nodes {
            payload.extend_from_slice(&node.to_bytes());
        }
        for &(s, ty, v) in &self.env_decls {
            payload.extend_from_slice(&s.to_le_bytes());
            payload.extend_from_slice(&ty.to_le_bytes());
            payload.extend_from_slice(&v.to_le_bytes());
        }
        for &(ind, rec, np, ni) in &self.inductive_rules {
            payload.extend_from_slice(&ind.to_le_bytes());
            payload.extend_from_slice(&rec.to_le_bytes());
            payload.extend_from_slice(&np.to_le_bytes());
            payload.extend_from_slice(&ni.to_le_bytes());
        }
        for q in &self.quot_entries {
            for &w in q {
                payload.extend_from_slice(&w.to_le_bytes());
            }
        }
        for &(k0, k1, thm) in &self.discr_trie_entries {
            payload.extend_from_slice(&k0.to_le_bytes());
            payload.extend_from_slice(&k1.to_le_bytes());
            payload.extend_from_slice(&thm.to_le_bytes());
        }
        for &(lhs, rhs) in &self.unify_worklist {
            payload.extend_from_slice(&lhs.to_le_bytes());
            payload.extend_from_slice(&rhs.to_le_bytes());
        }
        for &(e, ty) in &self.infer_seeds {
            payload.extend_from_slice(&e.to_le_bytes());
            payload.extend_from_slice(&ty.to_le_bytes());
        }

        let mut hdr = self.header;
        hdr.section_counts = [
            self.cam_nodes.len() as u32,
            self.env_decls.len() as u32,
            self.inductive_rules.len() as u32,
            self.quot_entries.len() as u32,
            self.discr_trie_entries.len() as u32,
            self.unify_worklist.len() as u32,
            self.infer_seeds.len() as u32,
        ];
        hdr.payload_crc32 = simple_crc32(&payload);

        let mut beats = Vec::new();
        beats.push(hdr.to_beat(payload.is_empty()));
        let chunks: Vec<&[u8]> = payload.chunks(64).collect();
        for (idx, chunk) in chunks.iter().enumerate() {
            let is_last = idx + 1 == chunks.len();
            beats.push(AxiStream512Beat::from_slice(chunk, is_last));
        }
        beats
    }

    /// Decode a 7-section `SiliconElabWireFrame` from 512-bit `AxiStream512Beat` DMA beats.
    pub fn from_axi_beats(beats: &[AxiStream512Beat]) -> Option<Self> {
        let first = beats.first()?;
        let header = ObcamWireHeader::from_beat(first)?;
        let mut payload = Vec::new();
        for beat in &beats[1..] {
            payload.extend_from_slice(&beat.tdata);
        }
        let mut cursor = 0usize;

        let mut cam_nodes = Vec::with_capacity(header.section_counts[0] as usize);
        for _ in 0..header.section_counts[0] {
            let node = PackedNodeWord88::from_bytes(payload.get(cursor..cursor + 11)?)?;
            cam_nodes.push(node);
            cursor += 11;
        }

        let mut env_decls = Vec::with_capacity(header.section_counts[1] as usize);
        for _ in 0..header.section_counts[1] {
            let b = payload.get(cursor..cursor + 12)?;
            let s = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            let ty = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
            let v = u32::from_le_bytes([b[8], b[9], b[10], b[11]]);
            env_decls.push((s, ty, v));
            cursor += 12;
        }

        let mut inductive_rules = Vec::with_capacity(header.section_counts[2] as usize);
        for _ in 0..header.section_counts[2] {
            let b = payload.get(cursor..cursor + 12)?;
            let ind = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            let rec = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
            let np = u16::from_le_bytes([b[8], b[9]]);
            let ni = u16::from_le_bytes([b[10], b[11]]);
            inductive_rules.push((ind, rec, np, ni));
            cursor += 12;
        }

        let mut quot_entries = Vec::with_capacity(header.section_counts[3] as usize);
        for _ in 0..header.section_counts[3] {
            let b = payload.get(cursor..cursor + 16)?;
            let q0 = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            let q1 = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
            let q2 = u32::from_le_bytes([b[8], b[9], b[10], b[11]]);
            let q3 = u32::from_le_bytes([b[12], b[13], b[14], b[15]]);
            quot_entries.push([q0, q1, q2, q3]);
            cursor += 16;
        }

        let mut discr_trie_entries = Vec::with_capacity(header.section_counts[4] as usize);
        for _ in 0..header.section_counts[4] {
            let b = payload.get(cursor..cursor + 12)?;
            let k0 = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            let k1 = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
            let thm = u32::from_le_bytes([b[8], b[9], b[10], b[11]]);
            discr_trie_entries.push((k0, k1, thm));
            cursor += 12;
        }

        let mut unify_worklist = Vec::with_capacity(header.section_counts[5] as usize);
        for _ in 0..header.section_counts[5] {
            let b = payload.get(cursor..cursor + 8)?;
            let lhs = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            let rhs = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
            unify_worklist.push((lhs, rhs));
            cursor += 8;
        }

        let mut infer_seeds = Vec::with_capacity(header.section_counts[6] as usize);
        for _ in 0..header.section_counts[6] {
            let b = payload.get(cursor..cursor + 8)?;
            let e = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
            let ty = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
            infer_seeds.push((e, ty));
            cursor += 8;
        }

        let computed_crc = simple_crc32(&payload[..cursor]);
        if computed_crc != header.payload_crc32 {
            return None;
        }

        Some(Self {
            header,
            cam_nodes,
            env_decls,
            inductive_rules,
            quot_entries,
            discr_trie_entries,
            unify_worklist,
            infer_seeds,
        })
    }
}

/// Deterministic IEEE 802.3 CRC-32 checksum over `bytes`.
pub fn simple_crc32(bytes: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

/// Hardware 88-bit `PackedNodeWord` (`BitVec 88`) matching `Obend.Lower.ExprCAM.packNodeWord88`
/// (`QUALIFICATION-AND-SILICON-LEAN.md` §2.1):
/// - `[15:0]`: `h0` (16b) | `[31:16]`: `h1` (16b) | `[47:32]`: `h2` (16b)
/// - `[63:48]`: `sym_idx` (16b) | `[79:64]`: `max_loose_bvar` (16b)
/// - `[80]`: `has_fvar` (1b) | `[81]`: `has_mvar` (1b) | `[82]`: `has_loose_bvar` (1b)
/// - `[83]`: `0` (1b) | `[87:84]`: `tag` (4b)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct HwPackedNodeWord88 {
    pub tag: u8,
    pub h0: u16,
    pub h1: u16,
    pub h2: u16,
    pub sym_idx: u16,
    pub has_loose_bvar: bool,
    pub has_fvar: bool,
    pub has_mvar: bool,
    pub max_loose_bvar: u16,
}

impl HwPackedNodeWord88 {
    /// Pack into an 88-bit word (`u128` with bits `[127:88] == 0`) matching `packNodeWord88`.
    pub fn pack_word88(&self) -> u128 {
        let mut w = 0u128;
        w |= self.h0 as u128;
        w |= (self.h1 as u128) << 16;
        w |= (self.h2 as u128) << 32;
        w |= (self.sym_idx as u128) << 48;
        w |= (self.max_loose_bvar as u128) << 64;
        if self.has_fvar {
            w |= 1u128 << 80;
        }
        if self.has_mvar {
            w |= 1u128 << 81;
        }
        if self.has_loose_bvar {
            w |= 1u128 << 82;
        }
        w |= ((self.tag & 0x0F) as u128) << 84;
        w
    }

    /// Unpack from an 88-bit word matching `unpackNodeWord88`.
    pub fn unpack_word88(w: u128) -> Self {
        Self {
            h0: (w & 0xFFFF) as u16,
            h1: ((w >> 16) & 0xFFFF) as u16,
            h2: ((w >> 32) & 0xFFFF) as u16,
            sym_idx: ((w >> 48) & 0xFFFF) as u16,
            max_loose_bvar: ((w >> 64) & 0xFFFF) as u16,
            has_fvar: ((w >> 80) & 1) != 0,
            has_mvar: ((w >> 81) & 1) != 0,
            has_loose_bvar: ((w >> 82) & 1) != 0,
            tag: ((w >> 84) & 0x0F) as u8,
        }
    }

    /// Serialize to 11 little-endian bytes (`BitVec 88`).
    pub fn to_le_bytes11(&self) -> [u8; 11] {
        let le16 = self.pack_word88().to_le_bytes();
        let mut out = [0u8; 11];
        out.copy_from_slice(&le16[..11]);
        out
    }

    /// Deserialize from 11 little-endian bytes (`BitVec 88`).
    pub fn from_le_bytes11(bytes: &[u8; 11]) -> Self {
        let mut le16 = [0u8; 16];
        le16[..11].copy_from_slice(bytes);
        Self::unpack_word88(u128::from_le_bytes(le16))
    }

    /// Convert to Zone-1 CAM word `PackedNodeWord88`.
    pub fn to_cam_node(&self) -> PackedNodeWord88 {
        let flags = (u8::from(self.has_fvar))
            | (u8::from(self.has_mvar) << 1)
            | (u8::from(self.has_loose_bvar) << 2);
        PackedNodeWord88 {
            opcode: ((self.tag & 0x0F) << 4) | flags,
            binder_depth: self.max_loose_bvar,
            child0: ((self.sym_idx as u32) << 16) | (self.h0 as u32),
            child1: ((self.h2 as u32) << 16) | (self.h1 as u32),
        }
    }
}

/// Encode `n` using unsigned LEB128 matching `Obend.Lower.ExprCAM.natToVarBytes`.
pub fn encode_lean_varint(mut n: u128, out: &mut Vec<u8>) {
    while n >= 128 {
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out.push(n as u8);
}

/// Decode an unsigned LEB128 integer matching `Obend.Lower.ExprCAM.decodeVarBytes`.
pub fn decode_lean_varint(bytes: &[u8]) -> Option<(u128, &[u8])> {
    let mut val = 0u128;
    let mut shift = 0u32;
    for (idx, &b) in bytes.iter().enumerate() {
        if shift >= 126 && (b & 0xFC) != 0 {
            return None;
        }
        val |= ((b & 0x7F) as u128) << shift;
        if b < 128 {
            return Some((val, &bytes[idx + 1..]));
        }
        shift += 7;
    }
    None
}

/// Lean `SiliconElabWireHeader` decoded from `Obend.Lower.ExprCAM.encodeWireHeader`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanObcamWireHeader {
    pub magic: u64,
    pub version: u32,
    pub flags: u32,
    pub node_count: u32,
    pub symbol_count: u32,
    pub level_count: u32,
    pub const_count: u32,
    pub rec_rule_count: u32,
    pub lut_entry_count: u32,
    pub icap_frame_count: u32,
    pub target_decl_sym_idx: u32,
    pub target_expr_handle: u32,
    pub target_type_handle: u32,
    pub fuel_budget: u32,
    pub env_pin_digest64: u64,
}

impl SiliconElabWireFrame {
    /// Decode a `ByteArray` produced by Lean's `Obend.Lower.ExprCAM.serializeSiliconWireFrame`
    /// (`encodeWireHeader` + Section-1 `PackedNodeWord` array) into a `SiliconElabWireFrame`.
    pub fn from_lean_wire_bytes(bytes: &[u8]) -> Option<(LeanObcamWireHeader, Self)> {
        let (magic, r) = decode_lean_varint(bytes)?;
        let magic_u64 = u64::try_from(magic).ok()?;
        if magic_u64 != OBCAM_WIRE_MAGIC {
            return None;
        }
        let (version, r) = decode_lean_varint(r)?;
        let (flags, r) = decode_lean_varint(r)?;
        let (node_count, r) = decode_lean_varint(r)?;
        let (symbol_count, r) = decode_lean_varint(r)?;
        let (level_count, r) = decode_lean_varint(r)?;
        let (const_count, r) = decode_lean_varint(r)?;
        let (rec_rule_count, r) = decode_lean_varint(r)?;
        let (lut_entry_count, r) = decode_lean_varint(r)?;
        let (icap_frame_count, r) = decode_lean_varint(r)?;
        let (target_decl_sym_idx, r) = decode_lean_varint(r)?;
        let (target_expr_handle, r) = decode_lean_varint(r)?;
        let (target_type_handle, r) = decode_lean_varint(r)?;
        let (fuel_budget, r) = decode_lean_varint(r)?;
        let (env_pin_digest64, r) = decode_lean_varint(r)?;

        let lean_hdr = LeanObcamWireHeader {
            magic: magic_u64,
            version: u32::try_from(version).ok()?,
            flags: u32::try_from(flags).ok()?,
            node_count: u32::try_from(node_count).ok()?,
            symbol_count: u32::try_from(symbol_count).ok()?,
            level_count: u32::try_from(level_count).ok()?,
            const_count: u32::try_from(const_count).ok()?,
            rec_rule_count: u32::try_from(rec_rule_count).ok()?,
            lut_entry_count: u32::try_from(lut_entry_count).ok()?,
            icap_frame_count: u32::try_from(icap_frame_count).ok()?,
            target_decl_sym_idx: u32::try_from(target_decl_sym_idx).ok()?,
            target_expr_handle: u32::try_from(target_expr_handle).ok()?,
            target_type_handle: u32::try_from(target_type_handle).ok()?,
            fuel_budget: u32::try_from(fuel_budget).ok()?,
            env_pin_digest64: u64::try_from(env_pin_digest64).ok()?,
        };

        let (list_len, mut cur) = decode_lean_varint(r)?;
        let mut frame = SiliconElabWireFrame::new(
            lean_hdr.target_expr_handle,
            lean_hdr.target_type_handle,
            lean_hdr.target_decl_sym_idx,
            lean_hdr.fuel_budget,
        );
        frame.header.flags = lean_hdr.flags;

        for _ in 0..list_len {
            let (tag, r1) = decode_lean_varint(cur)?;
            let (h0, r2) = decode_lean_varint(r1)?;
            let (h1, r3) = decode_lean_varint(r2)?;
            let (h2, r4) = decode_lean_varint(r3)?;
            let (sym_idx, r5) = decode_lean_varint(r4)?;
            let (has_loose, r6) = decode_lean_varint(r5)?;
            let (has_f, r7) = decode_lean_varint(r6)?;
            let (has_m, r8) = decode_lean_varint(r7)?;
            let (max_b, r9) = decode_lean_varint(r8)?;
            cur = r9;
            let hw = HwPackedNodeWord88 {
                tag: (tag & 0x0F) as u8,
                h0: (h0 & 0xFFFF) as u16,
                h1: (h1 & 0xFFFF) as u16,
                h2: (h2 & 0xFFFF) as u16,
                sym_idx: (sym_idx & 0xFFFF) as u16,
                has_loose_bvar: has_loose != 0,
                has_fvar: has_f != 0,
                has_mvar: has_m != 0,
                max_loose_bvar: (max_b & 0xFFFF) as u16,
            };
            frame.cam_nodes.push(hw.to_cam_node());
        }

        Some((lean_hdr, frame))
    }
}

