//! `obend-fpga-hal` — Unified 4-Rung Cloud-FPGA Hardware Abstraction Layer.
//!
//! Provides a single trait (`FpgaHalBackend`) and unified controller (`ObendFpgaHal`)
//! spanning:
//! - **Rung 1 (`SimBackend`)**: POSIX 4 MiB shared memory (`mmap`) + Unix domain socket
//!   Verilator co-simulation daemon (`obend-silicon-sim`),
//! - **Rung 3 & Rung 4 (`AwsF2Backend`)**: AWS EC2 F2 (`vu47p` `xcvu47p-fsvh2892-2-e`)
//!   BAR0 OCL MMIO (`/dev/fpga0`) + 512-bit AXI4-Stream DMA (`/dev/xdma0_{h2c,c2h}_0`) +
//!   3-phase glitch-free ICAP Dynamic Partial Reconfiguration (`obend_macro_icap_dpr_tile`).

pub mod aws_f2_backend;
pub mod regs;
pub mod sim_backend;

use aws_f2_backend::{AwsF2Backend, AwsF2Config};
use regs::{ctrl_bits, csr, AxiStream512Beat, SiliconElabWireFrame, OBEND_MAGIC_F20};
use serde::{Deserialize, Serialize};
use sim_backend::SimBackend;
use thiserror::Error;

/// Errors returned by `obend-fpga-hal`.
#[derive(Debug, Error)]
pub enum FpgaHalError {
    #[error("FPGA HAL I/O error: {0}")]
    Io(String),
    #[error("BAR0 CSR offset 0x{0:x} out of bounds")]
    OutOfBounds(usize),
    #[error("invalid BAR0 magic: expected 0x{expected:016x}, found 0x{found:016x}")]
    InvalidMagic { expected: u64, found: u64 },
    #[error("OBCAMv1 wire frame decode error: {0}")]
    WireDecode(String),
    #[error("ICAP DPR digest mismatch: expected 0x{expected:016x}, computed 0x{computed:016x}")]
    DprDigestMismatch { expected: u64, computed: u64 },
}

/// Real-time hardware & 4-zone Silicon Elaborator telemetry for `obend-node` and `obend-gui`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiliconTelemetry {
    pub backend: String,
    pub total_cycles: u64,
    pub silicon_cycles: u32,
    pub cam_hits: u32,
    pub cam_allocs: u32,
    pub uram_bypass_hits: u32,
    pub noc_flits: u32,
    pub discr_lut_hits: u32,
    pub zone3_match_thm: u32,
    pub kernel_accepted: bool,
    pub dpr_isolated: bool,
    pub dpr_fallback_active: bool,
}

/// Receipt emitted by a 3-phase ICAP Dynamic Partial Reconfiguration hot-swap.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IcapDprSwapReceipt {
    pub slot_name: String,
    pub frame_word: u64,
    pub expected_digest: u64,
    pub computed_digest: u64,
    pub moved_pin_violation: bool,
    pub committed: bool,
    pub fallback_activated: bool,
    pub held_output_port0_during_isolation: u64,
}

/// Common trait implemented by both `SimBackend` (Rung 1) and `AwsF2Backend` (Rung 3/4).
pub trait FpgaHalBackend: Send + Sync {
    fn backend_name(&self) -> &'static str;
    fn read_csr32(&self, offset: usize) -> Result<u32, FpgaHalError>;
    fn write_csr32(&mut self, offset: usize, val: u32) -> Result<(), FpgaHalError>;
    fn read_csr64(&self, offset: usize) -> Result<u64, FpgaHalError>;
    fn write_csr64(&mut self, offset: usize, val: u64) -> Result<(), FpgaHalError>;
    fn push_dma_beats(&mut self, beats: &[AxiStream512Beat]) -> Result<usize, FpgaHalError>;
    fn pull_dma_beats(&mut self, max_beats: usize) -> Result<Vec<AxiStream512Beat>, FpgaHalError>;
    fn step_cycles(&mut self, num_cycles: u32) -> Result<u64, FpgaHalError>;
    fn read_telemetry(&self) -> Result<SiliconTelemetry, FpgaHalError>;
}

/// Unified Cloud-FPGA Hardware Abstraction Layer controller (`ObendFpgaHal`).
pub struct ObendFpgaHal {
    backend: Box<dyn FpgaHalBackend>,
}

impl ObendFpgaHal {
    /// Construct an `ObendFpgaHal` backed by the in-process POSIX `mmap` Verilator simulation backend.
    pub fn new_sim() -> Result<Self, FpgaHalError> {
        let backend = SimBackend::new()?;
        Ok(Self {
            backend: Box::new(backend),
        })
    }

    /// Construct an `ObendFpgaHal` backed by an AWS EC2 F2 (`vu47p`) hardware backend.
    pub fn new_aws_f2(cfg: AwsF2Config) -> Result<Self, FpgaHalError> {
        let backend = AwsF2Backend::open(cfg)?;
        Ok(Self {
            backend: Box::new(backend),
        })
    }

    /// Wrap any `FpgaHalBackend` implementation.
    pub fn from_backend<B: FpgaHalBackend + 'static>(backend: B) -> Self {
        Self {
            backend: Box::new(backend),
        }
    }

    /// Auto-select `AwsF2Backend` if `OBEND_FPGA_BACKEND=aws-f2` and `/dev/fpga0` exists,
    /// otherwise fall back cleanly to `SimBackend`.
    pub fn auto_connect() -> Result<Self, FpgaHalError> {
        if std::env::var("OBEND_FPGA_BACKEND").as_deref() == Ok("aws-f2") {
            let cfg = AwsF2Config::default();
            if cfg.bar0_path.exists() {
                return Self::new_aws_f2(cfg);
            }
        }
        Self::new_sim()
    }

    pub fn backend_name(&self) -> &'static str {
        self.backend.backend_name()
    }

    /// Verify the BAR0 `"OBENDF20"` magic word at offset `0x0000`.
    pub fn verify_magic(&self) -> Result<u64, FpgaHalError> {
        let magic = self.backend.read_csr64(csr::OBEND_MAGIC)?;
        if magic != OBEND_MAGIC_F20 {
            return Err(FpgaHalError::InvalidMagic {
                expected: OBEND_MAGIC_F20,
                found: magic,
            });
        }
        Ok(magic)
    }

    /// Write a 64-bit input port `OBEND_IN_PORT[idx]` (`idx in 0..32`).
    pub fn write_in_port(&mut self, idx: usize, val: u64) -> Result<(), FpgaHalError> {
        self.backend.write_csr64(csr::in_port_offset(idx), val)
    }

    /// Read a 64-bit output port `OBEND_OUT_PORT[idx]` (`idx in 0..32`).
    pub fn read_out_port(&self, idx: usize) -> Result<u64, FpgaHalError> {
        self.backend.read_csr64(csr::out_port_offset(idx))
    }

    /// Read a 64-bit `always_ff` state snapshot register `OBEND_STATE_SNAP[idx]` (`idx in 0..32`).
    pub fn read_state_snap(&self, idx: usize) -> Result<u64, FpgaHalError> {
        self.backend.read_csr64(csr::state_snap_offset(idx))
    }

    /// Submit a 7-section `SiliconElabWireFrame` (`OBCAMv1`) over 512-bit AXI4-Stream DMA,
    /// step the 4-zone Silicon Elaborator fabric, and return the resulting `SiliconTelemetry`.
    pub fn run_silicon_elab_frame(
        &mut self,
        frame: &SiliconElabWireFrame,
        cycles: u32,
    ) -> Result<SiliconTelemetry, FpgaHalError> {
        let beats = frame.to_axi_beats();
        self.backend.push_dma_beats(&beats)?;
        self.backend.step_cycles(cycles.max(3))?;
        self.backend.read_telemetry()
    }

    /// Decode a raw `ByteArray` produced by Lean's `Obend.Lower.ExprCAM.serializeSiliconWireFrame`
    /// (`OBCAMv1` LEB128 varint protocol) and execute it on the active backend.
    pub fn run_lean_wire_bytes(
        &mut self,
        lean_bytes: &[u8],
        cycles: u32,
    ) -> Result<SiliconTelemetry, FpgaHalError> {
        let (_hdr, frame) = SiliconElabWireFrame::from_lean_wire_bytes(lean_bytes).ok_or_else(
            || FpgaHalError::WireDecode("invalid Lean OBCAMv1 LEB128 wire frame".to_string()),
        )?;
        self.run_silicon_elab_frame(&frame, cycles)
    }

    /// Execute a 3-phase glitch-free ICAP Dynamic Partial Reconfiguration (`obend_macro_icap_dpr_tile`)
    /// hot-swap:
    /// 1. **Phase 1 (Isolate)**: Assert `DPR_ISOLATE_EN` in `OBEND_CTRL` (`0x0010`) so `skid_held_q`
    ///    holds active datapath outputs glitch-free while the shadow LUT/carry frame loads.
    /// 2. **Phase 2 (Stream & Guard Check)**: Write `OBEND_DPR_SLOT_GUARD_PIN` (`0x0030`) and stream
    ///    the 512-bit ICAP frame beat (`frame_word`, `expected_digest`, `computed_digest`).
    /// 3. **Phase 3 (De-Isolate & Commit/Fallback)**: De-assert `DPR_ISOLATE_EN`; if
    ///    `expected_digest == computed_digest && !moved_pin_violation`, commit the shadow frame,
    ///    otherwise activate the 1-cycle fallback (`DPR_FALLBACK_ACTIVE`) per
    ///    `quotientHypergraph_moved_pin_blocks`.
    pub fn perform_icap_dpr_hot_swap(
        &mut self,
        slot_name: impl Into<String>,
        frame_word: u64,
        expected_digest: u64,
        computed_digest: u64,
        moved_pin_violation: bool,
    ) -> Result<IcapDprSwapReceipt, FpgaHalError> {
        let slot_name = slot_name.into();

        // Phase 1: Assert DPR_ISOLATE_EN
        let ctrl0 = self.backend.read_csr32(csr::OBEND_CTRL)?;
        self.backend
            .write_csr32(csr::OBEND_CTRL, ctrl0 | ctrl_bits::DPR_ISOLATE_EN)?;
        self.backend
            .write_csr32(csr::OBEND_DPR_SLOT_GUARD_PIN, u32::from(moved_pin_violation))?;

        // Phase 2: Stream ICAP configuration beat while isolated, and verify outputs stay held
        let mut dpr_beat = AxiStream512Beat::default();
        dpr_beat.tlast = true;
        dpr_beat.set_word64(0, frame_word);
        dpr_beat.set_word64(1, expected_digest);
        dpr_beat.set_word64(2, computed_digest);
        self.backend.push_dma_beats(&[dpr_beat])?;
        self.backend.step_cycles(1)?;
        let held_out0 = self.read_out_port(0)?;

        // Phase 3: De-assert DPR_ISOLATE_EN and commit or trigger 1-cycle fallback
        let commit_ok = (expected_digest == computed_digest) && !moved_pin_violation;
        let mut ctrl_post = ctrl0 & !ctrl_bits::DPR_ISOLATE_EN;
        if commit_ok {
            ctrl_post &= !ctrl_bits::DPR_FALLBACK_ACTIVE;
        } else {
            ctrl_post |= ctrl_bits::DPR_FALLBACK_ACTIVE;
        }
        self.backend.write_csr32(csr::OBEND_CTRL, ctrl_post)?;
        self.backend.step_cycles(1)?;

        Ok(IcapDprSwapReceipt {
            slot_name,
            frame_word,
            expected_digest,
            computed_digest,
            moved_pin_violation,
            committed: commit_ok,
            fallback_activated: !commit_ok,
            held_output_port0_during_isolation: held_out0,
        })
    }

    pub fn step_cycles(&mut self, num_cycles: u32) -> Result<u64, FpgaHalError> {
        self.backend.step_cycles(num_cycles)
    }

    pub fn read_telemetry(&self) -> Result<SiliconTelemetry, FpgaHalError> {
        self.backend.read_telemetry()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::regs::{
        encode_lean_varint, HwPackedNodeWord88, PackedNodeWord88, OBCAM_WIRE_MAGIC,
    };

    #[test]
    fn test_bar0_magic_and_physical_obend_cores_in_sim() {
        let mut hal = ObendFpgaHal::new_sim().expect("SimBackend init");
        assert_eq!(hal.verify_magic().unwrap(), OBEND_MAGIC_F20);

        // Drive CleanroomTcadStack (port 0 = 4), LcDrivesStator (port 1 = 8), Cnc5AxisMill (port 2 = 6)
        hal.write_in_port(0, 4).unwrap();
        hal.write_in_port(1, 8).unwrap();
        hal.write_in_port(2, 6).unwrap();
        hal.step_cycles(2).unwrap();

        // CleanroomTcadStack outputs
        assert_eq!(hal.read_out_port(0).unwrap(), 700);
        assert_eq!(hal.read_out_port(1).unwrap(), 250);
        assert_eq!(hal.read_out_port(2).unwrap(), 270);
        assert_eq!(hal.read_out_port(3).unwrap(), 56);
        assert_eq!(hal.read_out_port(4).unwrap(), 72);
        assert_eq!(hal.read_state_snap(4).unwrap(), 72);
        // Verify full 32-entry OBEND_STATE_SNAP[0..31] including index 31 without collision
        assert_eq!(hal.read_state_snap(31).unwrap(), 0);

        // LcDrivesStator outputs
        assert_eq!(hal.read_out_port(5).unwrap(), 395);
        assert_eq!(hal.read_out_port(6).unwrap(), 34);
        assert_eq!(hal.read_out_port(7).unwrap(), 9);
        assert_eq!(hal.read_out_port(8).unwrap(), 24);
        assert_eq!(hal.read_out_port(9).unwrap(), 122);

        // Cnc5AxisMill outputs
        assert_eq!(hal.read_out_port(10).unwrap(), 6);
        assert_eq!(hal.read_out_port(11).unwrap(), 12);
        assert_eq!(hal.read_out_port(12).unwrap(), 6);
        assert_eq!(hal.read_out_port(13).unwrap(), 10024);
        assert_eq!(hal.read_out_port(14).unwrap(), 26);
    }

    #[test]
    fn test_obcamv1_7section_wire_frame_roundtrip_and_4zone_execution() {
        let mut frame = SiliconElabWireFrame::new(0x1001, 0x1001, 0x0204, 512);
        let node = PackedNodeWord88 {
            opcode: 0x04,
            binder_depth: 2,
            child0: 0x1001,
            child1: 0x1001,
        };
        // Push two identical nodes back-to-back to exercise Zone 1 UltraRAM RAW collision bypass & CAM hit
        frame.cam_nodes.push(node);
        frame.cam_nodes.push(node);
        frame.env_decls.push((10, 0x1001, 0x1002));
        frame.inductive_rules.push((20, 21, 1, 0));
        frame.quot_entries.push([1, 2, 3, 4]);
        frame.discr_trie_entries.push((0x1001, 0x0204, 42));
        frame.unify_worklist.push((0x1001, 0x1001));
        frame.infer_seeds.push((0x1001, 0x1001));

        let beats = frame.to_axi_beats();
        assert!(beats.len() >= 2);
        let decoded = SiliconElabWireFrame::from_axi_beats(&beats).expect("decode OBCAMv1");
        assert_eq!(decoded.cam_nodes, frame.cam_nodes);
        assert_eq!(decoded.env_decls, frame.env_decls);
        assert_eq!(decoded.inductive_rules, frame.inductive_rules);
        assert_eq!(decoded.quot_entries, frame.quot_entries);
        assert_eq!(decoded.discr_trie_entries, frame.discr_trie_entries);
        assert_eq!(decoded.unify_worklist, frame.unify_worklist);
        assert_eq!(decoded.infer_seeds, frame.infer_seeds);

        let mut hal = ObendFpgaHal::new_sim().unwrap();
        let telem = hal.run_silicon_elab_frame(&frame, 4).unwrap();
        assert!(telem.kernel_accepted);
        assert!(telem.cam_allocs >= 1);
        assert!(telem.cam_hits >= 1);
        assert!(telem.uram_bypass_hits >= 1);
        assert!(telem.noc_flits >= 1);
        assert!(telem.discr_lut_hits >= 1);
        assert_ne!(telem.zone3_match_thm, 0);
    }

    #[test]
    fn test_icap_dpr_3phase_glitch_free_swap_and_moved_pin_fallback() {
        let mut hal = ObendFpgaHal::new_sim().unwrap();
        hal.write_in_port(0, 4).unwrap();
        hal.step_cycles(1).unwrap();
        assert_eq!(hal.read_out_port(0).unwrap(), 700);

        // 1. Valid 3-phase ICAP DPR swap (matching digest, moved_pin_violation = false)
        let receipt_ok = hal
            .perform_icap_dpr_hot_swap(
                "quotient_stator_slot",
                0xCAFE_BABE_1234_5678,
                0xABCD_EF01_2345_6789,
                0xABCD_EF01_2345_6789,
                false,
            )
            .unwrap();
        assert!(receipt_ok.committed);
        assert!(!receipt_ok.fallback_activated);
        assert_eq!(receipt_ok.held_output_port0_during_isolation, 700);

        // 2. Symmetry-breaking `.obend` override (moved_pin_violation = true) triggers 1-cycle fallback
        let receipt_fb = hal
            .perform_icap_dpr_hot_swap(
                "quotient_stator_slot",
                0xDEAD_BEEF_0000_0001,
                0xABCD_EF01_2345_6789,
                0xABCD_EF01_2345_6789,
                true,
            )
            .unwrap();
        assert!(!receipt_fb.committed);
        assert!(receipt_fb.fallback_activated);
        let telem = hal.read_telemetry().unwrap();
        assert!(telem.dpr_fallback_active);
    }

    #[test]
    fn test_aws_f2_backend_mock_device_mmio_xdma_and_bad_magic_rejection() {
        let tmp_dir =
            std::env::temp_dir().join(format!("obend_aws_f2_test_{}", std::process::id()));
        let mut f2 = AwsF2Backend::open_mock_in_dir(&tmp_dir).expect("open mock AWS F2");
        let cfg = f2.config().clone();

        // Populate 2 sequential C2H beats and verify pull_dma_beats advances without rewinding
        {
            use std::io::Write;
            let mut c2h_writer = std::fs::OpenOptions::new()
                .write(true)
                .truncate(true)
                .open(&cfg.xdma_c2h_path)
                .unwrap();
            let mut b0 = [0u8; 64];
            b0[0] = 0xAA;
            let mut b1 = [0u8; 64];
            b1[0] = 0x55;
            c2h_writer.write_all(&b0).unwrap();
            c2h_writer.write_all(&b1).unwrap();
            c2h_writer.flush().unwrap();
        }
        let first_pull = f2.pull_dma_beats(1).unwrap();
        assert_eq!(first_pull.len(), 1);
        assert_eq!(first_pull[0].tdata[0], 0xAA);
        let second_pull = f2.pull_dma_beats(1).unwrap();
        assert_eq!(second_pull.len(), 1);
        assert_eq!(second_pull[0].tdata[0], 0x55);

        let mut hal = ObendFpgaHal::from_backend(f2);
        assert_eq!(hal.backend_name(), "aws-f2-vu47p");
        assert_eq!(hal.verify_magic().unwrap(), OBEND_MAGIC_F20);

        hal.write_in_port(0, 200).unwrap();
        let frame = SiliconElabWireFrame::new(0x2001, 0x2001, 0x0101, 256);
        let telem = hal.run_silicon_elab_frame(&frame, 3).unwrap();
        assert!(telem.total_cycles >= 3);
        drop(hal);

        // Corrupt BAR0 magic and verify AwsF2Backend::open fails closed with InvalidMagic
        {
            let mut bad_ap = sim_backend::PosixShmAperture::open_existing_mmio(&cfg.bar0_path).unwrap();
            bad_ap.write_u64(csr::OBEND_MAGIC, 0xBAD0_BAD0_BAD0_BAD0);
        }
        let err = AwsF2Backend::open(cfg).err().expect("must reject bad magic");
        assert!(matches!(
            err,
            FpgaHalError::InvalidMagic {
                expected: OBEND_MAGIC_F20,
                found: 0xBAD0_BAD0_BAD0_BAD0
            }
        ));

        let _ = std::fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_hw_packed_node_word88_and_lean_leb128_wire_protocol() {
        // 1. Exact 88-bit hardware layout matching Obend.Lower.ExprCAM.packNodeWord88
        let hw = HwPackedNodeWord88 {
            tag: 0x0A,
            h0: 0x1234,
            h1: 0x5678,
            h2: 0x9ABC,
            sym_idx: 0x0042,
            has_loose_bvar: true,
            has_fvar: false,
            has_mvar: true,
            max_loose_bvar: 0x0007,
        };
        let packed = hw.pack_word88();
        assert_eq!((packed >> 84) & 0x0F, 0x0A);
        assert_eq!((packed >> 82) & 1, 1);
        assert_eq!((packed >> 81) & 1, 1);
        assert_eq!((packed >> 80) & 1, 0);
        assert_eq!((packed >> 64) & 0xFFFF, 0x0007);
        assert_eq!((packed >> 48) & 0xFFFF, 0x0042);
        assert_eq!((packed >> 32) & 0xFFFF, 0x9ABC);
        assert_eq!((packed >> 16) & 0xFFFF, 0x5678);
        assert_eq!(packed & 0xFFFF, 0x1234);
        assert_eq!(HwPackedNodeWord88::unpack_word88(packed), hw);
        let bytes11 = hw.to_le_bytes11();
        assert_eq!(HwPackedNodeWord88::from_le_bytes11(&bytes11), hw);

        // 2. Lean ExprCAM.serializeSiliconWireFrame LEB128 byte stream decode & execution
        let mut lean_bytes = Vec::new();
        encode_lean_varint(OBCAM_WIRE_MAGIC as u128, &mut lean_bytes); // magic
        encode_lean_varint(1, &mut lean_bytes); // version
        encode_lean_varint(0, &mut lean_bytes); // flags
        encode_lean_varint(2, &mut lean_bytes); // nodeCount
        encode_lean_varint(0, &mut lean_bytes); // symbolCount
        encode_lean_varint(0, &mut lean_bytes); // levelCount
        encode_lean_varint(1, &mut lean_bytes); // constCount
        encode_lean_varint(0, &mut lean_bytes); // recRuleCount
        encode_lean_varint(0, &mut lean_bytes); // lutEntryCount
        encode_lean_varint(0, &mut lean_bytes); // icapFrameCount
        encode_lean_varint(7, &mut lean_bytes); // targetDeclSymIdx
        encode_lean_varint(1, &mut lean_bytes); // targetExprHandle
        encode_lean_varint(2, &mut lean_bytes); // targetTypeHandle
        encode_lean_varint(4096, &mut lean_bytes); // fuelBudget
        encode_lean_varint(0xCAFE_BABE_u128, &mut lean_bytes); // envPinDigest64
        // Section 1 list length = 2
        encode_lean_varint(2, &mut lean_bytes);
        for _ in 0..2 {
            encode_lean_varint(hw.tag as u128, &mut lean_bytes);
            encode_lean_varint(hw.h0 as u128, &mut lean_bytes);
            encode_lean_varint(hw.h1 as u128, &mut lean_bytes);
            encode_lean_varint(hw.h2 as u128, &mut lean_bytes);
            encode_lean_varint(hw.sym_idx as u128, &mut lean_bytes);
            encode_lean_varint(1, &mut lean_bytes); // hasLooseBVar
            encode_lean_varint(0, &mut lean_bytes); // hasFVar
            encode_lean_varint(1, &mut lean_bytes); // hasMVar
            encode_lean_varint(hw.max_loose_bvar as u128, &mut lean_bytes);
        }

        let mut hal = ObendFpgaHal::new_sim().unwrap();
        let telem = hal.run_lean_wire_bytes(&lean_bytes, 4).unwrap();
        assert!(telem.kernel_accepted);
        assert!(telem.cam_allocs >= 1);
        assert!(telem.cam_hits >= 1);
    }

    #[test]
    fn test_edge_cases_corrupted_crc_bad_magic_and_oob_csr() {
        // 1. Empty beats slice returns None
        assert!(SiliconElabWireFrame::from_axi_beats(&[]).is_none());

        // 2. Corrupted payload byte fails CRC-32 verification
        let mut frame = SiliconElabWireFrame::new(0x10, 0x20, 0x30, 128);
        frame.unify_worklist.push((1, 2));
        let mut beats = frame.to_axi_beats();
        beats[1].tdata[0] ^= 0xFF;
        assert!(SiliconElabWireFrame::from_axi_beats(&beats).is_none());

        // 3. Corrupted wire magic fails header decode
        let mut bad_hdr_beats = frame.to_axi_beats();
        bad_hdr_beats[0].set_word64(0, 0xDEAD_BEEF_CAFE_BABE);
        assert!(SiliconElabWireFrame::from_axi_beats(&bad_hdr_beats).is_none());

        // 4. Out-of-bounds CSR access returns OutOfBounds error
        let mut sim = SimBackend::new().unwrap();
        assert!(matches!(
            sim.read_csr64(regs::SHM_APERTURE_BYTES),
            Err(FpgaHalError::OutOfBounds(_))
        ));
        assert!(matches!(
            sim.write_csr32(regs::SHM_APERTURE_BYTES, 1),
            Err(FpgaHalError::OutOfBounds(_))
        ));

        // 5. Digest mismatch during ICAP DPR triggers fallback (committed = false)
        let mut hal = ObendFpgaHal::new_sim().unwrap();
        let receipt_bad_digest = hal
            .perform_icap_dpr_hot_swap(
                "corrupted_bitstream_slot",
                0x1111_2222_3333_4444,
                0xAAAA_BBBB_CCCC_DDDD,
                0xAAAA_BBBB_CCCC_0000,
                false,
            )
            .unwrap();
        assert!(!receipt_bad_digest.committed);
        assert!(receipt_bad_digest.fallback_activated);
    }
}
