//! `obend-node::silicon_bridge` — Hardware-Accelerated Turn/Batch Verification &
//! Live Specialization Deoptimization (`SlotGuardReg` / 3-Phase ICAP DPR) via `obend-fpga-hal`.
//!
//! Implements `QUALIFICATION-AND-SILICON-LEAN.md` Mandate #6 & §3.1:
//! - Encodes BFT turn/batch & `drex-clearing@1` obligations into 7-section `OBCAMv1`
//!   (`SiliconElabWireFrame`) and Lean LEB128 wire frames (`HwPackedNodeWord88` / `PackedNodeWord88`).
//! - Executes 4-zone Silicon Elaborator verification on `ObendFpgaHal` (`auto_connect()` / `new_sim()`),
//!   returning dated `DatedSiliconReceipt` telemetry recorded alongside finalized BFT receipts.
//! - Enforces `SlotGuardReg` live specialization deoptimization via `perform_icap_dpr_hot_swap`:
//!   - Triggers a 1-cycle `moved_pin_violation` / digest-mismatch fallback (`fallback_activated == true`,
//!     glitch-free `held_output_port0_during_isolation` skid clamp) when a stale or unauthorized law/schema
//!     pin arrives.
//!   - Executes a clean 3-phase glitch-free ICAP DPR commit (`committed == true`,
//!     `fallback_activated == false`) when an authorized `"world-carry@1"` (`K-CARRY`) upgrade commits
//!     across the BFT quorum.

use crate::judge_witness::JudgeWitnessError;
use crate::net::VaultTurn;
use crate::{cshake256_domain, DrexClearingCertificate, LimitOrder};
pub use obend_fpga_hal::regs::{
    encode_lean_varint, simple_crc32, HwPackedNodeWord88, ObcamWireHeader, PackedNodeWord88,
    SiliconElabWireFrame, OBCAM_WIRE_MAGIC, OBEND_MAGIC_F20,
};
pub use obend_fpga_hal::{
    FpgaHalBackend, FpgaHalError, IcapDprSwapReceipt, ObendFpgaHal, SiliconTelemetry,
};
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

/// Current wall-clock timestamp in milliseconds since `UNIX_EPOCH` for dating `SiliconTelemetry`.
pub fn current_unix_timestamp_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(1)
        .max(1)
}

/// Derive a deterministic non-zero 64-bit ICAP DPR configuration frame word from `(epoch_id, law_pin_digest)`.
pub fn derive_icap_frame_word(epoch_id: u64, slot_name: &str, law_pin_digest: u64) -> u64 {
    let mut left = [0u8; 16];
    left[..8].copy_from_slice(&epoch_id.to_be_bytes());
    left[8..16].copy_from_slice(&law_pin_digest.to_be_bytes());
    let digest = cshake256_domain(b"obend.node.icap.frame_word", &left, slot_name.as_bytes());
    let mut word_bytes = [0u8; 8];
    word_bytes.copy_from_slice(&digest[..8]);
    u64::from_be_bytes(word_bytes) | 1
}

/// Dated hardware verification receipt pairing `SiliconTelemetry` with BAR0 port/snapshot samples
/// and active law/schema pin metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DatedSiliconReceipt {
    pub recorded_at_unix_ms: u64,
    pub epoch_id: u64,
    pub block_height: u64,
    pub active_slot_name: String,
    pub law_pin_digest: u64,
    pub wire_frame_crc32: u32,
    pub bar0_port0_out: u64,
    pub bar0_state_snap4: u64,
    pub telemetry: SiliconTelemetry,
}

/// Errors raised by `NodeSiliconAccelerator` during `SlotGuardReg` checking, ICAP DPR hot-swap,
/// or 4-zone `OBCAMv1` proof/obligation verification.
#[derive(Debug, thiserror::Error)]
pub enum SiliconSlotGuardError {
    #[error(
        "SlotGuardReg 1-cycle deoptimization fallback triggered: active law pin 0x{expected_pin:016x} != observed pin 0x{observed_pin:016x}"
    )]
    StaleOrUnauthorizedPinFallback {
        expected_pin: u64,
        observed_pin: u64,
        receipt: IcapDprSwapReceipt,
        post_telemetry: SiliconTelemetry,
    },

    #[error(
        "ICAP DPR bitstream digest mismatch on slot '{slot_name}': expected 0x{expected_digest:016x}, computed 0x{computed_digest:016x}"
    )]
    DigestMismatchFallback {
        slot_name: String,
        expected_digest: u64,
        computed_digest: u64,
        receipt: IcapDprSwapReceipt,
        post_telemetry: SiliconTelemetry,
    },

    #[error(
        "4-zone Silicon Elaborator rejected OBCAMv1 frame at epoch {epoch_id} height {block_height}"
    )]
    HardwareKernelRejected {
        epoch_id: u64,
        block_height: u64,
        telemetry: SiliconTelemetry,
    },

    #[error("turn judge witness rejected before hardware execution: {0}")]
    WitnessRejected(#[from] JudgeWitnessError),

    #[error("FPGA HAL error: {0}")]
    Hal(#[from] FpgaHalError),
}

/// Construct a deterministic 7-section `SiliconElabWireFrame` (`OBCAMv1`) binding a BFT block/batch's
/// active law pin, `VaultTurn` footprints, `LimitOrder` book, and `DrexClearingCertificate` obligations.
pub fn build_turn_obcam_wire_frame(
    epoch_id: u64,
    block_height: u64,
    law_pin_digest: u64,
    turns: &[VaultTurn],
    orders: &[LimitOrder],
    clearing_cert: Option<&DrexClearingCertificate>,
) -> SiliconElabWireFrame {
    let mut meta = [0u8; 24];
    meta[0..8].copy_from_slice(&epoch_id.to_be_bytes());
    meta[8..16].copy_from_slice(&block_height.to_be_bytes());
    meta[16..24].copy_from_slice(&law_pin_digest.to_be_bytes());

    let clearing_bytes: &[u8] = clearing_cert
        .map(|c| c.digest.as_slice())
        .unwrap_or(b"no-clearing-cert");
    let frame_seed = cshake256_domain(b"obend.node.obcam.frame", &meta, clearing_bytes);

    let target_expr_h =
        (u32::from_le_bytes([frame_seed[0], frame_seed[1], frame_seed[2], frame_seed[3]])
            & 0x7FFF_FFFF)
            .max(1);
    let target_type_h =
        (u32::from_le_bytes([frame_seed[4], frame_seed[5], frame_seed[6], frame_seed[7]])
            & 0x7FFF_FFFF)
            .max(1);
    let target_decl_sym =
        (u32::from_le_bytes([frame_seed[8], frame_seed[9], frame_seed[10], frame_seed[11]])
            & 0x00FF_FFFF)
            .max(1);
    let witness_count: usize = turns.iter().map(|t| t.witnesses.len()).sum();
    let obligation_count =
        turns.len() + witness_count + orders.len() + usize::from(clearing_cert.is_some());
    let fuel_budget = 512u32.saturating_add((obligation_count as u32).saturating_mul(64));

    let mut frame =
        SiliconElabWireFrame::new(target_expr_h, target_type_h, target_decl_sym, fuel_budget);
    frame.header.flags = (epoch_id as u32) & 0xFFFF;

    // Root law/schema CAM node encoded via exact 88-bit `HwPackedNodeWord88` layout.
    // Pushed back-to-back to exercise Zone 1 UltraRAM RAW collision bypass & CAM deduplication hit.
    let law_lo = (law_pin_digest & 0xFFFF) as u16;
    let law_mid = ((law_pin_digest >> 16) & 0xFFFF) as u16;
    let law_hi = ((law_pin_digest >> 32) & 0xFFFF) as u16;
    let root_hw_node = HwPackedNodeWord88 {
        tag: 0x04,
        h0: law_lo.max(1),
        h1: law_mid.max(1),
        h2: law_hi.max(1),
        sym_idx: ((epoch_id & 0x7FFF) as u16).max(1),
        has_loose_bvar: false,
        has_fvar: false,
        has_mvar: false,
        max_loose_bvar: 0,
    };
    let root_cam_node = root_hw_node.to_cam_node();
    frame.cam_nodes.push(root_cam_node);
    frame.cam_nodes.push(root_cam_node);

    // Section 2: Environment declarations for active law pin
    frame
        .env_decls
        .push((target_decl_sym, target_type_h, target_expr_h));

    // Section 3: Inductive rules for `ZoeSeat` & `CarryClearingCell`
    frame
        .inductive_rules
        .push((0xD2E8_0001, 0xD2E8_0002, 3, 1));

    // Section 4: Quotient hypergraph pin handles
    frame.quot_entries.push([
        (epoch_id & 0xFFFF_FFFF) as u32,
        (block_height & 0xFFFF_FFFF) as u32,
        (law_pin_digest & 0xFFFF_FFFF) as u32,
        ((law_pin_digest >> 32) & 0xFFFF_FFFF) as u32,
    ]);

    // Encode each `VaultTurn` footprint obligation and its cited `TurnJudgeWitness` certificates
    let mut witness_sym_cursor = 1000u16;
    for (idx, turn) in turns.iter().enumerate() {
        let td = turn.digest();
        let h0 = u16::from_le_bytes([td[0], td[1]]).max(1);
        let h1 = u16::from_le_bytes([td[2], td[3]]).max(1);
        let h2 = (turn.read_slots.len() as u16)
            .wrapping_add((turn.write_slots.len() as u16) << 8)
            .max(1);
        let hw = HwPackedNodeWord88 {
            tag: 0x06,
            h0,
            h1,
            h2,
            sym_idx: (100 + idx as u16),
            has_loose_bvar: false,
            has_fvar: true,
            has_mvar: false,
            max_loose_bvar: 0,
        };
        frame.cam_nodes.push(hw.to_cam_node());
        let turn_handle = ((h0 as u32) << 16) | (h1 as u32);
        frame
            .env_decls
            .push((100 + idx as u32, target_type_h, turn_handle));
        frame
            .discr_trie_entries
            .push((turn_handle, target_decl_sym, 100 + idx as u32));
        frame.unify_worklist.push((turn_handle, target_expr_h));
        frame.infer_seeds.push((turn_handle, target_type_h));

        for w in &turn.witnesses {
            let wd = w.digest();
            let wh0 = u16::from_le_bytes([wd[0], wd[1]]).max(1);
            let wh1 = u16::from_le_bytes([wd[2], wd[3]]).max(1);
            let wh2 = (w.grade.min(u16::MAX as u32) as u16).max(1);
            let sym = witness_sym_cursor;
            witness_sym_cursor = witness_sym_cursor.saturating_add(1);
            let w_hw = HwPackedNodeWord88 {
                tag: 0x0C,
                h0: wh0,
                h1: wh1,
                h2: wh2,
                sym_idx: sym,
                has_loose_bvar: false,
                has_fvar: false,
                has_mvar: false,
                max_loose_bvar: 0,
            };
            frame.cam_nodes.push(w_hw.to_cam_node());
            let w_handle = ((wh0 as u32) << 16) | (wh1 as u32);
            frame
                .discr_trie_entries
                .push((w_handle, target_decl_sym, sym as u32));
            frame.unify_worklist.push((w_handle, turn_handle));
            frame.infer_seeds.push((w_handle, target_type_h));
        }
    }

    // Encode each `LimitOrder` obligation
    for (idx, order) in orders.iter().enumerate() {
        let acct_hash = cshake256_domain(
            b"obend.node.obcam.order",
            order.account.as_bytes(),
            &order.total.to_be_bytes(),
        );
        let h0 = (order.qty.min(u16::MAX as u64) as u16).max(1);
        let h1 = (order.total.min(u16::MAX as u64) as u16).max(1);
        let h2 = u16::from_le_bytes([acct_hash[0], acct_hash[1]]).max(1);
        let hw = HwPackedNodeWord88 {
            tag: 0x08,
            h0,
            h1,
            h2,
            sym_idx: (500 + idx as u16),
            has_loose_bvar: false,
            has_fvar: false,
            has_mvar: false,
            max_loose_bvar: 0,
        };
        frame.cam_nodes.push(hw.to_cam_node());
        let ord_handle = ((h2 as u32) << 16) | (h0 as u32);
        frame.unify_worklist.push((ord_handle, target_expr_h));
    }

    // Encode `DrexClearingCertificate` primal-dual conservation obligation
    if let Some(cert) = clearing_cert {
        let c0 = u16::from_le_bytes([cert.digest[0], cert.digest[1]]).max(1);
        let c1 = (cert.price.min(u16::MAX as u64) as u16).max(1);
        let c2 = (cert.fills.len() as u16).max(1);
        let hw = HwPackedNodeWord88 {
            tag: 0x0A,
            h0: c0,
            h1: c1,
            h2: c2,
            sym_idx: 0xD2E8,
            has_loose_bvar: false,
            has_fvar: false,
            has_mvar: false,
            max_loose_bvar: 0,
        };
        let node = hw.to_cam_node();
        frame.cam_nodes.push(node);
        let cert_handle = ((c0 as u32) << 16) | (c1 as u32);
        frame
            .discr_trie_entries
            .push((cert_handle, 0xD2E8, 0xD2E8_0001));
        frame.unify_worklist.push((cert_handle, cert_handle));
        frame.infer_seeds.push((cert_handle, target_type_h));
    }

    // Ensure non-empty discrimination tree, unification worklist, and inference seed sections
    // even for heartbeat / empty-order blocks so all 4 fabric zones execute deterministically.
    if frame.discr_trie_entries.is_empty() {
        frame
            .discr_trie_entries
            .push((target_expr_h, target_decl_sym, 1));
    }
    if frame.unify_worklist.is_empty() {
        frame.unify_worklist.push((target_expr_h, target_expr_h));
    }
    if frame.infer_seeds.is_empty() {
        frame.infer_seeds.push((target_expr_h, target_type_h));
    }

    frame
}

/// Encode a Lean `Obend.Lower.ExprCAM.serializeSiliconWireFrame` LEB128 byte stream for a package
/// law pin and slice of `HwPackedNodeWord88` nodes (`OBCAMv1` LEB128 wire protocol).
pub fn encode_lean_obcam_wire_bytes(
    epoch_id: u64,
    law_pin_digest: u64,
    hw_nodes: &[HwPackedNodeWord88],
) -> Vec<u8> {
    let mut out = Vec::new();
    encode_lean_varint(OBCAM_WIRE_MAGIC as u128, &mut out); // magic
    encode_lean_varint(1, &mut out); // version
    encode_lean_varint((epoch_id & 0xFFFF) as u128, &mut out); // flags
    encode_lean_varint(hw_nodes.len() as u128, &mut out); // nodeCount
    encode_lean_varint(4, &mut out); // symbolCount (4 .obend modules)
    encode_lean_varint(1, &mut out); // levelCount
    encode_lean_varint(6, &mut out); // constCount (6 package laws)
    encode_lean_varint(1, &mut out); // recRuleCount
    encode_lean_varint(4, &mut out); // lutEntryCount
    encode_lean_varint(1, &mut out); // icapFrameCount
    encode_lean_varint((epoch_id.max(1)) as u128, &mut out); // targetDeclSymIdx
    encode_lean_varint(1, &mut out); // targetExprHandle
    encode_lean_varint(2, &mut out); // targetTypeHandle
    encode_lean_varint(2048, &mut out); // fuelBudget
    encode_lean_varint(law_pin_digest as u128, &mut out); // envPinDigest64

    encode_lean_varint(hw_nodes.len() as u128, &mut out);
    for hw in hw_nodes {
        encode_lean_varint(hw.tag as u128, &mut out);
        encode_lean_varint(hw.h0 as u128, &mut out);
        encode_lean_varint(hw.h1 as u128, &mut out);
        encode_lean_varint(hw.h2 as u128, &mut out);
        encode_lean_varint(hw.sym_idx as u128, &mut out);
        encode_lean_varint(u128::from(hw.has_loose_bvar), &mut out);
        encode_lean_varint(u128::from(hw.has_fvar), &mut out);
        encode_lean_varint(u128::from(hw.has_mvar), &mut out);
        encode_lean_varint(hw.max_loose_bvar as u128, &mut out);
    }
    out
}

/// Per-validator hardware accelerator controller coupling `ObendFpgaHal` with `SlotGuardReg`
/// pin enforcement and 3-phase glitch-free ICAP Dynamic Partial Reconfiguration.
pub struct NodeSiliconAccelerator {
    hal: ObendFpgaHal,
    active_slot_name: String,
    active_epoch_id: u64,
    active_law_pin_digest: u64,
    active_frame_word: u64,
    swap_history: Vec<IcapDprSwapReceipt>,
    receipt_history: Vec<DatedSiliconReceipt>,
}

impl NodeSiliconAccelerator {
    /// Auto-connect to `AwsF2Backend` (when `OBEND_FPGA_BACKEND=aws-f2` and `/dev/fpga0` exists)
    /// or `SimBackend` (`ObendFpgaHal::auto_connect()`), verify BAR0 magic, prime BAR0 ports,
    /// and commit the initial DPR specialization slot.
    pub fn auto_connect(
        initial_slot: impl Into<String>,
        initial_law_pin_digest: u64,
    ) -> Result<Self, FpgaHalError> {
        let hal = ObendFpgaHal::auto_connect()?;
        Self::from_hal(hal, initial_slot, initial_law_pin_digest)
    }

    /// Construct a `NodeSiliconAccelerator` backed explicitly by `ObendFpgaHal::new_sim()`.
    pub fn new_sim(
        initial_slot: impl Into<String>,
        initial_law_pin_digest: u64,
    ) -> Result<Self, FpgaHalError> {
        let hal = ObendFpgaHal::new_sim()?;
        Self::from_hal(hal, initial_slot, initial_law_pin_digest)
    }

    /// Wrap an existing `ObendFpgaHal`, verify `OBEND_MAGIC_F20`, prime BAR0 I/O ports so
    /// `OBEND_OUT_PORT[0] == 700` and `OBEND_STATE_SNAP[4] == 72` are latched into the skid-buffer
    /// isolation fence, and load the genesis DPR bitstream slot.
    pub fn from_hal(
        mut hal: ObendFpgaHal,
        initial_slot: impl Into<String>,
        initial_law_pin_digest: u64,
    ) -> Result<Self, FpgaHalError> {
        let slot_name = initial_slot.into();
        let pin = initial_law_pin_digest.max(1);
        hal.verify_magic()?;

        // Prime physical `.obend` BAR0 cores so skid-buffer isolation holds non-zero steady outputs (700)
        hal.write_in_port(0, 4)?;
        hal.write_in_port(1, 8)?;
        hal.write_in_port(2, 6)?;
        hal.step_cycles(2)?;

        let frame_word = derive_icap_frame_word(1, &slot_name, pin);
        let init_receipt = hal.perform_icap_dpr_hot_swap(
            slot_name.clone(),
            frame_word,
            pin,
            pin,
            false,
        )?;

        Ok(Self {
            hal,
            active_slot_name: slot_name,
            active_epoch_id: 1,
            active_law_pin_digest: pin,
            active_frame_word: frame_word,
            swap_history: vec![init_receipt],
            receipt_history: Vec::new(),
        })
    }

    pub fn hal(&self) -> &ObendFpgaHal {
        &self.hal
    }

    pub fn hal_mut(&mut self) -> &mut ObendFpgaHal {
        &mut self.hal
    }

    pub fn backend_name(&self) -> &'static str {
        self.hal.backend_name()
    }

    pub fn active_slot_name(&self) -> &str {
        &self.active_slot_name
    }

    pub fn active_epoch_id(&self) -> u64 {
        self.active_epoch_id
    }

    pub fn active_law_pin_digest(&self) -> u64 {
        self.active_law_pin_digest
    }

    pub fn active_frame_word(&self) -> u64 {
        self.active_frame_word
    }

    pub fn swap_history(&self) -> &[IcapDprSwapReceipt] {
        &self.swap_history
    }

    pub fn receipt_history(&self) -> &[DatedSiliconReceipt] {
        &self.receipt_history
    }

    pub fn latest_receipt(&self) -> Option<&DatedSiliconReceipt> {
        self.receipt_history.last()
    }

    pub fn read_telemetry(&self) -> Result<SiliconTelemetry, FpgaHalError> {
        self.hal.read_telemetry()
    }

    /// Re-arm the currently authorized DPR specialization slot (clearing `DPR_FALLBACK_ACTIVE`
    /// if a prior rejected stale/unauthorized pin probe triggered the 1-cycle `SlotGuardReg` clamp).
    pub fn rearm_active_slot(&mut self) -> Result<IcapDprSwapReceipt, FpgaHalError> {
        let receipt = self.hal.perform_icap_dpr_hot_swap(
            self.active_slot_name.clone(),
            self.active_frame_word,
            self.active_law_pin_digest,
            self.active_law_pin_digest,
            false,
        )?;
        self.swap_history.push(receipt.clone());
        Ok(receipt)
    }

    /// Execute a 3-phase glitch-free ICAP Dynamic Partial Reconfiguration hot-swap (`perform_icap_dpr_hot_swap`)
    /// for a law/schema transition (`"world-carry@1"` `K-CARRY`) or test an unauthorized/corrupted frame:
    /// - If `moved_pin_violation == true`, triggers 1-cycle `SlotGuardReg` fallback (`committed == false`,
    ///   `fallback_activated == true`, `held_output_port0_during_isolation` held glitch-free) and returns
    ///   `Err(SiliconSlotGuardError::StaleOrUnauthorizedPinFallback)` without mutating `active_law_pin_digest`.
    /// - If `expected_digest != computed_digest`, triggers 1-cycle digest-mismatch fallback and returns
    ///   `Err(SiliconSlotGuardError::DigestMismatchFallback)` without mutating `active_law_pin_digest`.
    /// - Otherwise commits the new specialization slot (`committed == true`, `fallback_activated == false`)
    ///   and advances `(active_epoch_id, active_slot_name, active_law_pin_digest, active_frame_word)`.
    pub fn hot_swap_law_pin(
        &mut self,
        new_epoch_id: u64,
        slot_name: impl Into<String>,
        frame_word: u64,
        expected_digest: u64,
        computed_digest: u64,
        moved_pin_violation: bool,
    ) -> Result<IcapDprSwapReceipt, SiliconSlotGuardError> {
        let slot_name = slot_name.into();
        let receipt = self.hal.perform_icap_dpr_hot_swap(
            slot_name.clone(),
            frame_word,
            expected_digest,
            computed_digest,
            moved_pin_violation,
        )?;
        self.swap_history.push(receipt.clone());

        if moved_pin_violation {
            let post_telemetry = self.hal.read_telemetry()?;
            return Err(SiliconSlotGuardError::StaleOrUnauthorizedPinFallback {
                expected_pin: self.active_law_pin_digest,
                observed_pin: computed_digest,
                receipt,
                post_telemetry,
            });
        }
        if !receipt.committed || receipt.fallback_activated || expected_digest != computed_digest {
            let post_telemetry = self.hal.read_telemetry()?;
            return Err(SiliconSlotGuardError::DigestMismatchFallback {
                slot_name,
                expected_digest,
                computed_digest,
                receipt,
                post_telemetry,
            });
        }

        self.active_epoch_id = new_epoch_id;
        self.active_slot_name = slot_name;
        self.active_law_pin_digest = expected_digest.max(1);
        self.active_frame_word = frame_word;
        Ok(receipt)
    }

    /// Verify Lean `OBCAMv1` LEB128 wire bytes directly on the underlying `ObendFpgaHal`.
    pub fn verify_lean_obcam_bytes(
        &mut self,
        lean_bytes: &[u8],
        cycles: u32,
    ) -> Result<SiliconTelemetry, SiliconSlotGuardError> {
        let telem = self.hal.run_lean_wire_bytes(lean_bytes, cycles)?;
        if !telem.kernel_accepted {
            return Err(SiliconSlotGuardError::HardwareKernelRejected {
                epoch_id: self.active_epoch_id,
                block_height: 0,
                telemetry: telem,
            });
        }
        Ok(telem)
    }

    /// Hardware-verify a BFT turn/batch & `drex-clearing@1` obligation set against `SlotGuardReg`:
    /// 1. If `observed_law_pin_digest != self.active_law_pin_digest`, triggers a 1-cycle `SlotGuardReg`
    ///    deoptimization fallback via `perform_icap_dpr_hot_swap(..., moved_pin_violation = true)`
    ///    and fails closed with `StaleOrUnauthorizedPinFallback`.
    /// 2. Drives BAR0 input ports (`write_in_port`), submits the 7-section `OBCAMv1` `SiliconElabWireFrame`
    ///    over 512-bit AXI4-Stream DMA, samples `read_out_port(0)` and `read_state_snap(4)`, and returns
    ///    a dated `DatedSiliconReceipt`.
    pub fn verify_turn_or_batch(
        &mut self,
        epoch_id: u64,
        block_height: u64,
        observed_law_pin_digest: u64,
        turns: &[VaultTurn],
        orders: &[LimitOrder],
        clearing_cert: Option<&DrexClearingCertificate>,
    ) -> Result<DatedSiliconReceipt, SiliconSlotGuardError> {
        if observed_law_pin_digest != self.active_law_pin_digest {
            let stale_frame_word =
                derive_icap_frame_word(epoch_id, &self.active_slot_name, observed_law_pin_digest);
            let fb_receipt = self.hal.perform_icap_dpr_hot_swap(
                format!("{}:slot_guard_deopt", self.active_slot_name),
                stale_frame_word,
                self.active_law_pin_digest,
                observed_law_pin_digest,
                true,
            )?;
            self.swap_history.push(fb_receipt.clone());
            let post_telemetry = self.hal.read_telemetry()?;
            return Err(SiliconSlotGuardError::StaleOrUnauthorizedPinFallback {
                expected_pin: self.active_law_pin_digest,
                observed_pin: observed_law_pin_digest,
                receipt: fb_receipt,
                post_telemetry,
            });
        }

        for turn in turns {
            turn.verify_witnesses()?;
        }

        // If a previous unauthorized/stale pin probe latched `DPR_FALLBACK_ACTIVE`, re-validate and
        // re-arm the active authorized specialization slot before running this valid batch.
        if self.hal.read_telemetry()?.dpr_fallback_active {
            self.rearm_active_slot()?;
        }

        // Drive BAR0 input ports (keeping port 0 = 4 so CleanroomTcadStack port 0 = 700 stays primed)
        self.hal.write_in_port(0, 4)?;
        self.hal.write_in_port(3, epoch_id)?;
        self.hal.write_in_port(4, block_height)?;
        self.hal.write_in_port(5, observed_law_pin_digest)?;
        self.hal.write_in_port(6, orders.len() as u64)?;

        let frame = build_turn_obcam_wire_frame(
            epoch_id,
            block_height,
            observed_law_pin_digest,
            turns,
            orders,
            clearing_cert,
        );
        let beats = frame.to_axi_beats();
        let encoded_hdr = beats
            .first()
            .and_then(ObcamWireHeader::from_beat)
            .unwrap_or(frame.header);

        let telemetry = self.hal.run_silicon_elab_frame(&frame, 4)?;
        if !telemetry.kernel_accepted {
            return Err(SiliconSlotGuardError::HardwareKernelRejected {
                epoch_id,
                block_height,
                telemetry,
            });
        }

        let bar0_port0_out = self.hal.read_out_port(0)?;
        let bar0_state_snap4 = self.hal.read_state_snap(4)?;

        let receipt = DatedSiliconReceipt {
            recorded_at_unix_ms: current_unix_timestamp_ms(),
            epoch_id,
            block_height,
            active_slot_name: self.active_slot_name.clone(),
            law_pin_digest: self.active_law_pin_digest,
            wire_frame_crc32: encoded_hdr.payload_crc32,
            bar0_port0_out,
            bar0_state_snap4,
            telemetry,
        };
        self.receipt_history.push(receipt.clone());
        Ok(receipt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::OrderSide;

    #[test]
    fn test_silicon_accelerator_turn_telemetry_and_slot_guard_deopt() {
        let epoch1_pin = 0x1111_2222_3333_4444u64;
        let epoch2_pin = 0x9999_AAAA_BBBB_CCCCu64;

        let mut accel =
            NodeSiliconAccelerator::new_sim("sovereign_drex_epoch1", epoch1_pin).unwrap();
        assert_eq!(accel.active_law_pin_digest(), epoch1_pin);

        let turn = VaultTurn::new([7u8; 32], "alice", vec![1], vec![(2, b"escrow".to_vec())]);
        let orders = vec![
            LimitOrder {
                account: "alice".to_string(),
                side: OrderSide::Bid,
                qty: 10,
                total: 1000,
            },
            LimitOrder {
                account: "bob".to_string(),
                side: OrderSide::Ask,
                qty: 10,
                total: 980,
            },
        ];
        let cert = crate::solve_primal_dual_clearing("CBDC", "BOND", 0, &orders).unwrap();

        let receipt1 = accel
            .verify_turn_or_batch(1, 1, epoch1_pin, &[turn.clone()], &orders, Some(&cert))
            .expect("Epoch 1 hardware batch verification must succeed");
        assert!(receipt1.recorded_at_unix_ms > 0);
        assert!(receipt1.telemetry.kernel_accepted);
        assert!(receipt1.telemetry.total_cycles > 0);
        assert!(receipt1.telemetry.cam_hits >= 1);
        assert!(receipt1.telemetry.uram_bypass_hits >= 1);
        assert!(receipt1.telemetry.noc_flits >= 1);
        assert!(receipt1.telemetry.discr_lut_hits >= 1);
        assert!(!receipt1.telemetry.dpr_fallback_active);
        assert_eq!(receipt1.bar0_port0_out, 700);
        assert_eq!(receipt1.bar0_state_snap4, 72);

        // Authorized K-CARRY 3-phase glitch-free ICAP DPR hot-swap to Epoch 2
        let frame2 = derive_icap_frame_word(2, "sovereign_drex_epoch2", epoch2_pin);
        let swap_ok = accel
            .hot_swap_law_pin(
                2,
                "sovereign_drex_epoch2",
                frame2,
                epoch2_pin,
                epoch2_pin,
                false,
            )
            .expect("authorized K-CARRY DPR swap must commit");
        assert!(swap_ok.committed);
        assert!(!swap_ok.fallback_activated);
        assert_eq!(swap_ok.held_output_port0_during_isolation, 700);
        assert_eq!(accel.active_law_pin_digest(), epoch2_pin);

        // Stale Epoch 1 pin after upgrade triggers 1-cycle SlotGuardReg fallback
        let err = accel
            .verify_turn_or_batch(1, 2, epoch1_pin, &[turn.clone()], &orders, Some(&cert))
            .expect_err("stale pin must trigger SlotGuardReg fallback");
        match err {
            SiliconSlotGuardError::StaleOrUnauthorizedPinFallback {
                expected_pin,
                observed_pin,
                receipt,
                post_telemetry,
            } => {
                assert_eq!(expected_pin, epoch2_pin);
                assert_eq!(observed_pin, epoch1_pin);
                assert!(!receipt.committed);
                assert!(receipt.fallback_activated);
                assert!(receipt.moved_pin_violation);
                assert_eq!(receipt.held_output_port0_during_isolation, 700);
                assert!(post_telemetry.dpr_fallback_active);
            }
            other => panic!("unexpected error variant: {other:?}"),
        }
        assert!(accel.read_telemetry().unwrap().dpr_fallback_active);

        // Subsequent valid Epoch 2 batch re-arms the authorized Epoch 2 slot and succeeds
        let receipt2 = accel
            .verify_turn_or_batch(2, 2, epoch2_pin, &[turn], &orders, Some(&cert))
            .expect("valid Epoch 2 batch must succeed");
        assert!(receipt2.telemetry.kernel_accepted);
        assert!(!receipt2.telemetry.dpr_fallback_active);
        assert_eq!(receipt2.law_pin_digest, epoch2_pin);
    }
}
