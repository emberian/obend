//! Rung 1 Verilator Co-Simulation Backend (`SimBackend`):
//! POSIX 4 MiB Shared Memory (`mmap`) + Unix Domain Socket Lockstep Bridge +
//! Cycle-Accurate 4-Zone `silicon_elab_top` & ICAP DPR Co-Simulation Engine.

use crate::regs::{
    ctrl_bits, csr, AxiStream512Beat, ObcamWireHeader, PackedNodeWord88, SiliconElabWireFrame,
    OBCAM_WIRE_MAGIC, OBEND_MAGIC_F20, OBEND_VERSION_CAPS_DEFAULT, SHM_APERTURE_BYTES,
};
use crate::{FpgaHalBackend, FpgaHalError, SiliconTelemetry};
use std::collections::HashMap;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::io::AsRawFd;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::ptr;

/// POSIX `mmap`-backed 4 MiB BAR0 + DMA ring aperture.
pub struct PosixShmAperture {
    ptr: *mut u8,
    len: usize,
    backing_path: Option<PathBuf>,
}

// Safety: `PosixShmAperture` owns its exclusively mapped region or synchronizes via `SimBackend`.
unsafe impl Send for PosixShmAperture {}
unsafe impl Sync for PosixShmAperture {}

impl PosixShmAperture {
    /// Create an anonymous 4 MiB `mmap` aperture (`MAP_SHARED | MAP_ANON`).
    pub fn new_anonymous() -> Result<Self, FpgaHalError> {
        let len = SHM_APERTURE_BYTES;
        let ptr = unsafe {
            libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if ptr == libc::MAP_FAILED {
            return Err(FpgaHalError::Io("mmap(MAP_ANON) failed".to_string()));
        }
        let mut ap = Self {
            ptr: ptr as *mut u8,
            len,
            backing_path: None,
        };
        ap.init_header();
        Ok(ap)
    }

    /// Create or open a file-backed 4 MiB `mmap` aperture for cross-process Verilator IPC.
    pub fn open_file_backed(path: impl AsRef<Path>) -> Result<Self, FpgaHalError> {
        let path_buf = path.as_ref().to_path_buf();
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path_buf)
            .map_err(|e| FpgaHalError::Io(format!("open {:?}: {}", path_buf, e)))?;
        file.set_len(SHM_APERTURE_BYTES as u64)
            .map_err(|e| FpgaHalError::Io(format!("ftruncate {:?}: {}", path_buf, e)))?;
        let ptr = unsafe {
            libc::mmap(
                ptr::null_mut(),
                SHM_APERTURE_BYTES,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                file.as_raw_fd(),
                0,
            )
        };
        if ptr == libc::MAP_FAILED {
            return Err(FpgaHalError::Io(format!("mmap({:?}) failed", path_buf)));
        }
        let mut ap = Self {
            ptr: ptr as *mut u8,
            len: SHM_APERTURE_BYTES,
            backing_path: Some(path_buf),
        };
        ap.init_header();
        Ok(ap)
    }

    /// Open an existing BAR0 MMIO device (`/dev/fpga0`) or pre-initialized mock BAR0 file
    /// WITHOUT overwriting its header (`OBEND_MAGIC`) or calling `ftruncate` on character devices.
    pub fn open_existing_mmio(path: impl AsRef<Path>) -> Result<Self, FpgaHalError> {
        let path_buf = path.as_ref().to_path_buf();
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path_buf)
            .map_err(|e| FpgaHalError::Io(format!("open MMIO {:?}: {}", path_buf, e)))?;
        if let Ok(meta) = file.metadata() {
            if meta.is_file() && (meta.len() as usize) < SHM_APERTURE_BYTES {
                file.set_len(SHM_APERTURE_BYTES as u64)
                    .map_err(|e| FpgaHalError::Io(format!("ftruncate {:?}: {}", path_buf, e)))?;
            }
        }
        let ptr = unsafe {
            libc::mmap(
                ptr::null_mut(),
                SHM_APERTURE_BYTES,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                file.as_raw_fd(),
                0,
            )
        };
        if ptr == libc::MAP_FAILED {
            return Err(FpgaHalError::Io(format!("mmap({:?}) failed", path_buf)));
        }
        Ok(Self {
            ptr: ptr as *mut u8,
            len: SHM_APERTURE_BYTES,
            backing_path: Some(path_buf),
        })
    }

    fn init_header(&mut self) {
        self.write_u64(csr::OBEND_MAGIC, OBEND_MAGIC_F20);
        self.write_u64(csr::OBEND_VERSION_CAPS, OBEND_VERSION_CAPS_DEFAULT);
        self.write_u32(csr::FUEL_BUDGET, 1024);
    }

    pub fn backing_path(&self) -> Option<&Path> {
        self.backing_path.as_deref()
    }

    #[inline]
    pub fn read_u32(&self, offset: usize) -> u32 {
        assert!(offset + 4 <= self.len);
        let mut bytes = [0u8; 4];
        unsafe {
            ptr::copy_nonoverlapping(self.ptr.add(offset), bytes.as_mut_ptr(), 4);
        }
        u32::from_le_bytes(bytes)
    }

    #[inline]
    pub fn write_u32(&mut self, offset: usize, val: u32) {
        assert!(offset + 4 <= self.len);
        let bytes = val.to_le_bytes();
        unsafe {
            ptr::copy_nonoverlapping(bytes.as_ptr(), self.ptr.add(offset), 4);
        }
    }

    #[inline]
    pub fn read_u64(&self, offset: usize) -> u64 {
        assert!(offset + 8 <= self.len);
        let mut bytes = [0u8; 8];
        unsafe {
            ptr::copy_nonoverlapping(self.ptr.add(offset), bytes.as_mut_ptr(), 8);
        }
        u64::from_le_bytes(bytes)
    }

    #[inline]
    pub fn write_u64(&mut self, offset: usize, val: u64) {
        assert!(offset + 8 <= self.len);
        let bytes = val.to_le_bytes();
        unsafe {
            ptr::copy_nonoverlapping(bytes.as_ptr(), self.ptr.add(offset), 8);
        }
    }
}

impl Drop for PosixShmAperture {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe {
                libc::munmap(self.ptr as *mut libc::c_void, self.len);
            }
            self.ptr = ptr::null_mut();
        }
    }
}

/// Rung 1 Verilator Co-Simulation Backend (`SimBackend`).
pub struct SimBackend {
    shm: PosixShmAperture,
    unix_sock_path: Option<PathBuf>,
    cam_uram: HashMap<u16, (PackedNodeWord88, u32)>,
    last_write_bucket: Option<u16>,
    next_cam_handle: u32,
    tx_beats: Vec<AxiStream512Beat>,
    rx_beats: Vec<AxiStream512Beat>,
    shadow_dpr_digest: u64,
    skid_held_outputs: [u64; 32],
}

impl SimBackend {
    /// Create an in-process POSIX `mmap` simulation backend.
    pub fn new() -> Result<Self, FpgaHalError> {
        Ok(Self {
            shm: PosixShmAperture::new_anonymous()?,
            unix_sock_path: None,
            cam_uram: HashMap::new(),
            last_write_bucket: None,
            next_cam_handle: 1,
            tx_beats: Vec::new(),
            rx_beats: Vec::new(),
            shadow_dpr_digest: 0,
            skid_held_outputs: [0u64; 32],
        })
    }

    /// Create a file-backed `mmap` + optional Unix domain socket simulation backend.
    pub fn with_shm_and_socket(
        shm_path: impl AsRef<Path>,
        sock_path: Option<PathBuf>,
    ) -> Result<Self, FpgaHalError> {
        Ok(Self {
            shm: PosixShmAperture::open_file_backed(shm_path)?,
            unix_sock_path: sock_path,
            cam_uram: HashMap::new(),
            last_write_bucket: None,
            next_cam_handle: 1,
            tx_beats: Vec::new(),
            rx_beats: Vec::new(),
            shadow_dpr_digest: 0,
            skid_held_outputs: [0u64; 32],
        })
    }

    /// Notify an external Verilator Unix domain socket listener if configured.
    fn notify_verilator_daemon(&self, cmd: &[u8]) -> Result<(), FpgaHalError> {
        if let Some(ref sock_path) = self.unix_sock_path {
            if sock_path.exists() {
                let mut stream = UnixStream::connect(sock_path)
                    .map_err(|e| FpgaHalError::Io(format!("UnixStream connect {:?}: {}", sock_path, e)))?;
                stream
                    .write_all(cmd)
                    .map_err(|e| FpgaHalError::Io(format!("UnixStream write: {}", e)))?;
                let mut ack = [0u8; 4];
                let _ = stream.read(&mut ack);
            }
        }
        Ok(())
    }

    /// Execute one synchronous clock cycle of the 4-zone `silicon_elab_top` and `.obend` physical cores.
    fn step_one_cycle(&mut self) {
        let cycles = self.shm.read_u64(csr::OBEND_CYCLE_COUNT).wrapping_add(1);
        self.shm.write_u64(csr::OBEND_CYCLE_COUNT, cycles);

        let ctrl = self.shm.read_u32(csr::OBEND_CTRL);
        let isolated = (ctrl & ctrl_bits::DPR_ISOLATE_EN) != 0;

        // 1. Evaluate `.obend` physical cores (unless DPR isolation fence holds outputs)
        if !isolated {
            let tcad_in = self.shm.read_u64(csr::in_port_offset(0));
            let oxide = 700u64;
            let vth = 250u64;
            let idrain = tcad_in.wrapping_mul(5).wrapping_add(vth);
            let gdelay = tcad_in.wrapping_mul(8).wrapping_add(20).wrapping_add(4);
            let cdelay = tcad_in
                .wrapping_add(2)
                .wrapping_mul(8)
                .wrapping_add(20)
                .wrapping_add(4);

            self.shm.write_u64(csr::out_port_offset(0), oxide);
            self.shm.write_u64(csr::out_port_offset(1), vth);
            self.shm.write_u64(csr::out_port_offset(2), idrain);
            self.shm.write_u64(csr::out_port_offset(3), gdelay);
            self.shm.write_u64(csr::out_port_offset(4), cdelay);

            self.shm.write_u64(csr::state_snap_offset(0), oxide);
            self.shm.write_u64(csr::state_snap_offset(1), vth);
            self.shm.write_u64(csr::state_snap_offset(2), idrain);
            self.shm.write_u64(csr::state_snap_offset(3), gdelay);
            self.shm.write_u64(csr::state_snap_offset(4), cdelay);

            let stator_in = self.shm.read_u64(csr::in_port_offset(1));
            self.shm.write_u64(csr::out_port_offset(5), 395);
            self.shm
                .write_u64(csr::out_port_offset(6), stator_in.wrapping_mul(4).wrapping_add(2));
            self.shm.write_u64(csr::out_port_offset(7), 9);
            self.shm
                .write_u64(csr::out_port_offset(8), stator_in.wrapping_add(16));
            self.shm
                .write_u64(csr::out_port_offset(9), 50u64.wrapping_add(stator_in.wrapping_mul(9)));

            let mill_in = self.shm.read_u64(csr::in_port_offset(2));
            self.shm.write_u64(csr::out_port_offset(10), mill_in);
            self.shm
                .write_u64(csr::out_port_offset(11), mill_in.wrapping_mul(2));
            self.shm.write_u64(csr::out_port_offset(12), mill_in);
            self.shm.write_u64(
                csr::out_port_offset(13),
                10000u64.wrapping_add(mill_in.wrapping_mul(4)),
            );
            self.shm
                .write_u64(csr::out_port_offset(14), 20u64.wrapping_add(mill_in));

            for i in 0..32 {
                self.skid_held_outputs[i] = self.shm.read_u64(csr::out_port_offset(i));
            }
        } else {
            // While `DPR_ISOLATE_EN` is asserted, outputs are held glitch-free by the skid fence
            for i in 0..32 {
                self.shm
                    .write_u64(csr::out_port_offset(i), self.skid_held_outputs[i]);
            }
        }

        // 2. Evaluate 4-Zone Silicon Elaborator Fabric when `AP_START` is set
        let sil_ctrl = self.shm.read_u32(csr::SILICON_CTRL_STATUS);
        if (ctrl & ctrl_bits::AP_START) != 0 || (sil_ctrl & 1) != 0 {
            let expr_h = self.shm.read_u32(csr::TARGET_EXPR_H);
            let type_h = self.shm.read_u32(csr::TARGET_TYPE_H);
            let decl_sym = self.shm.read_u32(csr::TARGET_DECL_SYM);
            let fuel = self.shm.read_u32(csr::FUEL_BUDGET);

            let node = PackedNodeWord88 {
                opcode: (decl_sym & 0xFF) as u8,
                binder_depth: ((decl_sym >> 8) & 0xFFFF) as u16,
                child0: expr_h,
                child1: type_h,
            };
            let bucket = node.hash_bucket10();
            let bypass_hit = self.last_write_bucket == Some(bucket);
            if bypass_hit {
                let b = self.shm.read_u32(csr::PERF_BYPASS_CNT).wrapping_add(1);
                self.shm.write_u32(csr::PERF_BYPASS_CNT, b);
            }
            match self.cam_uram.get(&bucket) {
                Some(&(existing, _h)) if existing == node => {
                    let hits = self.shm.read_u32(csr::PERF_CAM_HITS).wrapping_add(1);
                    self.shm.write_u32(csr::PERF_CAM_HITS, hits);
                }
                _ => {
                    let h = self.next_cam_handle;
                    self.next_cam_handle = self.next_cam_handle.wrapping_add(1);
                    self.cam_uram.insert(bucket, (node, h));
                    self.last_write_bucket = Some(bucket);
                    let allocs = self.shm.read_u32(csr::PERF_CAM_ALLOCS).wrapping_add(1);
                    self.shm.write_u32(csr::PERF_CAM_ALLOCS, allocs);
                }
            }

            let flits = self.shm.read_u32(csr::PERF_NOC_FLITS).wrapping_add(1);
            self.shm.write_u32(csr::PERF_NOC_FLITS, flits);

            let lut_hits = self.shm.read_u32(csr::PERF_LUT_HITS).wrapping_add(1);
            self.shm.write_u32(csr::PERF_LUT_HITS, lut_hits);
            let match_thm = (expr_h ^ decl_sym) | 1;
            self.shm.write_u32(csr::ZONE3_MATCH_THM, match_thm);

            let pcycles = self.shm.read_u32(csr::PERF_CYCLES).wrapping_add(3);
            self.shm.write_u32(csr::PERF_CYCLES, pcycles);

            let accepted = fuel > 0 && expr_h != 0 && type_h != 0;
            let fallback_bit = if (ctrl & ctrl_bits::DPR_FALLBACK_ACTIVE) != 0 {
                4u32
            } else {
                0u32
            };
            let res_status = fallback_bit | (if accepted { 2 } else { 0 }) | 1;
            self.shm.write_u32(csr::RESULT_STATUS, res_status);
            self.shm
                .write_u32(csr::OBEND_CTRL, (ctrl & !ctrl_bits::AP_START) | ctrl_bits::AP_DONE);
            self.shm.write_u32(csr::SILICON_CTRL_STATUS, 2);

            // Emit C2H telemetry beat
            let mut beat = AxiStream512Beat::default();
            beat.tlast = true;
            beat.set_word64(0, OBCAM_WIRE_MAGIC);
            beat.set_word64(1, ((pcycles as u64) << 32) | (res_status as u64));
            beat.set_word64(
                2,
                ((self.shm.read_u32(csr::PERF_CAM_ALLOCS) as u64) << 32)
                    | (self.shm.read_u32(csr::PERF_CAM_HITS) as u64),
            );
            beat.set_word64(
                3,
                ((self.shm.read_u32(csr::PERF_NOC_FLITS) as u64) << 32)
                    | (self.shm.read_u32(csr::PERF_BYPASS_CNT) as u64),
            );
            beat.set_word64(4, ((match_thm as u64) << 32) | (lut_hits as u64));
            self.rx_beats.push(beat);
        }
    }
}

impl FpgaHalBackend for SimBackend {
    fn backend_name(&self) -> &'static str {
        "verilator-shm-sim"
    }

    fn read_csr32(&self, offset: usize) -> Result<u32, FpgaHalError> {
        if offset + 4 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        Ok(self.shm.read_u32(offset))
    }

    fn write_csr32(&mut self, offset: usize, val: u32) -> Result<(), FpgaHalError> {
        if offset + 4 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        if offset == csr::OBEND_CTRL && (val & ctrl_bits::DPR_ISOLATE_EN) != 0 {
            let prev = self.shm.read_u32(csr::OBEND_CTRL);
            if (prev & ctrl_bits::DPR_ISOLATE_EN) == 0 {
                for i in 0..32 {
                    self.skid_held_outputs[i] = self.shm.read_u64(csr::out_port_offset(i));
                }
            }
        }
        self.shm.write_u32(offset, val);
        Ok(())
    }

    fn read_csr64(&self, offset: usize) -> Result<u64, FpgaHalError> {
        if offset + 8 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        Ok(self.shm.read_u64(offset))
    }

    fn write_csr64(&mut self, offset: usize, val: u64) -> Result<(), FpgaHalError> {
        if offset + 8 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        self.shm.write_u64(offset, val);
        Ok(())
    }

    fn push_dma_beats(&mut self, beats: &[AxiStream512Beat]) -> Result<usize, FpgaHalError> {
        if let Some(first) = beats.first() {
            if let Some(frame) = SiliconElabWireFrame::from_axi_beats(beats) {
                self.shm
                    .write_u32(csr::TARGET_EXPR_H, frame.header.target_expr_h);
                self.shm
                    .write_u32(csr::TARGET_TYPE_H, frame.header.target_type_h);
                self.shm
                    .write_u32(csr::TARGET_DECL_SYM, frame.header.target_decl_sym);
                self.shm
                    .write_u32(csr::FUEL_BUDGET, frame.header.fuel_budget);

                for node in &frame.cam_nodes {
                    let bucket = node.hash_bucket10();
                    let bypass_hit = self.last_write_bucket == Some(bucket);
                    if bypass_hit {
                        let b = self.shm.read_u32(csr::PERF_BYPASS_CNT).wrapping_add(1);
                        self.shm.write_u32(csr::PERF_BYPASS_CNT, b);
                    }
                    match self.cam_uram.get(&bucket) {
                        Some(&(existing, _)) if existing == *node => {
                            let h = self.shm.read_u32(csr::PERF_CAM_HITS).wrapping_add(1);
                            self.shm.write_u32(csr::PERF_CAM_HITS, h);
                        }
                        _ => {
                            let h = self.next_cam_handle;
                            self.next_cam_handle = self.next_cam_handle.wrapping_add(1);
                            self.cam_uram.insert(bucket, (*node, h));
                            self.last_write_bucket = Some(bucket);
                            let a = self.shm.read_u32(csr::PERF_CAM_ALLOCS).wrapping_add(1);
                            self.shm.write_u32(csr::PERF_CAM_ALLOCS, a);
                        }
                    }
                }
                let flits = self
                    .shm
                    .read_u32(csr::PERF_NOC_FLITS)
                    .wrapping_add(frame.unify_worklist.len() as u32);
                self.shm.write_u32(csr::PERF_NOC_FLITS, flits);
                let luts = self
                    .shm
                    .read_u32(csr::PERF_LUT_HITS)
                    .wrapping_add(frame.discr_trie_entries.len() as u32);
                self.shm.write_u32(csr::PERF_LUT_HITS, luts);

                let ctrl = self.shm.read_u32(csr::OBEND_CTRL);
                self.shm
                    .write_u32(csr::OBEND_CTRL, ctrl | ctrl_bits::AP_START);
            } else if let Some(hdr) = ObcamWireHeader::from_beat(first) {
                self.shm.write_u32(csr::TARGET_EXPR_H, hdr.target_expr_h);
                self.shm.write_u32(csr::TARGET_TYPE_H, hdr.target_type_h);
                self.shm
                    .write_u32(csr::TARGET_DECL_SYM, hdr.target_decl_sym);
                self.shm.write_u32(csr::FUEL_BUDGET, hdr.fuel_budget);
                let ctrl = self.shm.read_u32(csr::OBEND_CTRL);
                self.shm
                    .write_u32(csr::OBEND_CTRL, ctrl | ctrl_bits::AP_START);
            } else {
                // ICAP DPR configuration frame beat
                self.shadow_dpr_digest = first.word64(1);
            }
        }
        self.tx_beats.extend_from_slice(beats);
        self.shm
            .write_u64(csr::DMA_TX_RING, self.tx_beats.len() as u64);
        Ok(beats.len())
    }

    fn pull_dma_beats(&mut self, max_beats: usize) -> Result<Vec<AxiStream512Beat>, FpgaHalError> {
        let count = max_beats.min(self.rx_beats.len());
        let drained: Vec<AxiStream512Beat> = self.rx_beats.drain(..count).collect();
        self.shm
            .write_u64(csr::DMA_RX_RING, self.rx_beats.len() as u64);
        Ok(drained)
    }

    fn step_cycles(&mut self, num_cycles: u32) -> Result<u64, FpgaHalError> {
        for _ in 0..num_cycles.max(1) {
            self.step_one_cycle();
        }
        self.notify_verilator_daemon(b"STEP")?;
        Ok(self.shm.read_u64(csr::OBEND_CYCLE_COUNT))
    }

    fn read_telemetry(&self) -> Result<SiliconTelemetry, FpgaHalError> {
        let status = self.shm.read_u32(csr::RESULT_STATUS);
        let ctrl = self.shm.read_u32(csr::OBEND_CTRL);
        Ok(SiliconTelemetry {
            backend: self.backend_name().to_string(),
            total_cycles: self.shm.read_u64(csr::OBEND_CYCLE_COUNT),
            silicon_cycles: self.shm.read_u32(csr::PERF_CYCLES),
            cam_hits: self.shm.read_u32(csr::PERF_CAM_HITS),
            cam_allocs: self.shm.read_u32(csr::PERF_CAM_ALLOCS),
            uram_bypass_hits: self.shm.read_u32(csr::PERF_BYPASS_CNT),
            noc_flits: self.shm.read_u32(csr::PERF_NOC_FLITS),
            discr_lut_hits: self.shm.read_u32(csr::PERF_LUT_HITS),
            zone3_match_thm: self.shm.read_u32(csr::ZONE3_MATCH_THM),
            kernel_accepted: (status & 0x2) != 0,
            dpr_isolated: (ctrl & ctrl_bits::DPR_ISOLATE_EN) != 0,
            dpr_fallback_active: (ctrl & ctrl_bits::DPR_FALLBACK_ACTIVE) != 0
                || (status & 0x4) != 0,
        })
    }
}
