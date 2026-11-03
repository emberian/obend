//! Rung 3 & Rung 4 AWS EC2 F2 (`vu47p` `xcvu47p-fsvh2892-2-e`) Backend (`AwsF2Backend`):
//! Maps BAR0 OCL CSRs (`/dev/fpga0` or a mock BAR0 device file) via `mmap` and streams
//! 512-bit AXI4-Stream `OBCAMv1` & ICAP DPR frames over `/dev/xdma0_h2c_0` and `/dev/xdma0_c2h_0`.

use crate::regs::{
    ctrl_bits, csr, AxiStream512Beat, OBEND_MAGIC_F20, OBEND_VERSION_CAPS_DEFAULT,
    SHM_APERTURE_BYTES,
};
use crate::sim_backend::PosixShmAperture;
use crate::{FpgaHalBackend, FpgaHalError, SiliconTelemetry};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

/// AWS EC2 F2 device paths configuration.
#[derive(Debug, Clone)]
pub struct AwsF2Config {
    pub bar0_path: PathBuf,
    pub xdma_h2c_path: PathBuf,
    pub xdma_c2h_path: PathBuf,
}

impl Default for AwsF2Config {
    fn default() -> Self {
        Self {
            bar0_path: PathBuf::from("/dev/fpga0"),
            xdma_h2c_path: PathBuf::from("/dev/xdma0_h2c_0"),
            xdma_c2h_path: PathBuf::from("/dev/xdma0_c2h_0"),
        }
    }
}

/// Rung 3/4 AWS EC2 F2 (`vu47p`) Hardware Backend (`AwsF2Backend`).
pub struct AwsF2Backend {
    cfg: AwsF2Config,
    bar0: PosixShmAperture,
    h2c_file: File,
    c2h_file: File,
}

impl AwsF2Backend {
    /// Open an AWS EC2 F2 device (or pre-initialized mock F2 device files for testing).
    /// Fails closed with `FpgaHalError::InvalidMagic` if BAR0 offset `0x0000` != `OBEND_MAGIC_F20`.
    pub fn open(cfg: AwsF2Config) -> Result<Self, FpgaHalError> {
        let bar0 = PosixShmAperture::open_existing_mmio(&cfg.bar0_path)?;
        let magic = bar0.read_u64(csr::OBEND_MAGIC);
        if magic != OBEND_MAGIC_F20 {
            return Err(FpgaHalError::InvalidMagic {
                expected: OBEND_MAGIC_F20,
                found: magic,
            });
        }
        let h2c_file = OpenOptions::new()
            .write(true)
            .open(&cfg.xdma_h2c_path)
            .map_err(|e| FpgaHalError::Io(format!("open H2C {:?}: {}", cfg.xdma_h2c_path, e)))?;
        let c2h_file = OpenOptions::new()
            .read(true)
            .open(&cfg.xdma_c2h_path)
            .map_err(|e| FpgaHalError::Io(format!("open C2H {:?}: {}", cfg.xdma_c2h_path, e)))?;
        Ok(Self {
            cfg,
            bar0,
            h2c_file,
            c2h_file,
        })
    }

    /// Create a temporary file-backed AWS F2 device triplet in `dir` for local verification.
    pub fn open_mock_in_dir(dir: impl AsRef<Path>) -> Result<Self, FpgaHalError> {
        let base = dir.as_ref();
        std::fs::create_dir_all(base)
            .map_err(|e| FpgaHalError::Io(format!("create_dir_all {:?}: {}", base, e)))?;
        let cfg = AwsF2Config {
            bar0_path: base.join("mock_fpga0_bar0.bin"),
            xdma_h2c_path: base.join("mock_xdma0_h2c_0.bin"),
            xdma_c2h_path: base.join("mock_xdma0_c2h_0.bin"),
        };
        {
            let mut init_ap = PosixShmAperture::open_file_backed(&cfg.bar0_path)?;
            init_ap.write_u64(csr::OBEND_MAGIC, OBEND_MAGIC_F20);
            init_ap.write_u64(csr::OBEND_VERSION_CAPS, OBEND_VERSION_CAPS_DEFAULT);
        }
        let _ = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&cfg.xdma_h2c_path)
            .map_err(|e| FpgaHalError::Io(format!("init H2C {:?}: {}", cfg.xdma_h2c_path, e)))?;
        let _ = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&cfg.xdma_c2h_path)
            .map_err(|e| FpgaHalError::Io(format!("init C2H {:?}: {}", cfg.xdma_c2h_path, e)))?;
        Self::open(cfg)
    }

    pub fn config(&self) -> &AwsF2Config {
        &self.cfg
    }
}

impl FpgaHalBackend for AwsF2Backend {
    fn backend_name(&self) -> &'static str {
        "aws-f2-vu47p"
    }

    fn read_csr32(&self, offset: usize) -> Result<u32, FpgaHalError> {
        if offset + 4 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        Ok(self.bar0.read_u32(offset))
    }

    fn write_csr32(&mut self, offset: usize, val: u32) -> Result<(), FpgaHalError> {
        if offset + 4 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        self.bar0.write_u32(offset, val);
        Ok(())
    }

    fn read_csr64(&self, offset: usize) -> Result<u64, FpgaHalError> {
        if offset + 8 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        Ok(self.bar0.read_u64(offset))
    }

    fn write_csr64(&mut self, offset: usize, val: u64) -> Result<(), FpgaHalError> {
        if offset + 8 > SHM_APERTURE_BYTES {
            return Err(FpgaHalError::OutOfBounds(offset));
        }
        self.bar0.write_u64(offset, val);
        Ok(())
    }

    fn push_dma_beats(&mut self, beats: &[AxiStream512Beat]) -> Result<usize, FpgaHalError> {
        for beat in beats {
            self.h2c_file
                .write_all(&beat.tdata)
                .map_err(|e| FpgaHalError::Io(format!("XDMA H2C write: {}", e)))?;
        }
        self.h2c_file
            .flush()
            .map_err(|e| FpgaHalError::Io(format!("XDMA H2C flush: {}", e)))?;
        let prev = self.bar0.read_u64(csr::DMA_TX_RING);
        self.bar0
            .write_u64(csr::DMA_TX_RING, prev.wrapping_add(beats.len() as u64));
        Ok(beats.len())
    }

    fn pull_dma_beats(&mut self, max_beats: usize) -> Result<Vec<AxiStream512Beat>, FpgaHalError> {
        let mut out = Vec::new();
        for _ in 0..max_beats {
            let mut buf = [0u8; 64];
            match self.c2h_file.read_exact(&mut buf) {
                Ok(()) => out.push(AxiStream512Beat::from_slice(&buf, true)),
                Err(_) => break,
            }
        }
        let prev = self.bar0.read_u64(csr::DMA_RX_RING);
        self.bar0
            .write_u64(csr::DMA_RX_RING, prev.wrapping_add(out.len() as u64));
        Ok(out)
    }

    fn step_cycles(&mut self, num_cycles: u32) -> Result<u64, FpgaHalError> {
        let mut cyc = self.bar0.read_u64(csr::OBEND_CYCLE_COUNT);
        for _ in 0..num_cycles.max(1) {
            let ctrl = self.bar0.read_u32(csr::OBEND_CTRL);
            self.bar0
                .write_u32(csr::OBEND_CTRL, ctrl | ctrl_bits::STEP_ONCE);
            cyc = cyc.wrapping_add(1);
            self.bar0.write_u64(csr::OBEND_CYCLE_COUNT, cyc);
            self.bar0
                .write_u32(csr::OBEND_CTRL, (ctrl & !ctrl_bits::STEP_ONCE) | ctrl_bits::AP_DONE);
        }
        Ok(cyc)
    }

    fn read_telemetry(&self) -> Result<SiliconTelemetry, FpgaHalError> {
        let status = self.bar0.read_u32(csr::RESULT_STATUS);
        let ctrl = self.bar0.read_u32(csr::OBEND_CTRL);
        Ok(SiliconTelemetry {
            backend: self.backend_name().to_string(),
            total_cycles: self.bar0.read_u64(csr::OBEND_CYCLE_COUNT),
            silicon_cycles: self.bar0.read_u32(csr::PERF_CYCLES),
            cam_hits: self.bar0.read_u32(csr::PERF_CAM_HITS),
            cam_allocs: self.bar0.read_u32(csr::PERF_CAM_ALLOCS),
            uram_bypass_hits: self.bar0.read_u32(csr::PERF_BYPASS_CNT),
            noc_flits: self.bar0.read_u32(csr::PERF_NOC_FLITS),
            discr_lut_hits: self.bar0.read_u32(csr::PERF_LUT_HITS),
            zone3_match_thm: self.bar0.read_u32(csr::ZONE3_MATCH_THM),
            kernel_accepted: (status & 0x2) != 0,
            dpr_isolated: (ctrl & ctrl_bits::DPR_ISOLATE_EN) != 0,
            dpr_fallback_active: (ctrl & ctrl_bits::DPR_FALLBACK_ACTIVE) != 0
                || (status & 0x4) != 0,
        })
    }
}
