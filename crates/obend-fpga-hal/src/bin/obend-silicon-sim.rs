//! `obend-silicon-sim` — drives the `MockBackend` register-map model and prints its telemetry.
//! It does not run any RTL (there is no Verilated model in this crate); see the crate docs.
//!
//! Usage:
//!   obend-silicon-sim [--shm <path>] [--socket <path>] [--cycles <N>] [--dpr-test]

use obend_fpga_hal::regs::{PackedNodeWord88, SiliconElabWireFrame};
use obend_fpga_hal::sim_backend::MockBackend;
use obend_fpga_hal::ObendFpgaHal;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    let mut shm_path: Option<PathBuf> = None;
    let mut sock_path: Option<PathBuf> = None;
    let mut cycles: u32 = 8;
    let mut run_dpr_test = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--shm" if i + 1 < args.len() => {
                shm_path = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--socket" if i + 1 < args.len() => {
                sock_path = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--cycles" if i + 1 < args.len() => {
                cycles = args[i + 1].parse().unwrap_or(8);
                i += 2;
            }
            "--dpr-test" => {
                run_dpr_test = true;
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }

    let mut hal = if let Some(shm) = shm_path {
        let backend = MockBackend::with_shm_and_socket(shm, sock_path)?;
        ObendFpgaHal::from_backend(backend)
    } else {
        ObendFpgaHal::new_mock()?
    };

    hal.verify_magic()?;
    hal.write_in_port(0, 4)?;
    hal.write_in_port(1, 8)?;
    hal.write_in_port(2, 6)?;

    let mut frame = SiliconElabWireFrame::new(0x1001, 0x1001, 0x0204, 1024);
    let node = PackedNodeWord88 {
        opcode: 0x04,
        binder_depth: 2,
        child0: 0x1001,
        child1: 0x1001,
    };
    frame.cam_nodes.push(node);
    frame.cam_nodes.push(node);
    frame.unify_worklist.push((0x1001, 0x1001));
    frame.discr_trie_entries.push((0x1001, 0x0204, 7));

    let telem = hal.run_silicon_elab_frame(&frame, cycles)?;

    if run_dpr_test {
        let _ = hal.perform_icap_dpr_hot_swap(
            "quotient_stator_slot",
            0xCAFE_BABE_1234_5678,
            0xABCD_EF01_2345_6789,
            0xABCD_EF01_2345_6789,
            false,
        )?;
    }

    println!("{}", serde_json::to_string_pretty(&telem)?);
    Ok(())
}
