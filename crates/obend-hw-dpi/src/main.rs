#![forbid(unsafe_code)]
//! Isolated stdio framed binary DPI process binary for `obend-hw-dpi`.

use std::io;
use obend_hw_dpi::Ospc4TileHardwareSim;

fn main() -> io::Result<()> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut reader = stdin.lock();
    let mut writer = stdout.lock();
    let mut sim = Ospc4TileHardwareSim::new();
    let _served = sim.serve_stream(&mut reader, &mut writer)?;
    Ok(())
}
