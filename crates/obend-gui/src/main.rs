use clap::{Parser, Subcommand};
use colored::*;
use obend_ffi::session::ObendSession;
use obend_gui::viewport::{render_projection_viewport, LawDialControl, LawDialMode, ProjectionKind};
use std::fs;
use std::path::PathBuf;

/// The `obend-gui` binary. Only the subcommands that evaluate through the Lean FFI open an
/// `ObendSession` (and so need `libobend_Obend` next to the binary); `viewport` and `help` never
/// touch Lean. Before 2026-11-04 the session was opened before the subcommand was read, and every
/// subcommand, `viewport` included, died with it when the library did not match the binary.
#[derive(Parser)]
#[command(
    name = "obend-gui",
    about = "Obend workbench server and viewport previewer (the notebook format is a prototype: one bounded counter per workbook)"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Send a file's bytes through the FFI session's cell evaluator and print the result's size.
    /// This is a round-trip smoke test of the FFI, not a notebook run: no cells are listed and no
    /// values are printed (needs libobend_Obend).
    EvalBytes {
        path: PathBuf,
        #[arg(short, long)]
        verbose: bool,
    },
    /// Project a hardware certificate file into a `.obnb` `Content.cell` and print its size
    /// (needs libobend_Obend).
    ProjectHw {
        cert_path: PathBuf,
    },
    /// Render a terminal viewport for one of the ProjectionKinds or physical viewport kinds
    /// (pure Rust; needs no Lean library).
    Viewport {
        #[arg(short, long, default_value = "waveform")]
        kind: String,
        #[arg(short, long, default_value = "ThermalCoolingOde")]
        title: String,
    },
    /// Start the HTTP/JSON workbench server (needs libobend_Obend).
    Serve {
        #[arg(short, long, default_value = "127.0.0.1:7878")]
        bind: String,
    },
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    match cli.command {
        Commands::EvalBytes { path, verbose } => {
            let mut session = ObendSession::new()?;
            println!("{} Reading: {}", "[OBEND]".bold().green(), path.display());
            let data = fs::read(&path)?;
            let res = session.eval_cell(&data)?;
            println!(
                "{} eval_cell returned {} bytes for {} bytes in.",
                "[FFI]".bold().green(),
                res.len(),
                data.len()
            );
            if verbose {
                println!("Output payload preview: {:?}", &res[..res.len().min(64)]);
            }
        }
        Commands::ProjectHw { cert_path } => {
            let mut session = ObendSession::new()?;
            println!("{} Reading hardware certificate: {}", "[EDA/CAD]".bold().magenta(), cert_path.display());
            let hw_raw = fs::read(&cert_path)?;
            let projected_cell = session.project_hardware(&hw_raw)?;
            println!("{} Projected cell: {} bytes (.obnb Content.cell)", "[OK]".bold().green(), projected_cell.len());
        }
        Commands::Viewport { kind, title } => {
            let dial = LawDialControl {
                cell_id: "cell-0".to_string(),
                mode: LawDialMode::Locked,
                invariant_expr: "T in [15.0, 35.0]".to_string(),
                margin_lo: 15.0,
                margin_hi: 35.0,
                current_value: 25.0,
            };
            if let Some(phys_kind) = obend_gui::viewport::PhysicalViewportKind::from_label(&kind) {
                let vp = obend_gui::viewport::render_physical_viewport(phys_kind, &title, &dial);
                println!("{}", vp.terminal_canvas);
            } else {
                let proj_kind = ProjectionKind::from_label(&kind)
                    .ok_or_else(|| format!("unknown ProjectionKind: {kind}"))?;
                let vp = render_projection_viewport(proj_kind, &title, &dial);
                println!("{}", vp.terminal_canvas);
            }
        }
        Commands::Serve { bind } => {
            let server = obend_gui::server::WorkbenchServer::bind(&bind)?;
            println!(
                "{} workbench listening on {}",
                "[WORKBENCH]".bold().green(),
                server.base_url()
            );
            loop {
                std::thread::sleep(std::time::Duration::from_secs(3600));
            }
        }
    }

    Ok(())
}
