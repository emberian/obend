use clap::{Parser, Subcommand};
use colored::*;
use obend_ffi::session::ObendSession;
use obend_gui::viewport::{render_projection_viewport, LawDialControl, LawDialMode, ProjectionKind};
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "obend-gui", about = "Obend Notebook Runner & Hardware CAD Previewer")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Execute an .obnb notebook and report cell evaluation results
    Run {
        notebook_path: PathBuf,
        #[arg(short, long)]
        verbose: bool,
    },
    /// Inspect cell dependency graph and footprint pins without evaluation
    Inspect {
        notebook_path: PathBuf,
    },
    /// Preview read-only hardware projections (schematics, timing slack, GDSII)
    ProjectHw {
        cert_path: PathBuf,
    },
    /// Render an interactive SVG/HTML/terminal viewport for any of the 10 ProjectionKinds
    Viewport {
        #[arg(short, long, default_value = "waveform")]
        kind: String,
        #[arg(short, long, default_value = "ThermalCoolingOde")]
        title: String,
    },
    /// Start the live interactive .obnb HTTP/WebSocket workbench server (`WS 31`)
    Serve {
        #[arg(short, long, default_value = "127.0.0.1:7878")]
        bind: String,
    },
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    let mut session = ObendSession::new()?;

    match cli.command {
        Commands::Run { notebook_path, verbose } => {
            println!("{} Loading notebook: {}", "[OBEND]".bold().green(), notebook_path.display());
            let data = fs::read(&notebook_path)?;
            let res = session.eval_cell(&data)?;
            println!("{} Evaluated {} bytes successfully.", "[PASS]".bold().green(), res.len());
            if verbose {
                println!("Output payload preview: {:?}", &res[..res.len().min(64)]);
            }
        }
        Commands::Inspect { notebook_path } => {
            println!("{} Inspecting notebook structure...", "[INSPECT]".bold().cyan());
            let content = fs::read_to_string(&notebook_path)?;
            println!("Notebook size: {} bytes", content.len());
        }
        Commands::ProjectHw { cert_path } => {
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
                "{} Live .obnb HTTP/JSON workbench listening on {}",
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

