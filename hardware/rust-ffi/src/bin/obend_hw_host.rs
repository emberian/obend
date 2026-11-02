//! CLI binary `obend_hw_host` for munging EDA files, running 2D FEMM Newton-Raphson meshes,
//! pruning 3D F-Rep octree CSG tapes (`Choice::Left`/`Right`/`Both`), running in-silico evolutionary
//! Pareto physical design search, and inspecting `.obnb` `Obend.Core.Data` binary cells.

use obend_hw_ffi::{
    eval_octree_frep_pruned, evolve_physical_design, munge_kicad_meander_sexpr, solve_femm_mesh,
    BinaryCodec, BinaryHwCert, BinaryTapeCert, HwCertDomain, ObendCoreData,
};
use std::env;
use std::fs;
use std::process;

fn extract_flag(args: &[String], flag: &str) -> Option<String> {
    for w in args.windows(2) {
        if w[0] == flag {
            return Some(w[1].clone());
        }
    }
    None
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!(
            "usage: obend_hw_host <emit-cbor|decode-cbor|inspect-obnb|munge-kicad|solve-femm|prune-octree|evolve> [flags]"
        );
        process::exit(2);
    }

    match args[0].as_str() {
        "emit-cbor" => {
            let dom_str = extract_flag(&args, "--domain").unwrap_or_else(|| "pnr".to_string());
            let mode = extract_flag(&args, "--mode").unwrap_or_else(|| "golden".to_string());
            let out_path = extract_flag(&args, "--out").expect("--out PATH required");
            let dom = HwCertDomain::from_name(&dom_str).expect("unknown domain");
            let mut cert = BinaryHwCert::golden_for_domain(dom);
            if mode == "corrupt" {
                cert.p5 = 100; // violate PnR clock period slack
            }
            let bytes = cert.to_vec();
            fs::write(&out_path, &bytes).expect("failed to write binary CBOR");
            println!(
                "rust-ffi: emitted {} bytes of RFC 8949 CBOR (tag=0x0BED, domain={:?}) to {}",
                bytes.len(),
                dom,
                out_path
            );
        }
        "solve-femm" => {
            let out_path = extract_flag(&args, "--out").expect("--out PATH required");
            let sol = solve_femm_mesh();
            let bytes = sol.tape_cert.to_vec();
            fs::write(&out_path, &bytes).expect("failed to write FEMM mesh CBOR");
            println!(
                "rust-ffi: solve-femm converged in {} Newton-Raphson iters (||r||_inf={}, elements={}, energy={}, peak_B2={}) -> {} bytes CBOR at {}",
                sol.iterations,
                sol.max_residual_norm,
                sol.element_energies.len(),
                sol.total_energy,
                sol.peak_tooth_b2_scaled,
                bytes.len(),
                out_path
            );
        }
        "prune-octree" => {
            let out_path = extract_flag(&args, "--out").expect("--out PATH required");
            let rep = eval_octree_frep_pruned();
            let bytes = rep.tape_cert.to_vec();
            fs::write(&out_path, &bytes).expect("failed to write octree F-Rep CBOR");
            println!(
                "rust-ffi: prune-octree Choice compaction: unpruned_ops={} -> pruned_ops={} (choices={}, zero_discrepancy={}) -> {} bytes CBOR at {}",
                rep.unpruned_tape_ops,
                rep.pruned_tape_ops,
                rep.choice_left_or_right_count,
                rep.zero_discrepancy,
                bytes.len(),
                out_path
            );
        }
        "evolve" => {
            let out_path = extract_flag(&args, "--out").expect("--out PATH required");
            let evo = evolve_physical_design();
            let bytes = evo.tape_cert.to_vec();
            fs::write(&out_path, &bytes).expect("failed to write evolutionary Pareto CBOR");
            println!(
                "rust-ffi: evolve evaluated {} candidates, Pareto front={}, best=(tooth={}um, aspect={}, fcml={}kHz, feed={}mm/s, T_peak={}mC, err={}um) -> {} bytes CBOR at {}",
                evo.evaluated_candidates,
                evo.pareto_front.len(),
                evo.best_candidate.tooth_width_um,
                evo.best_candidate.microchannel_aspect_permille,
                evo.best_candidate.fcml_freq_khz,
                evo.best_candidate.cnc_feed_mm_s,
                evo.best_candidate.peak_winding_temp_mc,
                evo.best_candidate.volumetric_error_um,
                bytes.len(),
                out_path
            );
        }
        "decode-cbor" => {
            let in_path = extract_flag(&args, "--in").expect("--in PATH required");
            let bytes = fs::read(&in_path).expect("failed to read binary CBOR");
            if let Some(cert) = BinaryHwCert::from_slice(&bytes) {
                println!(
                    "rust-ffi: decoded valid CBOR BinaryHwCert: domain={:?} params=[{}, {}, {}, {}, {}, {}]",
                    cert.domain, cert.p0, cert.p1, cert.p2, cert.p3, cert.p4, cert.p5
                );
            } else if let Some(tcert) = BinaryTapeCert::from_slice(&bytes) {
                println!(
                    "rust-ffi: decoded valid CBOR BinaryTapeCert: domain={:?} metric0={} metric1={} words={:?}",
                    tcert.domain, tcert.metric0, tcert.metric1, tcert.words
                );
            } else {
                eprintln!("rust-ffi: invalid CBOR BinaryHwCert/BinaryTapeCert frame");
                process::exit(3);
            }
        }
        "munge-kicad" => {
            let sexpr = extract_flag(&args, "--sexpr").unwrap_or_else(|| {
                "(kicad_pcb (meander (base_length_um 25200) (num_bends 6) (amplitude_um 400) (pitch_um 400) (spacing_step 4) (ref_length_um 30000)))".to_string()
            });
            let out_path = extract_flag(&args, "--out").expect("--out PATH required");
            let cert = munge_kicad_meander_sexpr(&sexpr).expect("failed to munge KiCad sexpr");
            let bytes = cert.to_vec();
            fs::write(&out_path, &bytes).expect("failed to write binary CBOR");
            println!(
                "rust-ffi: munged KiCad S-expression into {} bytes of CBOR at {}",
                bytes.len(),
                out_path
            );
        }
        "inspect-obnb" => {
            let in_path = extract_flag(&args, "--in").expect("--in PATH required");
            let bytes = fs::read(&in_path).expect("failed to read .obnb binary cell");
            match ObendCoreData::decode_canonical(&bytes) {
                Some((data, rest)) if rest.is_empty() => {
                    println!("rust-ffi: decoded .obnb Obend.Core.Data cell: {:?}", data);
                }
                _ => {
                    eprintln!("rust-ffi: failed to decode .obnb binary cell");
                    process::exit(3);
                }
            }
        }
        other => {
            eprintln!("unknown subcommand: {}", other);
            process::exit(2);
        }
    }
}
