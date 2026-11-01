//! CLI binary `obend_hw_host` for munging EDA files into RFC 8949 CBOR hardware certificates
//! and inspecting `.obnb` `Obend.Core.Data` binary cells emitted by the Lean kernel.

use obend_hw_ffi::{
    munge_kicad_meander_sexpr, BinaryCodec, BinaryHwCert, HwCertDomain, ObendCoreData,
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
        eprintln!("usage: obend_hw_host <emit-cbor|decode-cbor|inspect-obnb|munge-kicad> [flags]");
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
        "decode-cbor" => {
            let in_path = extract_flag(&args, "--in").expect("--in PATH required");
            let bytes = fs::read(&in_path).expect("failed to read binary CBOR");
            match BinaryHwCert::from_slice(&bytes) {
                Some(cert) => {
                    println!(
                        "rust-ffi: decoded valid CBOR BinaryHwCert: domain={:?} params=[{}, {}, {}, {}, {}, {}]",
                        cert.domain, cert.p0, cert.p1, cert.p2, cert.p3, cert.p4, cert.p5
                    );
                }
                None => {
                    eprintln!("rust-ffi: invalid CBOR BinaryHwCert frame");
                    process::exit(3);
                }
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
