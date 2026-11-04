fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../../lean/c/obend_bridge.c");
    println!("cargo:rerun-if-env-changed=LEAN_SYSROOT");
    println!("cargo:rerun-if-env-changed=OBEND_LEAN_LINK");
    println!("cargo:rerun-if-env-changed=OBEND_ALLOW_STUB_FFI");
    println!("cargo:rerun-if-env-changed=OBEND_LAKE_LIB_DIR");

    // The Lean library is the default and the only backend that verifies anything. The stub is
    // opt-in by name (`OBEND_ALLOW_STUB_FFI=1`, or the Cargo feature `stub`) for builds that need
    // the crate to compile without `lake build Obend:shared`; every verify or weave through it
    // refuses with `ObendError::StubBackend`, so a receipt cannot pass through a substitute
    // unnoticed. (Until 2026-11-04 the stub was substituted silently whenever the library was
    // missing, and its verify accepted what it had itself committed.)
    let allow_stub = std::env::var("CARGO_FEATURE_STUB").is_ok()
        || std::env::var("OBEND_ALLOW_STUB_FFI")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);

    if std::env::var("CARGO_FEATURE_STUB").is_ok() {
        println!("cargo:warning=obend-ffi: Cargo feature `stub` set; no Lean kernel is linked and every verify or weave refuses.");
        return;
    }

    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let lake_lib_dir = std::env::var("OBEND_LAKE_LIB_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| workspace_root.join("lean/.lake/build/lib"));

    let lib_so = lake_lib_dir.join("libobend_Obend.so");
    let lib_dylib = lake_lib_dir.join("libobend_Obend.dylib");
    let lib_a = lake_lib_dir.join("libObend.a");
    let lib_so2 = lake_lib_dir.join("libObend.so");
    let lib_dylib2 = lake_lib_dir.join("libObend.dylib");

    let has_libobend = lib_so.exists() || lib_dylib.exists();
    let has_native =
        has_libobend || lib_a.exists() || lib_so2.exists() || lib_dylib2.exists();

    if !has_native {
        if !allow_stub {
            panic!(
                "obend-ffi: the Lean library `libobend_Obend` (.so/.dylib) was not found in {}. \
                 Build it with `lake build Obend:shared` in `lean/` (or point OBEND_LAKE_LIB_DIR at it). \
                 To compile without a kernel anyway, set OBEND_ALLOW_STUB_FFI=1: the stub refuses every \
                 verify and weave, so nothing built that way can check a receipt.",
                lake_lib_dir.display()
            );
        }
        println!(
            "cargo:warning=obend-ffi: OBEND_ALLOW_STUB_FFI set and no Lean library at {}; building the stub, which refuses every verify or weave.",
            lake_lib_dir.display()
        );
        println!("cargo:rustc-cfg=feature=\"stub\"");
        return;
    }

    let lean_sysroot = std::env::var("LEAN_SYSROOT").unwrap_or_else(|_| {
        let out = std::process::Command::new("lean")
            .arg("--print-prefix")
            .current_dir(workspace_root.join("lean"))
            .output()
            .or_else(|_| {
                let home = std::env::var("HOME").unwrap_or_default();
                std::process::Command::new(format!("{home}/.elan/bin/lean"))
                    .arg("--print-prefix")
                    .current_dir(workspace_root.join("lean"))
                    .output()
            })
            .or_else(|_| {
                std::process::Command::new("elan")
                    .args(["run", "leanprover/lean4:v4.35.0", "lean", "--print-prefix"])
                    .current_dir(workspace_root.join("lean"))
                    .output()
            })
            .expect("Failed to locate Lean sysroot via lean --print-prefix");
        String::from_utf8(out.stdout).expect("Valid UTF8").trim().to_string()
    });

    let lean_include = std::path::PathBuf::from(&lean_sysroot).join("include");
    let bridge_c = workspace_root.join("lean/c/obend_bridge.c");

    cc::Build::new()
        .file(&bridge_c)
        .include(&lean_include)
        .warnings(false)
        .compile("obend_bridge");

    println!("cargo:rustc-link-search=native={}", lake_lib_dir.display());
    println!("cargo:rustc-link-search=native={}/lib/lean", lean_sysroot);

    let link_mode = std::env::var("OBEND_LEAN_LINK").unwrap_or_else(|_| {
        if has_libobend || lib_so2.exists() || lib_dylib2.exists() {
            "shared".into()
        } else {
            "static".into()
        }
    });
    if link_mode == "static" {
        println!("cargo:rustc-link-lib=static=Obend");
        println!("cargo:rustc-link-lib=static=leanrt");
        println!("cargo:rustc-link-lib=static=leancpp");
    } else {
        if lib_so.exists() || lib_dylib.exists() {
            println!("cargo:rustc-link-lib=dylib=obend_Obend");
        } else {
            println!("cargo:rustc-link-lib=dylib=Obend");
        }
        println!("cargo:rustc-link-lib=dylib=leanshared");
    }

    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lake_lib_dir.display());
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}/lib/lean", lean_sysroot);
    // `rustc-link-arg` reaches only this crate's own binaries. A dependent's test binary or
    // executable finds the shared library through these (`DEP_OBEND_BRIDGE_LIB_DIR`,
    // `DEP_OBEND_BRIDGE_LEAN_LIB_DIR`; see `crates/obend-node/build.rs`).
    println!("cargo:lib_dir={}", lake_lib_dir.display());
    println!("cargo:lean_lib_dir={}/lib/lean", lean_sysroot);
}
