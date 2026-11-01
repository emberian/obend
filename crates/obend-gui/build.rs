fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if std::env::var("CARGO_FEATURE_STUB").is_ok() {
        return;
    }

    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let lake_lib_dir = workspace_root.join("lean/.lake/build/lib");

    let lib_so = lake_lib_dir.join("libobend_Obend.so");
    let lib_dylib = lake_lib_dir.join("libobend_Obend.dylib");
    let lib_a = lake_lib_dir.join("libObend.a");
    let lib_so2 = lake_lib_dir.join("libObend.so");
    let lib_dylib2 = lake_lib_dir.join("libObend.dylib");

    let has_native = lib_so.exists() || lib_dylib.exists() || lib_a.exists() || lib_so2.exists() || lib_dylib2.exists();
    if !has_native {
        return;
    }

    let lean_sysroot = std::env::var("LEAN_SYSROOT").unwrap_or_else(|_| {
        let out = std::process::Command::new("lean")
            .arg("--print-prefix")
            .current_dir(workspace_root.join("lean"))
            .output()
            .or_else(|_| {
                std::process::Command::new("elan")
                    .args(["run", "leanprover/lean4:v4.35.0", "lean", "--print-prefix"])
                    .current_dir(workspace_root.join("lean"))
                    .output()
            })
            .expect("Failed to locate Lean sysroot via lean --print-prefix");
        String::from_utf8(out.stdout).expect("Valid UTF8").trim().to_string()
    });

    println!("cargo:rustc-link-search=native={}", lake_lib_dir.display());
    println!("cargo:rustc-link-search=native={}/lib/lean", lean_sysroot);
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lake_lib_dir.display());
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}/lib/lean", lean_sysroot);
}
