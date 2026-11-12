// Propagate the Lean shared library rpath flags exported by `obend-ffi` (`links = "obend_bridge"`)
// to dependent test binaries in `obend-gui`.
fn main() {
    println!("cargo:rerun-if-env-changed=DEP_OBEND_BRIDGE_LIB_DIR");
    println!("cargo:rerun-if-env-changed=DEP_OBEND_BRIDGE_LEAN_LIB_DIR");
    for var in ["DEP_OBEND_BRIDGE_LIB_DIR", "DEP_OBEND_BRIDGE_LEAN_LIB_DIR"] {
        if let Ok(dir) = std::env::var(var) {
            if !dir.is_empty() {
                println!("cargo:rustc-link-arg=-Wl,-rpath,{dir}");
            }
        }
    }
}
