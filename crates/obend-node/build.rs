// The Lean library `obend-ffi` links is shared; `obend-ffi`'s own rpath flags do not reach a
// dependent's binaries, so this crate's executables and test binaries take the directories
// `obend-ffi` publishes (`links = "obend_bridge"`) as rpaths. Under the opt-in stub the
// variables are absent and nothing is added.
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
