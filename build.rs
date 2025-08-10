use convert_case::{Case, Casing};
use std::path::Path;

fn main() {
    let bind_crate_name = std::env::var("CARGO_PKG_NAME")
        .unwrap()
        .to_case(Case::Snake);
    let workspace_root = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let target_dir =
        std::env::var("CARGO_TARGET_DIR").unwrap_or(format!("{workspace_root}/target"));

    let config = cbindgen::Config {
        language: cbindgen::Language::Cxx,
        namespace: Some("ffi".to_string()),
        include_guard: Some(format!("_{}_H", bind_crate_name.to_uppercase())),
        ..std::default::Default::default()
    };
    cbindgen::generate_with_config(&workspace_root, config)
        .unwrap()
        .write_to_file(Path::new(&target_dir).join(format!("{bind_crate_name}.h")));

    println!("cargo::rerun-if-changed=src");
}
