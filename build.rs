use convert_case::{Case, Casing};
use std::path::{Path, PathBuf};

const RISCV_SIM_SRC_DIR: &str = "cpp-src/riscv-fesvr";

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
        includes: vec!["fesvr/dmi.h".to_string()],
        ..std::default::Default::default()
    };
    cbindgen::generate_with_config(&workspace_root, config)
        .unwrap()
        .write_to_file(Path::new(&target_dir).join(format!("{bind_crate_name}.h")));

    let rust_bindings = bindgen::Builder::default()
        .header(
            Path::new(RISCV_SIM_SRC_DIR)
                .join("fesvr/dmi.h")
                .as_os_str()
                .to_str()
                .unwrap(),
        )
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("unable to generate rust bindings");
    let out_path = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    rust_bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("unable to generate binding.rs");
}
