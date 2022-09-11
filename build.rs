fn main() {
    let c_paths: Vec<std::path::PathBuf> =
        glob::glob("rabbitizer/src/**/*.c").unwrap().filter_map(|g| g.ok()).collect();
    let h_paths: Vec<std::path::PathBuf> =
        glob::glob("rabbitizer/include/**/*.h").unwrap().filter_map(|g| g.ok()).collect();
    println!("cargo:rerun-if-changed=wrapper.h");
    for path in c_paths.iter().chain(&h_paths) {
        println!("cargo:rerun-if-changed={}", path.to_string_lossy());
    }
    cc::Build::new()
        .files(c_paths)
        .include("rabbitizer/include")
        .warnings(false)
        .compile("rabbitizer");
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg("-Irabbitizer/include")
        .use_core()
        .ctypes_prefix("cty")
        .default_enum_style(bindgen::EnumVariation::Rust { non_exhaustive: false })
        .prepend_enum_name(false)
        .allowlist_function("Rabbitizer.*")
        .allowlist_var("Rabbitizer.*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks));
    let result = bindings.generate().expect("Unable to generate bindings");
    let out_path = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    result.write_to_file(out_path.join("bindings.rs")).expect("Couldn't write bindings");
}
