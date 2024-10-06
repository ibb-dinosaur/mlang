use std::env;
use std::path::PathBuf;

fn main() {
    // cbindgen
    /*let headers_dir = "~/gcc/src/gcc/jit";
    let library_dir = "~/gcc/build/gcc";

    println!("cargo:rustc-link-search={}", library_dir);
    println!("cargo:rustc-link-lib=gccjit");
    let bindings = bindgen::Builder::default()
        .header(format!("{}/libgccjit.h", headers_dir))
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");*/

    /*    let headers_dir = "~/rsjit/mir";
        let library_dir = "~/rsjit/mir";
    
        println!("cargo:rustc-link-search={}", library_dir);
        println!("cargo:rustc-link-lib=mir");
        let bindings = bindgen::Builder::default()
            .header(format!("{}/mir.h", headers_dir))
            .header(format!("{}/mir-gen.h", headers_dir))
            .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
            .generate()
            .expect("Unable to generate bindings");
        let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
        bindings
            .write_to_file(out_path.join("bindings.rs"))
            .expect("Couldn't write bindings!");
    */
    
    lalrpop::process_src().unwrap();

    // llvm-extras
    /*println!("cargo:rerun-if-changed=llvm-extras.cpp");
    cc::Build::new()
        .cpp(true)
        .file("llvm-extras.cpp")
        .include("/usr/include/llvm-18")
        .include("/usr/include/llvm-c-18")
        .compile("llvm-extras");*/

    println!("cargo:rustc-link-search=.");
    println!("cargo:rustc-link-lib=static=llvm-extras");
}