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
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    
    lalrpop::process_src().unwrap();

    // llvm-extras
    println!("cargo:rerun-if-changed=llvm-extras.cpp");
    cc::Build::new()
        .cpp(true)
        .file("llvm-extras.cpp")
        .include("/usr/include/llvm-18")
        .include("/usr/include/llvm-c-18")
        .compile("llvm-extras");

    println!("cargo:rustc-link-search=.");
    println!("cargo:rustc-link-lib=static=llvm-extras");

    // compile asm
    println!("cargo:rerun-if-changed=src/asm/farjmp.S");
    if !std::process::Command::new("nasm")
        .arg("-f").arg("elf64")
        .arg("-o").arg(out_path.join("farjmp.S.o"))
        .arg("src/asm/farjmp.S")
        .status().expect("failed to execute nasm").success() {
            panic!("failed to assemble farjmp.S");
        } // to object file
    cc::Build::new()
        .object(out_path.join("farjmp.S.o"))
        .compile("farjmp"); // to static library
    println!("cargo:rustc-link-lib=static=llvm-extras");

    // compile core.ll to bitcode
    println!("cargo:rerun-if-changed=src/core.ll");
    if !std::process::Command::new("llvm-as-18")
        .arg("src/core.ll")
        .status()
        .expect("failed to execute llvm-as-18")
        .success() {
            panic!("failed to assemble core.ll");
        }
    if !std::process::Command::new("opt-18")
        .arg("--Os")
        .arg("src/core.bc")
        .arg("-o").arg("src/core.bc")
        .status()
        .expect("failed to execute opt-18")
        .success() {
            panic!("failed to optimize core.bc");
        }
}