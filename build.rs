fn main() {
    // Tell Cargo that if the given file changes, to rerun this build script.
    println!("cargo:rerun-if-changed=src/crc4.c");
    // Use the `cc` crate to build a C file and statically link it.
    cc::Build::new().file("src/crc4.c").compile("hello");
}
