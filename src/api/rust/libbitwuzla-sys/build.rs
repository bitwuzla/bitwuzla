//! Build script for `libbitwuzla-sys`.
//!
//! Locates a Bitwuzla library, emits the corresponding link directives, and
//! generates with bindgen:
//!
//! - `bindings.rs`: the C API (`bitwuzla/c/bitwuzla.h`, `bitwuzla/c/parser.h`)
//!   with C names.
//! - `rust_enums.rs`: Rust enums for the `bitwuzla` crate, exported as
//!   `DEP_BITWUZLA_RUST_ENUMS`.
//!
//! On docs.rs (`DOCS_RS` set), the checked-in copies in `prebuilt/` are used
//! instead and nothing is linked.
//!
//! Bitwuzla is looked up in this order:
//!
//! 1. `BITWUZLA_LIB_DIR`: directory containing `libbitwuzla`; headers are taken
//!    from `BITWUZLA_INCLUDE_DIR`, `$BITWUZLA_LIB_DIR/../include`, or the
//!    enclosing Bitwuzla source tree.
//! 2. `BITWUZLA_BUILD_DIR`: a (meson) build directory of a Bitwuzla checkout,
//!    used via its uninstalled pkg-config file.
//! 3. `<source root>/build` if this crate lives inside a Bitwuzla source tree
//!    and that build directory provides the requested kind of library (shared,
//!    or static with the `static` feature).
//! 4. pkg-config (`bitwuzla.pc`, honors `PKG_CONFIG_PATH`).
//!
//! Libraries older than this crate are rejected (see `src/version.rs`). The
//! version is taken from pkg-config, for `BITWUZLA_LIB_DIR` from
//! `$BITWUZLA_LIB_DIR/pkgconfig/bitwuzla.pc` if it exists.

use std::env;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use bindgen::callbacks::{
    EnumVariantCustomBehavior, EnumVariantValue, ItemInfo, ItemKind, ParseCallbacks,
};

#[path = "src/version.rs"]
mod version;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=src/version.rs");
    for var in [
        "BITWUZLA_LIB_DIR",
        "BITWUZLA_INCLUDE_DIR",
        "BITWUZLA_BUILD_DIR",
        "PKG_CONFIG_PATH",
        "DOCS_RS",
    ] {
        println!("cargo:rerun-if-env-changed={var}");
    }
    println!("cargo::rustc-check-cfg=cfg(libbitwuzla_sys_in_tree)");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    // Exported to dependents as DEP_BITWUZLA_RUST_ENUMS (see lib.rs).
    println!(
        "cargo:rust_enums={}",
        out_dir.join("rust_enums.rs").display()
    );

    // docs.rs has neither Bitwuzla nor its headers: document the prebuilt
    // bindings and skip linking.
    if env::var_os("DOCS_RS").is_some() {
        let prebuilt = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("prebuilt");
        for file in PREBUILT {
            std::fs::copy(prebuilt.join(file), out_dir.join(file))
                .unwrap_or_else(|e| panic!("Couldn't copy prebuilt/{file}: {e}"));
        }
        return;
    }

    let statik = cfg!(feature = "static");
    let lib = locate(statik);
    check_version(&lib);
    emit_link(&lib, statik);
    if statik {
        // Relink dependents when the static library is rebuilt.
        for dir in &lib.lib_dirs {
            let archive = dir.join("libbitwuzla.a");
            if archive.is_file() {
                println!("cargo:rerun-if-changed={}", archive.display());
            }
        }
        link_cxx_stdlib();
    } else {
        expose_shared_library(&lib.lib_dirs);
    }
    // Exported to dependents as DEP_BITWUZLA_LIBDIR / DEP_BITWUZLA_INCLUDE.
    if let Some(dir) = lib.lib_dirs.first() {
        println!("cargo:libdir={}", dir.display());
    }
    if let Some(dir) = lib.include_dirs.first() {
        println!("cargo:include={}", dir.display());
    }
    // In a Bitwuzla source tree, tests in lib.rs compare the crate version
    // and the licence files with the tree and, for bindings generated from the
    // tree's headers, check that the prebuilt ones are up to date.
    if let Some(root) = source_root() {
        println!(
            "cargo:rustc-env=LIBBITWUZLA_SYS_SOURCE_ROOT={}",
            root.display()
        );
        let include = root.join("include").canonicalize().ok();
        if lib
            .include_dirs
            .iter()
            .any(|d| d.join("bitwuzla/c/bitwuzla.h").is_file() && d.canonicalize().ok() == include)
        {
            println!("cargo:rustc-cfg=libbitwuzla_sys_in_tree");
        }
    }
    generate_bindings(&lib.include_dirs);
}

/// The generated files, also checked in under `prebuilt/` for docs.rs.
const PREBUILT: [&str; 2] = ["bindings.rs", "rust_enums.rs"];

struct Library {
    include_dirs: Vec<PathBuf>,
    lib_dirs: Vec<PathBuf>,
    /// The libraries to link, libbitwuzla and its dependencies.
    libs: Vec<String>,
    version: Option<String>,
}

/// Emit the link directives: libbitwuzla of the requested kind, and its
/// dependencies of whichever kind the linker finds.
fn emit_link(lib: &Library, statik: bool) {
    for dir in &lib.lib_dirs {
        println!("cargo:rustc-link-search=native={}", dir.display());
    }
    for name in &lib.libs {
        if name == "bitwuzla" {
            let kind = if statik { "static" } else { "dylib" };
            println!("cargo:rustc-link-lib={kind}=bitwuzla");
        } else {
            println!("cargo:rustc-link-lib={name}");
        }
    }
}

/// Reject a library older than these bindings, and record its version for
/// the run-time check (see `src/version.rs`).
fn check_version(lib: &Library) {
    let min = version::MIN_BITWUZLA_VERSION;
    let dir = lib
        .lib_dirs
        .first()
        .map_or_else(String::new, |d| format!(" in {}", d.display()));
    match &lib.version {
        Some(v) => {
            assert!(
                version::is_supported_version(v),
                "Bitwuzla {v}{dir} is too old: libbitwuzla-sys {min} requires Bitwuzla {min} or newer"
            );
            println!("cargo:rustc-env=LIBBITWUZLA_SYS_BITWUZLA_VERSION={v}");
        }
        None => println!(
            "cargo:warning=Could not determine the version of Bitwuzla{dir}, \
             libbitwuzla-sys {min} requires Bitwuzla {min} or newer"
        ),
    }
}

fn env_path(var: &str) -> Option<PathBuf> {
    env::var_os(var)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}

/// The root of the enclosing Bitwuzla source tree, if any.
fn source_root() -> Option<PathBuf> {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    // <root>/src/api/rust/libbitwuzla-sys
    let root = manifest.ancestors().nth(4)?.to_path_buf();
    (root.join("meson.build").is_file() && root.join("include/bitwuzla/c/bitwuzla.h").is_file())
        .then_some(root)
}

fn locate(statik: bool) -> Library {
    if let Some(lib_dir) = env_path("BITWUZLA_LIB_DIR") {
        return from_lib_dir(lib_dir, statik);
    }
    if let Some(build_dir) = env_path("BITWUZLA_BUILD_DIR") {
        return from_build_dir(&build_dir, statik).unwrap_or_else(|e| {
            panic!(
                "BITWUZLA_BUILD_DIR={} is not a usable Bitwuzla build directory: {e}",
                build_dir.display()
            )
        });
    }
    // Skipped if it does not provide the requested kind of library.
    let mut skipped = String::new();
    if let Some(root) = source_root() {
        let build_dir = root.join("build");
        if build_dir.join(UNINSTALLED_PC).is_file() {
            match from_build_dir(&build_dir, statik) {
                Ok(lib) => return lib,
                Err(e) => {
                    let msg = format!("Not using {}: {e}", build_dir.display());
                    println!("cargo:warning={msg}");
                    skipped = format!("\n{msg}");
                }
            }
        }
    }
    probe("bitwuzla", statik).unwrap_or_else(|e| {
        panic!(
            "Could not find Bitwuzla. Set BITWUZLA_LIB_DIR (and optionally \
             BITWUZLA_INCLUDE_DIR) to a Bitwuzla installation, BITWUZLA_BUILD_DIR \
             to a Bitwuzla build directory, or make bitwuzla.pc available to \
             pkg-config.\npkg-config: {e}{skipped}"
        )
    })
}

/// Probe pkg-config without emitting link directives, which are emitted
/// only for the library that is used (see [`emit_link`]).
fn probe(name: &str, statik: bool) -> Result<Library, String> {
    let lib = pkg_config::Config::new()
        .statik(statik)
        .cargo_metadata(false)
        .probe(name)
        .map_err(|e| e.to_string())?;
    check_kind(&lib.link_paths, statik)?;
    Ok(Library {
        include_dirs: lib.include_paths,
        lib_dirs: lib.link_paths,
        libs: lib.libs,
        version: Some(lib.version),
    })
}

fn from_lib_dir(lib_dir: PathBuf, statik: bool) -> Library {
    assert!(
        lib_dir.is_dir(),
        "BITWUZLA_LIB_DIR does not exist: {}",
        lib_dir.display()
    );
    let include_dir = env_path("BITWUZLA_INCLUDE_DIR")
        .or_else(|| {
            let dir = lib_dir.join("../include");
            dir.join("bitwuzla/c/bitwuzla.h").is_file().then_some(dir)
        })
        .or_else(|| source_root().map(|root| root.join("include")))
        .unwrap_or_else(|| {
            panic!(
                "Bitwuzla headers not found. Set BITWUZLA_INCLUDE_DIR or install \
                 them to {}",
                lib_dir.join("../include").display()
            )
        });
    check_kind(std::slice::from_ref(&lib_dir), statik)
        .unwrap_or_else(|e| panic!("BITWUZLA_LIB_DIR: {e}"));
    let mut libs = vec!["bitwuzla".to_owned()];
    if statik {
        // External dependencies of the default configuration, the SAT solvers
        // are part of libbitwuzla. Other configurations need pkg-config.
        libs.extend(["mpfr", "gmp"].map(String::from));
    }
    // Installations come with a pkg-config file next to the library.
    let version = std::fs::read_to_string(lib_dir.join("pkgconfig/bitwuzla.pc"))
        .ok()
        .and_then(|pc| {
            pc.lines()
                .find_map(|l| Some(l.strip_prefix("Version:")?.trim().to_owned()))
        });
    Library {
        include_dirs: vec![include_dir],
        lib_dirs: vec![lib_dir],
        libs,
        version,
    }
}

/// The uninstalled pkg-config file meson generates in a build directory.
const UNINSTALLED_PC: &str = "meson-uninstalled/bitwuzla-uninstalled.pc";

/// Use the uninstalled pkg-config file of a build directory.
fn from_build_dir(build_dir: &Path, statik: bool) -> Result<Library, String> {
    let pc = build_dir.join(UNINSTALLED_PC);
    if !pc.is_file() {
        return Err(format!("{} not found", pc.display()));
    }
    let old = env::var_os("PKG_CONFIG_PATH");
    let pc_dir = pc.parent().unwrap().to_path_buf();
    let path =
        env::join_paths(std::iter::once(pc_dir).chain(old.iter().flat_map(env::split_paths)))
            .map_err(|e| e.to_string())?;
    // SAFETY: build scripts are single-threaded.
    unsafe { env::set_var("PKG_CONFIG_PATH", path) };
    let lib = probe("bitwuzla-uninstalled", statik);
    // Restored for the pkg-config lookup in case this build directory is
    // skipped. SAFETY: as above.
    unsafe {
        match old {
            Some(old) => env::set_var("PKG_CONFIG_PATH", old),
            None => env::remove_var("PKG_CONFIG_PATH"),
        }
    }
    lib
}

/// The library directories must contain the requested kind of library: for
/// `static`, the linker would otherwise silently link a shared one, and
/// otherwise, it would fail to link a static one without its dependencies.
fn check_kind(lib_dirs: &[PathBuf], statik: bool) -> Result<(), String> {
    // Nothing to check if pkg-config reports no directory.
    if lib_dirs.is_empty() {
        return Ok(());
    }
    let has = |name: &str| lib_dirs.iter().any(|d| d.join(name).is_file());
    let dirs: Vec<_> = lib_dirs.iter().map(|d| d.display().to_string()).collect();
    let dirs = dirs.join(", ");
    if statik {
        if has("libbitwuzla.a") {
            return Ok(());
        }
        return Err(format!(
            "the `static` feature needs libbitwuzla.a, which is not in {dirs} \
             (configure Bitwuzla with --static)"
        ));
    }
    if shared_library_names().iter().any(|name| has(name)) {
        return Ok(());
    }
    let hint = if has("libbitwuzla.a") {
        "enable the `static` feature to link libbitwuzla.a, or configure \
         Bitwuzla with --shared"
    } else {
        "configure Bitwuzla with --shared"
    };
    Err(format!("no shared libbitwuzla in {dirs} ({hint})"))
}

/// The file names the linker looks for to link libbitwuzla dynamically.
fn shared_library_names() -> &'static [&'static str] {
    match env::var("CARGO_CFG_TARGET_OS").as_deref() {
        Ok("windows") => &["libbitwuzla.dll.a", "bitwuzla.lib"],
        Ok("macos" | "ios") => &["libbitwuzla.dylib"],
        _ => &["libbitwuzla.so"],
    }
}

/// Symlink the shared library into `OUT_DIR`.
///
/// Cargo only adds library search paths inside the target directory to the
/// dynamic library path of `cargo test` and `cargo run`, so this makes tests,
/// doctests, and examples find `libbitwuzla` without further setup.
fn expose_shared_library(lib_dirs: &[PathBuf]) {
    #[cfg(unix)]
    {
        let out = PathBuf::from(env::var("OUT_DIR").unwrap()).join("lib");
        let _ = std::fs::remove_dir_all(&out);
        std::fs::create_dir_all(&out).unwrap();
        let mut found = false;
        for dir in lib_dirs {
            let Ok(entries) = std::fs::read_dir(dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let name = entry.file_name();
                let name = name.to_string_lossy();
                let is_shared = name.starts_with("libbitwuzla.so")
                    || (name.starts_with("libbitwuzla") && name.ends_with(".dylib"));
                if is_shared && !out.join(&*name).exists() {
                    std::os::unix::fs::symlink(entry.path(), out.join(&*name)).unwrap();
                    found = true;
                }
            }
        }
        if found {
            println!("cargo:rustc-link-search=native={}", out.display());
        }
    }
    #[cfg(not(unix))]
    let _ = lib_dirs;
}

fn link_cxx_stdlib() {
    let target = env::var("TARGET").unwrap();
    if target.contains("msvc") {
        return;
    }
    if target.contains("apple") || target.contains("freebsd") {
        println!("cargo:rustc-link-lib=c++");
    } else {
        println!("cargo:rustc-link-lib=stdc++");
    }
}

/// The C enums with a Rust enum counterpart: C name, Rust name, variant
/// prefix, sentinel variant.
const ENUMS: [(&str, &str, &str, Option<&str>); 4] = [
    (
        "BitwuzlaKind",
        "Kind",
        "BITWUZLA_KIND_",
        Some("BITWUZLA_KIND_NUM_KINDS"),
    ),
    (
        "BitwuzlaRoundingMode",
        "RoundingMode",
        "BITWUZLA_RM_",
        Some("BITWUZLA_RM_MAX"),
    ),
    (
        "BitwuzlaOption",
        "Opt",
        "BITWUZLA_OPT_",
        Some("BITWUZLA_OPT_NUM_OPTS"),
    ),
    ("BitwuzlaResult", "SatResult", "BITWUZLA_", None),
];

fn enum_info(
    enum_name: &str,
) -> Option<&'static (
    &'static str,
    &'static str,
    &'static str,
    Option<&'static str>,
)> {
    let name = enum_name.strip_prefix("enum ").unwrap_or(enum_name);
    ENUMS.iter().find(|e| e.0 == name)
}

/// Derive the Rust enums from the C enums: strip the `Bitwuzla` /
/// `BITWUZLA_<ENUM>_` prefixes, hide the sentinels, and record the variants
/// and their values (for `ALL` and the conversions).
///
/// `BitwuzlaOption` and `BitwuzlaResult` become `Opt` and `SatResult` so that
/// glob imports do not shadow `std::option::Option` and `std::result::Result`.
#[derive(Debug, Default)]
struct EnumRenamer {
    variants: Arc<Mutex<Vec<Variant>>>,
}

/// (Rust enum name, Rust variant name, value), in declaration order.
type Variant = (&'static str, String, i64);

impl ParseCallbacks for EnumRenamer {
    fn enum_variant_behavior(
        &self,
        enum_name: Option<&str>,
        variant: &str,
        _value: EnumVariantValue,
    ) -> Option<EnumVariantCustomBehavior> {
        let info = enum_info(enum_name?)?;
        (info.3 == Some(variant)).then_some(EnumVariantCustomBehavior::Hide)
    }

    fn item_name(&self, info: ItemInfo<'_>) -> Option<String> {
        match info.kind {
            ItemKind::Type => enum_info(info.name).map(|e| e.1.to_owned()),
            _ => None,
        }
    }

    fn enum_variant_name(
        &self,
        enum_name: Option<&str>,
        variant: &str,
        value: EnumVariantValue,
    ) -> Option<String> {
        let info = enum_info(enum_name?)?;
        let name = pascal_case(variant.strip_prefix(info.2)?);
        if info.3 != Some(variant) {
            let value = match value {
                EnumVariantValue::Boolean(v) => i64::from(v),
                EnumVariantValue::Signed(v) => v,
                EnumVariantValue::Unsigned(v) => v as i64,
            };
            let mut variants = self.variants.lock().unwrap();
            let entry = (info.1, name.clone(), value);
            if !variants.contains(&entry) {
                variants.push(entry);
            }
        }
        Some(name)
    }
}

/// `UPPER_SNAKE_CASE` to `PascalCase`.
fn pascal_case(s: &str) -> String {
    s.split('_')
        .filter(|w| !w.is_empty())
        .map(|w| {
            let mut c = w.chars();
            let first = c.next().unwrap();
            first.to_ascii_uppercase().to_string() + &c.as_str().to_ascii_lowercase()
        })
        .collect()
}

/// The doc comments of the C headers are written for Doxygen, which renders
/// indented blocks as code. rustdoc does too, but compiles them as doctests.
#[derive(Debug)]
struct DocComments;

impl bindgen::callbacks::ParseCallbacks for DocComments {
    fn process_comment(&self, comment: &str) -> Option<String> {
        Some(fence_indented_blocks(comment))
    }
}

/// Wrap the indented code blocks of Markdown text `doc` in `text` fences.
fn fence_indented_blocks(doc: &str) -> String {
    let indent = |line: &str| line.len() - line.trim_start_matches(' ').len();
    let blank = |line: &str| line.trim().is_empty();
    let lines: Vec<&str> = doc.lines().collect();
    // rustdoc strips the indentation common to all lines.
    let base = lines
        .iter()
        .filter(|l| !blank(l))
        .map(|l| indent(l))
        .min()
        .unwrap_or(0);
    let code = base + 4;
    let mut out = Vec::new();
    let mut fenced = false;
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
        }
        // An indented code block starts after a blank line.
        if !fenced && !blank(line) && indent(line) >= code && (i == 0 || blank(lines[i - 1])) {
            let mut end = i;
            while end < lines.len() && (blank(lines[end]) || indent(lines[end]) >= code) {
                end += 1;
            }
            while blank(lines[end - 1]) {
                end -= 1;
            }
            let pad = " ".repeat(base);
            out.push(format!("{pad}```text"));
            for &l in &lines[i..end] {
                out.push(if blank(l) {
                    String::new()
                } else {
                    format!("{pad}{}", &l[code..])
                });
            }
            out.push(format!("{pad}```"));
            i = end;
        } else {
            out.push(line.to_string());
            i += 1;
        }
    }
    out.join("\n")
}

fn builder(include_dirs: &[PathBuf]) -> bindgen::Builder {
    let mut builder = bindgen::Builder::default()
        .header("wrapper.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .parse_callbacks(Box::new(DocComments))
        .rust_edition(bindgen::RustEdition::Edition2024)
        .formatter(bindgen::Formatter::Prettyplease)
        .generate_comments(true)
        .layout_tests(false);
    for dir in include_dirs {
        builder = builder.clang_arg(format!("-I{}", dir.display()));
    }
    builder
}

/// Generate `bindings.rs` (the C API, with C names) and `rust_enums.rs` (Rust
/// enums for the `bitwuzla` crate, see `lib.rs`) into `OUT_DIR`.
fn generate_bindings(include_dirs: &[PathBuf]) {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    builder(include_dirs)
        .allowlist_function("bitwuzla_.*")
        .allowlist_type("Bitwuzla.*")
        // Declared by hand in lib.rs: the callback must use the "C-unwind" ABI.
        .blocklist_function("bitwuzla_set_abort_callback")
        // FILE is opaque to the C API. Its definition and the reserved C
        // library typedefs it pulls in differ between platforms and would make
        // the bindings (and the prebuilt ones) platform-dependent.
        .blocklist_type("FILE|_IO_.*|_iobuf|__.*")
        .raw_line("pub use libc::FILE;")
        .prepend_enum_name(false)
        // Errors are reported by unwinding out of the abort callback, through
        // the C API function, back into Rust. Only matches named functions,
        // callback types keep the C ABI.
        .override_abi(bindgen::Abi::CUnwind, "bitwuzla_.*")
        .generate()
        .expect("Unable to generate Bitwuzla bindings")
        .write_to_file(out_dir.join("bindings.rs"))
        .expect("Couldn't write bindings.rs");

    let renamer = EnumRenamer::default();
    let variants = Arc::clone(&renamer.variants);
    let c_names = ENUMS.map(|e| e.0).join("|");
    let enums = builder(include_dirs)
        .parse_callbacks(Box::new(renamer))
        .allowlist_type(&c_names)
        // Releases add kinds and options, rounding modes and results are fixed.
        .rustified_non_exhaustive_enum("BitwuzlaKind|BitwuzlaOption")
        .rustified_enum("BitwuzlaRoundingMode|BitwuzlaResult")
        .generate()
        .expect("Unable to generate Bitwuzla enums")
        .to_string();

    // `ALL` lists the variants in declaration order; the conversions map
    // between a Rust enum and its C type in `libbitwuzla-sys`.
    let variants = variants.lock().unwrap();
    let mut ext = String::new();
    for (c_name, rust_name, _, _) in ENUMS {
        let vars: Vec<_> = variants.iter().filter(|v| v.0 == rust_name).collect();
        assert!(!vars.is_empty(), "no variants recorded for {rust_name}");
        let all: String = vars
            .iter()
            .map(|v| format!("        {rust_name}::{},\n", v.1))
            .collect();
        let arms: String = vars
            .iter()
            .map(|v| format!("            {} => Ok({rust_name}::{}),\n", v.2, v.1))
            .collect();
        let c_type = format!("::libbitwuzla_sys::{c_name}");
        write!(
            ext,
            "\nimpl {rust_name} {{\n    \
             /// All values of this enum, in declaration order.\n    \
             pub const ALL: &'static [{rust_name}] = &[\n{all}    ];\n}}\n\
             \n\
             impl From<{rust_name}> for {c_type} {{\n    \
             fn from(value: {rust_name}) -> Self {{\n        \
             value as Self\n    \
             }}\n\
             }}\n\
             \n\
             impl TryFrom<{c_type}> for {rust_name} {{\n    \
             type Error = {c_type};\n\
             \n    \
             /// Fails (returning `value`) for values without a variant.\n    \
             fn try_from(value: {c_type}) -> ::core::result::Result<Self, Self::Error> {{\n        \
             match value {{\n\
             {arms}            \
             _ => Err(value),\n        \
             }}\n    \
             }}\n\
             }}\n",
        )
        .unwrap();
    }
    std::fs::write(out_dir.join("rust_enums.rs"), enums + &ext)
        .expect("Couldn't write rust_enums.rs");
}
