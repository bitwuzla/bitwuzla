//! The Bitwuzla versions these bindings support. Also included by the build
//! script, which rejects older libraries.

// Unused in the build script.
#![allow(dead_code)]

/// The oldest Bitwuzla version these bindings support.
///
/// This is the version of this crate: the bindings are maintained alongside
/// Bitwuzla and may rely on anything that version provides, including fixes
/// that do not change any declaration.
pub const MIN_BITWUZLA_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Whether these bindings support Bitwuzla `version`, i.e., whether it is at
/// least [`MIN_BITWUZLA_VERSION`].
///
/// `version` has the form `major.minor.patch[-suffix]`, as reported by
/// pkg-config or [`bitwuzla_version`](crate::bitwuzla_version). A version with
/// a suffix (e.g., `0.10.0-dev`) is a development version after the release
/// without it. Versions of any other form are not supported.
pub fn is_supported_version(version: &str) -> bool {
    at_least(version, MIN_BITWUZLA_VERSION)
}

/// The version of the Bitwuzla library the bindings were generated for, if
/// the build script could determine it.
pub const BUILT_BITWUZLA_VERSION: Option<&str> = option_env!("LIBBITWUZLA_SYS_BITWUZLA_VERSION");

/// Whether a library of Bitwuzla `version`, loaded at run time, can be used
/// with these bindings: it must be supported (see [`is_supported_version`])
/// and, if known, of the release the bindings were generated for
/// ([`BUILT_BITWUZLA_VERSION`]).
///
/// Releases may renumber the values of C enums and change struct layouts,
/// so bindings generated for one release cannot use the library of another.
/// Development versions of the same release are not distinguished.
pub fn is_compatible_version(version: &str) -> bool {
    is_supported_version(version)
        && BUILT_BITWUZLA_VERSION.is_none_or(|built| same_release(version, built))
}

/// Whether two Bitwuzla versions are of the same release.
fn same_release(a: &str, b: &str) -> bool {
    matches!((parse(a), parse(b)), (Some(a), Some(b)) if a == b)
}

/// Whether Bitwuzla `version` is `min` or newer.
fn at_least(version: &str, min: &str) -> bool {
    match (parse(version), parse(min)) {
        (Some(version), Some(min)) => version >= min,
        _ => false,
    }
}

/// A version as (major, minor, patch, development version), which orders like
/// Bitwuzla versions.
fn parse(version: &str) -> Option<(u64, u64, u64, bool)> {
    let (release, dev) = match version.split_once('-') {
        Some((release, _)) => (release, true),
        None => (version, false),
    };
    let mut numbers = release.split('.').map(|n| n.parse::<u64>().ok());
    let parsed = (numbers.next()??, numbers.next()??, numbers.next()??, dev);
    numbers.next().is_none().then_some(parsed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering() {
        assert!(at_least("0.10.0", "0.10.0"));
        assert!(at_least("0.10.1", "0.10.0"));
        assert!(at_least("0.11.0", "0.10.9"));
        assert!(at_least("1.0.0", "0.10.0"));
        assert!(!at_least("0.9.10", "0.10.0"));
        // Development versions follow their release.
        assert!(at_least("0.10.0-dev", "0.10.0"));
        assert!(at_least("0.10.0-dev", "0.10.0-dev"));
        assert!(at_least("0.10.1", "0.10.0-dev"));
        assert!(!at_least("0.10.0", "0.10.0-dev"));
        assert!(!at_least("0.10.0-dev", "0.10.1"));
        // bitwuzla_version() appends the git revision to development versions.
        assert!(at_least("0.10.0-dev-main@268cc9dea", "0.10.0-dev"));
    }

    #[test]
    fn malformed() {
        for version in ["", "0.10", "0.10.0.1", "0.10.x", "v0.10.0", "0.10.0 "] {
            assert!(!at_least(version, "0.1.0"), "{version:?}");
        }
    }

    #[test]
    fn own_version_supported() {
        assert!(is_supported_version(MIN_BITWUZLA_VERSION));
    }

    #[test]
    fn releases() {
        assert!(same_release("0.10.0", "0.10.0"));
        assert!(same_release("0.10.0-dev", "0.10.0-dev-main@268cc9dea"));
        assert!(!same_release("0.10.0", "0.10.0-dev"));
        assert!(!same_release("0.10.1", "0.10.0"));
        assert!(!same_release("0.11.0", "x"));
    }
}
