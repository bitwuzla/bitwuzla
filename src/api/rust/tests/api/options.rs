//! Options (test_api.cpp: Options).
//!
//! The C++ `set` overloads for names (`set(lng, value)`) and command line
//! arguments (`set(args)`) correspond to `set_by_name` and `set_args`.

use bitwuzla::{Opt, OptionKind, Options};

use crate::common::has_sat_solver;

#[test]
fn options_set() {
    {
        let mut opts = Options::new();
        assert_err!(opts.set_by_name("incrremental", "true"));
        assert_err!(opts.set(Opt::Verbosity, 5));
        assert_err!(opts.set_by_name("VERBOSITY", "5"));
    }
    {
        let mut opts = Options::new();
        assert_eq!(opts.get(Opt::ProduceUnsatCores), 0);
        opts.set(Opt::ProduceUnsatCores, true).unwrap();
        assert_eq!(opts.get(Opt::ProduceUnsatCores), 1);

        assert_eq!(opts.get(Opt::Verbosity), 0);
        opts.set(Opt::Verbosity, 2).unwrap();
        assert_eq!(opts.get(Opt::Verbosity), 2);
        opts.set_by_name("verbosity", "3").unwrap();
        assert_eq!(opts.get(Opt::Verbosity), 3);
        assert_err!(opts.set_by_name("verbositi", "3"));

        assert_eq!(opts.get_mode(Opt::BvSolver), "bitblast");
        opts.set(Opt::BvSolver, "prop").unwrap();
        assert_eq!(opts.get_mode(Opt::BvSolver), "prop");
        opts.set(Opt::BvSolver, "bitblast").unwrap();
        assert_eq!(opts.get_mode(Opt::BvSolver), "bitblast");
        if has_sat_solver("cadical") {
            opts.set(Opt::SatSolver, "cadical").unwrap();
            assert_eq!(opts.get_mode(Opt::SatSolver), "cadical");
        }
        for solver in ["kissat", "cms"] {
            if has_sat_solver(solver) {
                opts.set_by_name("sat-solver", solver).unwrap();
                assert_eq!(opts.get_mode(Opt::SatSolver), solver);
            }
        }
        assert_err!(opts.set_by_name("sat--solver", "kissat"));
        assert_err!(opts.set(Opt::BvSolver, "asdf"));
    }
    {
        let mut opts = Options::new();
        opts.set_by_name("prop-nprops", "18446744073709551615") // u64::MAX
            .unwrap();
        assert_eq!(opts.get(Opt::PropNprops), u64::MAX);
        assert_err!(opts.set_by_name("prop-nprops", "99999999999999999999999999"));
        assert_err!(opts.set_by_name("prop-nprops", "foo"));
        assert_err!(opts.set_by_name("prop-nprops", "123abc"));
        // The same via the typed interface.
        let mut opts = Options::new();
        opts.set(Opt::PropNprops, u64::MAX).unwrap();
        assert_eq!(opts.get(Opt::PropNprops), u64::MAX);
    }
    {
        // Error checking of the typed set/get overloads.
        let mut opts = Options::new();
        // numeric value on a non-numeric (mode) option
        assert_panics!(
            opts.set(Opt::BvSolver, 1u64),
            "expected numeric option, --bv-solver takes an option mode"
        );
        // the type is checked before the value
        assert_panics!(opts.set(Opt::BvSolver, -1), "expected numeric option");
        // Boolean and numeric values are not interchangeable
        assert_panics!(
            opts.set(Opt::ProduceModels, 1),
            "expected numeric option, --produce-models takes a Boolean"
        );
        assert_panics!(
            opts.set(Opt::Verbosity, true),
            "expected Boolean option, --verbosity takes a number"
        );
        // numeric value below the option minimum (nthreads minimum is 1)
        assert_err!(opts.set(Opt::Nthreads, 0u64), "expected value >= 1");
        // negative value
        assert_err!(opts.set(Opt::Verbosity, -1), "expected value >= 0");
        // string value on a numeric option
        assert_panics!(
            opts.set(Opt::Verbosity, "x"),
            "expected option with option modes or strings, --verbosity takes a number"
        );
        // get (numeric) on a mode option
        assert_panics!(
            opts.get(Opt::BvSolver),
            "expected Boolean or numeric option"
        );
        // get_mode on a non-mode (numeric) option
        assert_panics!(
            opts.get_mode(Opt::Verbosity),
            "expected option with option modes"
        );
        // get_str on a non-string (mode) option
        assert_panics!(opts.get_str(Opt::BvSolver), "expected string option");
        // invalid option name lookup
        assert_eq!(opts.option("nonsense"), None);
    }
    {
        // Error checking of the string (long name) set interface.
        let mut opts = Options::new();
        // invalid value for a Boolean option
        assert_err!(opts.set_by_name("produce-models", "yes"));
        // empty option name and empty value
        assert_err!(opts.set_by_name("", "1"));
        assert_err!(opts.set_by_name("verbosity", ""));
        // numeric value above the option maximum (verbosity maximum is 4)
        assert_err!(opts.set_by_name("verbosity", "5"));
        // numeric value below the option minimum (nthreads minimum is 1)
        assert_err!(opts.set_by_name("nthreads", "0"));
        assert_eq!(opts.get(Opt::Verbosity), 0);
        assert_eq!(opts.get(Opt::Nthreads), 1);
    }
    {
        // Lookup by long and short name.
        let opts = Options::new();
        assert_eq!(opts.option("produce-models"), Some(Opt::ProduceModels));
        assert_eq!(opts.option("m"), Some(Opt::ProduceModels));
        assert_eq!(opts.lng(Opt::ProduceModels), "produce-models");
        assert_eq!(opts.shrt(Opt::ProduceModels).as_deref(), Some("m"));
    }
}

#[test]
fn option_set_args() {
    let mut options = Options::new();
    options.set_args(["-v", "-v"]).unwrap();
    assert_eq!(options.get(Opt::Verbosity), 2);
    options.set_args(["-v", "3"]).unwrap();
    assert_eq!(options.get(Opt::Verbosity), 3);
    options.set_args(["-v=4"]).unwrap();
    assert_eq!(options.get(Opt::Verbosity), 4);
    options.set_args(["-v=4"]).unwrap();
    assert_eq!(options.get(Opt::Verbosity), 4);
    assert_err!(options.set_args(["-v=100"]));
    if has_sat_solver("cadical") {
        options.set_args(["-S=cadical"]).unwrap();
        assert_eq!(options.get_mode(Opt::SatSolver), "cadical");
    }
    assert_err!(options.set_args(["--no-verbosity"]));
    // invalid mode value
    assert_err!(options.set_args(["-S=foo"]));
    // invalid Boolean value
    assert_err!(options.set_args(["--produce-models=yes"]));
    // invalid numeric value
    assert_err!(options.set_args(["--prop-nprops=foo"]));
    assert_err!(options.set_args(["-v=3x"]));
    assert_err!(options.set_args(["--prop-nprops=99999999999999999999999"]));
    assert_eq!(options.get(Opt::Verbosity), 4);
}

#[test]
fn option_info() {
    for &opt in Opt::ALL {
        let options = Options::new();
        let info = options.info(opt);
        assert_eq!(info.opt, opt);
        match &info.kind {
            OptionKind::Bool { cur, .. } => {
                assert!(options.is_bool(opt));
                assert!(!options.is_numeric(opt));
                assert_eq!(u64::from(*cur), options.get(opt));
            }
            OptionKind::Numeric { cur, min, max, .. } => {
                assert!(options.is_numeric(opt));
                assert!(!options.is_bool(opt));
                assert_eq!(*cur, options.get(opt));
                assert!(cur >= min);
                assert!(cur <= max);
            }
            OptionKind::Mode { cur, modes, .. } => {
                assert!(options.is_mode(opt));
                assert_eq!(&options.get_mode(opt), cur);
                assert!(modes.contains(cur));
                assert_eq!(&options.modes(opt), modes);
            }
            OptionKind::String { cur, .. } => {
                assert!(options.is_str(opt));
                assert_eq!(&options.get_str(opt), cur);
            }
        }
        assert!(!info.description.is_empty());
        assert_eq!(options.option(&info.lng), Some(opt));
        if let Some(shrt) = &info.shrt {
            assert_eq!(options.option(shrt), Some(opt));
        }
    }
}

#[test]
fn option_is_valid() {
    let options = Options::new();
    assert!(!options.is_valid("incremental"));
    assert!(options.is_valid("produce-models"));
}
