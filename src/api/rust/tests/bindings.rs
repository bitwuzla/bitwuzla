//! Tests of Rust-binding specific behavior (error recovery, ownership,
//! terminators) that has no counterpart in the C++ API tests.

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::Once;

use bitwuzla::{Bitwuzla, Kind, Opt, Options, Parser, RoundingMode, SatResult, Term, TermManager};

/// Run `f`, which must panic, and return the panic message.
fn panic_message(f: impl FnOnce()) -> String {
    let payload =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).expect_err("expected a panic");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
}

thread_local! {
    static PANIC_LOCATION: RefCell<Option<(String, u32)>> = const { RefCell::new(None) };
}

/// Run `f`, which must panic, and return the location the panic reports.
fn panic_location(f: impl FnOnce()) -> (String, u32) {
    static HOOK: Once = Once::new();
    HOOK.call_once(|| {
        // Record the location for panics on threads that ask for it, keep
        // the default behavior for all others.
        let default = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if PANIC_LOCATION.with(|l| l.borrow().is_some()) {
                let loc = info.location().unwrap();
                PANIC_LOCATION.with(|l| *l.borrow_mut() = Some((loc.file().into(), loc.line())));
            } else {
                default(info)
            }
        }));
    });
    PANIC_LOCATION.with(|l| *l.borrow_mut() = Some((String::new(), 0)));
    panic_message(f);
    PANIC_LOCATION.with(|l| l.borrow_mut().take()).unwrap()
}

#[test]
fn contract_violations_panic_and_are_recoverable() {
    let tm = TermManager::new();
    // Error raised by a C API check.
    let msg = panic_message(|| {
        let _ = tm.mk_bv_sort(0);
    });
    assert!(msg.contains("must be > 0"), "{msg}");
    assert!(!msg.starts_with("bitwuzla: error:"), "{msg}");
    // Error raised by the C++ API.
    let bv8 = tm.mk_bv_sort(8);
    let x = tm.mk_const(&bv8, "x");
    let msg = panic_message(|| {
        let _ = tm.mk_term(Kind::Not, &[&x], &[]);
    });
    assert!(msg.contains("unexpected sort"), "{msg}");
    // The term manager is still usable.
    assert_eq!(tm.mk_term(Kind::BvNot, &[&x], &[]).kind(), Kind::BvNot);
}

#[test]
fn panics_report_the_caller_location() {
    let tm = TermManager::new();
    let bv8 = tm.mk_bv_sort(8);
    let x = tm.mk_const(&bv8, "x");
    let mut bitwuzla = Bitwuzla::new(&tm, &Options::new()).unwrap();
    let here = |line| (file!().to_string(), line);
    let line = line!() + 2;
    let loc = panic_location(|| {
        let _ = tm.mk_bv_sort(0);
    });
    assert_eq!(loc, here(line));
    let line = line!() + 2;
    let loc = panic_location(|| {
        let _ = tm.mk_term(Kind::Not, &[&x], &[]);
    });
    assert_eq!(loc, here(line));
    let line = line!() + 2;
    let loc = panic_location(|| {
        let _ = x.sort().fp_exp_size();
    });
    assert_eq!(loc, here(line));
    let line = line!() + 1;
    let loc = panic_location(|| bitwuzla.assert_formula(&x));
    assert_eq!(loc, here(line));
    let line = line!() + 2;
    let loc = panic_location(|| {
        let _ = bitwuzla.get_value(&x);
    });
    assert_eq!(loc, here(line));
    let mut options = Options::new();
    let line = line!() + 2;
    let loc = panic_location(|| {
        let _ = options.set(Opt::Verbosity, "x");
    });
    assert_eq!(loc, here(line));
}

#[test]
fn errors_on_other_threads() {
    // The abort callback is configured per thread.
    std::thread::spawn(|| {
        let tm = TermManager::new();
        let msg = panic_message(|| {
            let _ = tm.mk_bv_sort(0);
        });
        assert!(msg.contains("must be > 0"), "{msg}");
        let bv8 = tm.mk_bv_sort(8);
        assert!(tm.mk_bv_value(&bv8, "2", 2).is_err());
    })
    .join()
    .unwrap();
}

#[test]
fn mixing_term_managers_panics() {
    let tm1 = TermManager::new();
    let tm2 = TermManager::new();
    let bv8 = tm1.mk_bv_sort(8);
    let x = tm1.mk_const(&bv8, "x");
    let msg = panic_message(|| {
        let _ = tm2.mk_term(Kind::BvNot, &[&x], &[]);
    });
    assert!(msg.contains("mismatching term manager"), "{msg}");
    let msg = panic_message(|| {
        let _ = tm2.mk_const(&bv8, "y");
    });
    assert!(msg.contains("mismatching term manager"), "{msg}");
    let mut bitwuzla = Bitwuzla::new(&tm2, &Options::new()).unwrap();
    let eq = tm1.mk_term(Kind::Equal, &[&x, &x], &[]);
    let msg = panic_message(|| bitwuzla.assert_formula(&eq));
    assert!(msg.contains("mismatching term manager"), "{msg}");
}

#[test]
fn enums_display() {
    // Bitwuzla's names, padded like strings.
    assert_eq!(Kind::ArraySelect.to_string(), "SELECT");
    assert_eq!(
        format!(
            "[{:>6}|{:<4}|{:^7}]",
            SatResult::Sat,
            RoundingMode::Rne,
            Kind::Not
        ),
        "[   sat|RNE |  NOT  ]"
    );
}

#[test]
fn interior_nul() {
    let tm = TermManager::new();
    let bv8 = tm.mk_bv_sort(8);
    // Panics in symbols, an error in input strings.
    let msg = panic_message(|| {
        let _ = tm.mk_const(&bv8, "a\0b");
    });
    assert!(msg.contains("NUL"), "{msg}");
    let e = tm.mk_bv_value(&bv8, "1\0", 10).unwrap_err();
    assert!(e.message().contains("NUL"), "{e}");
    let mut options = Options::new();
    let e = options.set_by_name("verbosity\0", "1").unwrap_err();
    assert!(e.message().contains("NUL"), "{e}");
    let e = options.set_args(["-v", "1\0"]).unwrap_err();
    assert!(e.message().contains("NUL"), "{e}");
    assert_eq!(options.option("verbosity\0"), None);
    let mut parser = Parser::new(&tm, &options, "smt2", 2, "<stdout>").unwrap();
    let e = parser.parse_str("(set-logic QF_BV)\0").unwrap_err();
    assert!(e.message().contains("NUL"), "{e}");
    let e = parser.parse_file("a\0b.smt2").unwrap_err();
    assert!(e.message().contains("NUL"), "{e}");
}

#[test]
fn objects_outlive_term_manager() {
    let (t, s, children, mut bitwuzla) = {
        let tm = TermManager::new();
        let bv8 = tm.mk_bv_sort(8);
        let x = tm.mk_const(&bv8, "x");
        let y = tm.mk_const(&bv8, "y");
        let add = tm.mk_term(Kind::BvAdd, &[&x, &y], &[]);
        let bitwuzla = Bitwuzla::new(&tm, &Options::new()).unwrap();
        (add.clone(), bv8, add.children(), bitwuzla)
    };
    assert_eq!(t.kind(), Kind::BvAdd);
    assert_eq!(s.bv_size(), 8);
    assert!(children.iter().all(Term::is_const));
    let eq = bitwuzla
        .term_manager()
        .mk_term(Kind::Equal, &[&t, &children[0]], &[]);
    bitwuzla.assert_formula(&eq);
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
}

#[test]
fn options_outlive_options_value() {
    // The solver logs to the diagnostic output stream owned by its options,
    // which must stay alive after the `Options` value is dropped.
    let log = std::env::temp_dir().join(format!("bitwuzla-rs-{}-diag.log", std::process::id()));
    let tm = TermManager::new();
    let mut bitwuzla = {
        let mut options = Options::new();
        options.set(Opt::Verbosity, 2).unwrap();
        options
            .set_diagnostic_output_stream(log.to_str().unwrap())
            .unwrap();
        Bitwuzla::new(&tm, &options).unwrap()
    };
    let bv8 = tm.mk_bv_sort(8);
    let x = tm.mk_const(&bv8, "x");
    bitwuzla.assert_formula(&tm.mk_term(Kind::Equal, &[&x, &x], &[]));
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
    drop(bitwuzla);
    let content = std::fs::read_to_string(&log).unwrap();
    let _ = std::fs::remove_file(&log);
    assert!(!content.is_empty());
}

/// A formula that takes long to solve (unsat multiplication commutativity).
fn hard_formula(tm: &TermManager) -> Term {
    let bv = tm.mk_bv_sort(32);
    let x = tm.mk_const(&bv, "x");
    let y = tm.mk_const(&bv, "y");
    let xy = tm.mk_term(Kind::BvMul, &[&x, &y], &[]);
    let yx = tm.mk_term(Kind::BvMul, &[&y, &x], &[]);
    tm.mk_term(Kind::Distinct, &[&xy, &yx], &[])
}

#[test]
fn terminator_closure() {
    let tm = TermManager::new();
    let mut options = Options::new();
    options.set(Opt::RewriteLevel, 0).unwrap();
    let mut bitwuzla = Bitwuzla::new(&tm, &options).unwrap();
    bitwuzla.assert_formula(&hard_formula(&tm));
    let calls = Rc::new(Cell::new(0u64));
    let c = Rc::clone(&calls);
    bitwuzla
        .configure_terminator(move || {
            c.set(c.get() + 1);
            true
        })
        .unwrap();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
    assert!(calls.get() > 0);

    // A cleared terminator is no longer queried.
    bitwuzla.clear_terminator();
    let before = calls.get();
    bitwuzla.push(1);
    bitwuzla.assert_formula(&tm.mk_false());
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    assert_eq!(calls.get(), before);
}

#[test]
fn terminator_panic_is_resumed() {
    let tm = TermManager::new();
    let mut options = Options::new();
    options.set(Opt::RewriteLevel, 0).unwrap();
    let mut bitwuzla = Bitwuzla::new(&tm, &options).unwrap();
    bitwuzla.assert_formula(&hard_formula(&tm));
    bitwuzla
        .configure_terminator(|| panic!("terminator panicked"))
        .unwrap();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| bitwuzla.check_sat()));
    let payload = res.unwrap_err();
    assert_eq!(payload.downcast_ref::<&str>(), Some(&"terminator panicked"));
    // The solver is still usable.
    bitwuzla.clear_terminator();
    bitwuzla.push(1);
    bitwuzla.assert_formula(&tm.mk_false());
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
}

#[test]
fn parser_bitwuzla_borrowed() {
    let tm = TermManager::new();
    let mut parser = Parser::new(&tm, &Options::new(), "smt2", 2, "<stdout>").unwrap();
    // Not initialized before the first command that needs it.
    assert!(parser.bitwuzla().is_none());
    parser
        .parse_str("(set-logic QF_BV)(declare-const x (_ BitVec 8))")
        .unwrap();
    let x = parser.get_declared_funs().pop().unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();
    let one = bitwuzla.term_manager().mk_bv_one(&x.sort());
    let eq = tm.mk_term(Kind::Equal, &[&x, &one], &[]);
    bitwuzla.assert_formula(&eq);
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
    // The parser owns the instance; dropping the wrapper does not delete it.
    assert_eq!(
        parser.bitwuzla().unwrap().check_sat().unwrap(),
        SatResult::Sat
    );
    let e = parser.parse_str("(assert y)").unwrap_err();
    assert!(e.message().contains("undefined symbol 'y'"), "{e}");
}

#[test]
fn parser_parse_only_and_paths() {
    let dir = std::env::temp_dir();
    let id = std::process::id();
    let input = dir.join(format!("bitwuzla-rs-{id}-check-sat.smt2"));
    std::fs::write(&input, "(check-sat)\n").unwrap();
    let outfile = dir.join(format!("bitwuzla-rs-{id}-parse-only.out"));
    {
        let tm = TermManager::new();
        let mut parser =
            Parser::new(&tm, &Options::new(), "smt2", 2, outfile.to_str().unwrap()).unwrap();
        // Parse-only mode applies to all subsequent calls until disabled.
        parser.configure_parse_only(true);
        parser.parse_str("(set-logic QF_BV)(check-sat)").unwrap();
        parser.parse_file(&input).unwrap();
        parser.configure_parse_only(false);
        parser.parse_str("(check-sat)").unwrap();
        // Any AsRef<Path>.
        parser.parse_file(input.to_str().unwrap()).unwrap();
        parser.parse_file(input.clone()).unwrap();
        // Paths are bytes on Unix, they need not be valid UTF-8.
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            let mut name = format!("bitwuzla-rs-{id}-").into_bytes();
            name.extend_from_slice(b"\xff.smt2");
            let input = dir.join(std::ffi::OsStr::from_bytes(&name));
            std::fs::write(&input, "(check-sat)\n").unwrap();
            parser.parse_file(&input).unwrap();
            std::fs::remove_file(&input).unwrap();
        }
    }
    std::fs::remove_file(&input).unwrap();
    let output = std::fs::read_to_string(&outfile).unwrap();
    std::fs::remove_file(&outfile).unwrap();
    let expected = "sat\n".repeat(if cfg!(unix) { 4 } else { 3 });
    assert_eq!(output, expected);
}

/// A parser whose solver needs a while for an assertion that the solver
/// cannot simplify away.
fn parser_with_hard_formula(tm: &TermManager) -> Parser {
    let mut options = Options::new();
    options.set(Opt::RewriteLevel, 0).unwrap();
    let mut parser = Parser::new(tm, &options, "smt2", 2, "<stdout>").unwrap();
    parser
        .parse_str(
            "(set-logic QF_BV)\
             (declare-const x (_ BitVec 32))(declare-const y (_ BitVec 32))\
             (assert (distinct (bvmul x y) (bvmul y x)))",
        )
        .unwrap();
    parser
}

#[test]
fn parser_solver_moved_out() {
    let tm = TermManager::new();
    // The moved-out instance keeps the parser alive.
    let mut parser = parser_with_hard_formula(&tm);
    let other = Bitwuzla::new(&tm, &Options::new()).unwrap();
    let mut bitwuzla = std::mem::replace(parser.bitwuzla().unwrap(), other);
    drop(parser);
    bitwuzla.push(1);
    bitwuzla.assert_formula(&tm.mk_false());
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);

    // A terminator configured on the instance stays alive while the parser
    // uses it, even if the wrapper it was configured on is dropped.
    let mut parser = parser_with_hard_formula(&tm);
    let calls = Rc::new(Cell::new(0u64));
    let c = Rc::clone(&calls);
    parser
        .bitwuzla()
        .unwrap()
        .configure_terminator(move || {
            c.set(c.get() + 1);
            true
        })
        .unwrap();
    let other = Bitwuzla::new(&tm, &Options::new()).unwrap();
    drop(std::mem::replace(parser.bitwuzla().unwrap(), other));
    parser.parse_str("(check-sat)").unwrap();
    assert!(calls.get() > 0);
}

#[test]
fn parser_solver_after_reset() {
    // The parser replaces its solver on (reset) and (reset-assertions), the
    // instance must refer to the current one.
    let tm = TermManager::new();
    let mut parser = Parser::new(&tm, &Options::new(), "smt2", 2, "<stdout>").unwrap();
    parser
        .parse_str("(set-logic QF_BV)(declare-const x Bool)(assert x)")
        .unwrap();
    assert_eq!(
        parser.bitwuzla().unwrap().check_sat().unwrap(),
        SatResult::Sat
    );
    for reset in ["(reset-assertions)", "(reset)(set-logic QF_BV)"] {
        let input = format!("{reset}(declare-const y Bool)(assert (not y))");
        parser.parse_str(&input).unwrap();
        let bitwuzla = parser.bitwuzla().unwrap();
        let assertions = bitwuzla.get_assertions();
        assert_eq!(assertions.len(), 1);
        assert_eq!(assertions[0].to_string(), "(not y)");
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
    }
}

#[test]
fn parser_terminator_panics_are_resumed() {
    let tm = TermManager::new();
    // A panic in the parser's terminator, raised while solving through the
    // parser's instance.
    let mut parser = parser_with_hard_formula(&tm);
    parser
        .configure_terminator(|| panic!("parser terminator"))
        .unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();
    assert_eq!(
        panic_message(|| {
            let _ = bitwuzla.check_sat();
        }),
        "parser terminator"
    );
    // A panic in the instance's terminator, raised while the parser solves.
    let mut parser = parser_with_hard_formula(&tm);
    parser
        .bitwuzla()
        .unwrap()
        .configure_terminator(|| panic!("solver terminator"))
        .unwrap();
    assert_eq!(
        panic_message(|| {
            let _ = parser.parse_str("(check-sat)");
        }),
        "solver terminator"
    );
    // Both are usable afterwards.
    let bitwuzla = parser.bitwuzla().unwrap();
    bitwuzla.clear_terminator();
    bitwuzla.push(1);
    bitwuzla.assert_formula(&tm.mk_false());
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
}

const IN_TERMINATOR: &str =
    "a terminator must not use Bitwuzla objects other than to clone or drop them";

#[test]
fn terminator_may_clone_and_drop() {
    let tm = TermManager::new();
    let mut options = Options::new();
    options.set(Opt::RewriteLevel, 0).unwrap();
    let mut bitwuzla = Bitwuzla::new(&tm, &options).unwrap();
    let formula = hard_formula(&tm);
    bitwuzla.assert_formula(&formula);
    let mut other = Some(Bitwuzla::new(&tm, &Options::new()).unwrap());
    let mut kept = Vec::new();
    bitwuzla
        .configure_terminator(move || {
            kept.push(formula.clone());
            kept.pop();
            drop(other.take());
            assert_eq!(Kind::Not.to_string(), "NOT");
            assert!(!bitwuzla::version().is_empty());
            true
        })
        .unwrap();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
}

#[test]
fn terminator_calls_into_bitwuzla_panic() {
    let tm = TermManager::new();
    let mut options = Options::new();
    options.set(Opt::RewriteLevel, 0).unwrap();
    let mut bitwuzla = Bitwuzla::new(&tm, &options).unwrap();
    bitwuzla.assert_formula(&hard_formula(&tm));
    let tm2 = tm.clone();
    bitwuzla
        .configure_terminator(move || {
            tm2.mk_true();
            false
        })
        .unwrap();
    assert_eq!(
        panic_message(|| {
            let _ = bitwuzla.check_sat();
        }),
        IN_TERMINATOR
    );
    // Calls are allowed again once the terminator returned.
    bitwuzla.clear_terminator();
    bitwuzla.push(1);
    bitwuzla.assert_formula(&tm.mk_false());
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
}

#[test]
fn terminator_cannot_reenter_parser_solver() {
    let tm = TermManager::new();
    let moved_out = |parser: &mut Parser| {
        std::mem::replace(
            parser.bitwuzla().unwrap(),
            Bitwuzla::new(&tm, &Options::new()).unwrap(),
        )
    };
    // The terminator replaces itself through another instance of the same
    // solver, which would free it while it runs.
    let mut parser = parser_with_hard_formula(&tm);
    let mut bitwuzla = moved_out(&mut parser);
    let mut other = moved_out(&mut parser);
    assert_eq!(bitwuzla.as_raw(), other.as_raw());
    bitwuzla
        .configure_terminator(move || {
            other.configure_terminator(|| true).unwrap();
            false
        })
        .unwrap();
    assert_eq!(
        panic_message(|| {
            let _ = bitwuzla.check_sat();
        }),
        IN_TERMINATOR
    );
    // The terminator keeps the parser alive through `other`.
    bitwuzla.clear_terminator();
    // The parser's terminator solves with the solver the parser is solving
    // with.
    let mut parser = parser_with_hard_formula(&tm);
    let mut bitwuzla = moved_out(&mut parser);
    parser
        .configure_terminator(move || {
            let _ = bitwuzla.check_sat();
            false
        })
        .unwrap();
    assert_eq!(
        panic_message(|| {
            let _ = parser.parse_str("(check-sat)");
        }),
        IN_TERMINATOR
    );
    parser.clear_terminator();
}

/// A parser whose formula is not solved by rewriting, and is terminated in
/// preprocessing if a terminator is configured, but solved quickly otherwise.
fn parser_with_small_formula(tm: &TermManager) -> Parser {
    let mut options = Options::new();
    options.set(Opt::RewriteLevel, 0).unwrap();
    let mut parser = Parser::new(tm, &options, "smt2", 2, "<stdout>").unwrap();
    parser
        .parse_str(
            "(set-logic QF_BV)\
             (declare-const x (_ BitVec 4))(declare-const s (_ BitVec 4))\
             (declare-const t (_ BitVec 4))\
             (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))",
        )
        .unwrap();
    parser
}

#[test]
fn parser_solver_clear_terminator_keeps_parser_terminator() {
    let tm = TermManager::new();
    let mut parser = parser_with_small_formula(&tm);
    parser.configure_terminator(|| true).unwrap();
    // The instance has no terminator of its own, clearing it keeps the
    // parser's.
    let bitwuzla = parser.bitwuzla().unwrap();
    bitwuzla.clear_terminator();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
    parser.configure_terminator(|| false).unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
}

#[test]
fn parser_clear_terminator() {
    let tm = TermManager::new();
    let mut parser = parser_with_small_formula(&tm);
    parser.configure_terminator(|| true).unwrap();
    assert_eq!(
        parser.bitwuzla().unwrap().check_sat().unwrap(),
        SatResult::Unknown
    );
    parser.clear_terminator();
    assert_eq!(
        parser.bitwuzla().unwrap().check_sat().unwrap(),
        SatResult::Unsat
    );
    // Without a terminator of its own, clearing keeps the solver's.
    let mut parser = parser_with_small_formula(&tm);
    parser
        .bitwuzla()
        .unwrap()
        .configure_terminator(|| true)
        .unwrap();
    parser.clear_terminator();
    assert_eq!(
        parser.bitwuzla().unwrap().check_sat().unwrap(),
        SatResult::Unknown
    );
}

#[test]
fn term_and_sort_ids() {
    let tm = TermManager::new();
    let bv8 = tm.mk_bv_sort(8);
    let x = tm.mk_const(&bv8, "x");
    let y = tm.mk_const(&bv8, "y");
    assert_ne!(x.id(), y.id());
    assert_eq!(x.id(), x.clone().id());
    assert_eq!(tm.mk_true().id(), tm.mk_true().id());
    assert_ne!(bv8.id(), tm.mk_bool_sort().id());
    assert_eq!(bv8.id(), tm.mk_bv_sort(8).id());
}

#[test]
fn fallible_calls_check_term_manager() {
    let tm1 = TermManager::new();
    let tm2 = TermManager::new();
    let bv8 = tm1.mk_bv_sort(8);
    let rm = tm1.mk_rm_value(RoundingMode::Rne);
    let fp16 = tm1.mk_fp_sort(5, 11);
    let x = tm1.mk_const(&tm1.mk_bool_sort(), "x");
    let mut bitwuzla = Bitwuzla::new(&tm2, &Options::new()).unwrap();
    for msg in [
        panic_message(|| {
            let _ = bitwuzla.check_sat_assuming(&[&x]);
        }),
        panic_message(|| {
            let _ = bitwuzla.simplify_term(&x);
        }),
        panic_message(|| {
            let _ = bitwuzla.get_interpolant(&[&x]);
        }),
        panic_message(|| {
            let _ = tm2.mk_bv_value(&bv8, "1", 2);
        }),
        panic_message(|| {
            let _ = tm2.mk_fp_from_real(&tm2.mk_fp_sort(5, 11), &rm, "1.0");
        }),
        panic_message(|| {
            let _ = tm2.mk_fp_from_rational(&fp16, &tm2.mk_rm_value(RoundingMode::Rne), "1", "2");
        }),
    ] {
        assert!(msg.contains("mismatching term manager"), "{msg}");
    }
    // Other contract violations the bindings check before calling Bitwuzla.
    let msg = panic_message(|| {
        let _ = tm1.mk_bv_value(&bv8, "1", 3);
    });
    assert!(msg.contains("invalid base 3"), "{msg}");
    let msg = panic_message(|| {
        let _ = tm1.mk_bv_value(&fp16, "1", 2);
    });
    assert!(msg.contains("expected bit-vector sort"), "{msg}");
    let msg = panic_message(|| {
        let _ = tm1.mk_fp_from_real(&fp16, &x, "1.0");
    });
    assert!(msg.contains("expected rounding mode term"), "{msg}");
}

#[test]
fn print_formula_errors_depend_on_the_formula() {
    let tm = TermManager::new();
    let mut bitwuzla = Bitwuzla::new(&tm, &Options::new()).unwrap();
    let fp16 = tm.mk_fp_sort(5, 11);
    let x = tm.mk_const(&fp16, "x");
    bitwuzla.assert_formula(&tm.mk_term(Kind::FpIsNan, &[&x], &[]));
    assert!(bitwuzla.print_formula("smt2", 2).is_ok());
    let e = bitwuzla.print_formula("btor2", 2).unwrap_err();
    assert!(e.message().contains("BTOR2"), "{e}");
}

#[test]
fn substitute_checks_term_manager() {
    let tm1 = TermManager::new();
    let tm2 = TermManager::new();
    let bv8 = tm1.mk_bv_sort(8);
    let z = tm1.mk_const(&bv8, "z");
    let zz = tm1.mk_term(Kind::BvAdd, &[&z, &z], &[]);
    let msg = panic_message(|| {
        let _ = tm2.substitute_term(&zz, [(&z, &z)]);
    });
    assert!(msg.contains("mismatching term manager"), "{msg}");
    let mut terms = vec![zz.clone()];
    let msg = panic_message(|| tm2.substitute_terms(&mut terms, [(&z, &z)]));
    assert!(msg.contains("mismatching term manager"), "{msg}");
    // Empty maps and term sets are no-ops, as in the C++ API.
    assert_eq!(tm1.substitute_term(&zz, []), zz);
    tm1.substitute_terms(&mut [], [(&z, &z)]);
    let one = tm1.mk_bv_one(&bv8);
    let res = tm1.substitute_term(&zz, [(&z, &one)]);
    assert_eq!(res.to_string(), "(bvadd #b00000001 #b00000001)");
}
