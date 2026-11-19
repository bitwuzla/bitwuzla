//! SAT solver and Termination function (test_api.cpp: SAT solver,
//! Termination function).
//!
//! A C++ `Terminator` subclass corresponds to a closure; one that throws
//! corresponds to one that panics, which terminates the solver call and is
//! resumed when the call returns (`terminate_timeout_wrap`).
//! `configure_terminator(nullptr)` corresponds to `clear_terminator`.
//! Exception types are not distinguished, only messages
//! (`bitwuzla::Unsupported` in `configure_terminator_unsupported`). Whether
//! Kissat is our patched, bundled one (`kissat_patched`, a compile-time
//! constant in the C++ tests) is probed by configuring a terminator.

use std::panic::{self, AssertUnwindSafe};
use std::time::{Duration, Instant};

use bitwuzla::{Bitwuzla, Kind, Opt, Options, SatResult, Term, TermManager};

use crate::common::{Fixture, TempFile, has_sat_solver, parser_output};

/// Whether Kissat is compiled in and supports terminators, i.e., is our
/// patched, bundled Kissat.
fn kissat_patched() -> bool {
    if !has_sat_solver("kissat") {
        return false;
    }
    let tm = TermManager::new();
    let mut opts = Options::new();
    opts.set(Opt::BvSolver, "bitblast").unwrap();
    opts.set(Opt::SatSolver, "kissat").unwrap();
    let mut bitwuzla = Bitwuzla::new(&tm, &opts).unwrap();
    bitwuzla.configure_terminator(|| false).is_ok()
}

/// A terminator that terminates once `time_limit_ms` milliseconds have
/// passed since its creation.
fn time_limit_terminator(time_limit_ms: u64) -> impl FnMut() -> bool + 'static {
    let start = Instant::now();
    move || start.elapsed() >= Duration::from_millis(time_limit_ms)
}

/// `(distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t))`.
fn mul_assoc(f: &Fixture, x: &Term, s: &Term, t: &Term) -> Term {
    f.mk(
        Kind::Distinct,
        &[
            &f.mk(Kind::BvMul, &[s, &f.mk(Kind::BvMul, &[x, t])]),
            &f.mk(Kind::BvMul, &[&f.mk(Kind::BvMul, &[s, x]), t]),
        ],
    )
}

/// `mul_assoc` over fresh constants of the given size.
fn mul_assoc_consts(f: &Fixture, size: u64) -> Term {
    let sort = f.tm.mk_bv_sort(size);
    let x = f.tm.mk_const(&sort, None);
    let s = f.tm.mk_const(&sort, None);
    let t = f.tm.mk_const(&sort, None);
    mul_assoc(f, &x, &s, &t)
}

#[test]
fn sat_solvers() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_sat_solvers.smt2",
        "(set-logic QF_BV)\n\
         (declare-fun u0 () (_ BitVec 4))\n\
         (declare-fun u1 () (_ BitVec 4))\n\
         (assert (distinct (bvadd (bvshl u0 (bvshl (_ bv1 4) (_ bv0 4))) u0) \
         (bvnot (_ bv0 4))))\n\
         (check-sat)\n",
    );

    let mut options = Options::new();
    for solver in ["cadical", "cms", "kissat"] {
        if has_sat_solver(solver) {
            options.set(Opt::SatSolver, solver).unwrap();
            let output = parser_output(&f.tm, &options, "smt2", |parser| {
                parser.parse_file(input.path()).unwrap();
            });
            assert_eq!(output, "sat\n", "{solver}");
        }
    }
}

#[test]
fn terminate() {
    let f = Fixture::new();
    let bv_sort4 = f.tm.mk_bv_sort(4);
    let x = f.tm.mk_const(&bv_sort4, None);
    let s = f.tm.mk_const(&bv_sort4, None);
    let t = f.tm.mk_const(&bv_sort4, None);
    let a = f.mk(
        Kind::And,
        &[
            &f.mk(
                Kind::Equal,
                &[
                    &f.mk(Kind::BvAdd, &[&x, &x]),
                    &f.tm.mk_bv_value_u64(&bv_sort4, 3),
                ],
            ),
            &f.mk(Kind::Not, &[&f.mk(Kind::BvUaddOverflow, &[&x, &x])]),
        ],
    );
    let b = mul_assoc(&f, &x, &s, &t);
    let smt2 = "(declare-const x (_ BitVec 4))\
                (declare-const s (_ BitVec 4))\
                (declare-const t (_ BitVec 4))\
                (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))\
                (check-sat)\n";

    // solved by rewriting
    {
        let mut opts = Options::new();
        opts.set(Opt::BvSolver, "bitblast").unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla.assert_formula(&a);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    }
    {
        let mut opts = Options::new();
        opts.set(Opt::BvSolver, "prop").unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla.assert_formula(&a);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    }
    // not solved by rewriting, should be terminated in the PP when configured
    {
        let mut opts = Options::new();
        opts.set(Opt::BvSolver, "bitblast").unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla.assert_formula(&b);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    }
    if has_sat_solver("cadical") {
        {
            let mut opts = Options::new();
            opts.set(Opt::RewriteLevel, 0).unwrap();
            opts.set(Opt::BvSolver, "bitblast").unwrap();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            bitwuzla.configure_terminator(|| true).unwrap();
            bitwuzla.assert_formula(&b);
            assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
        }
        {
            let mut opts = Options::new();
            opts.set(Opt::RewriteLevel, 0).unwrap();
            opts.set(Opt::BvSolver, "prop").unwrap();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            bitwuzla.configure_terminator(|| true).unwrap();
            bitwuzla.assert_formula(&b);
            assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
        }
        {
            // Configure terminator via parser.
            let mut opts = Options::new();
            opts.set(Opt::RewriteLevel, 0).unwrap();
            opts.set(Opt::BvSolver, "prop").unwrap();
            let output = parser_output(&f.tm, &opts, "smt2", |parser| {
                parser.configure_terminator(|| true).unwrap();
                parser.parse_str(smt2).unwrap();
            });
            assert_eq!(output, "");
        }
    }
    // No terminator support in CryptoMiniSat and Gimsatul, so configuring the
    // terminator will already throw even though this would terminate in the
    // PP (as the terminator immediately would terminate the execution on the
    // first call to terminate).
    for solver in ["cms", "gimsatul"] {
        if has_sat_solver(solver) {
            let mut opts = Options::new();
            opts.set(Opt::RewriteLevel, 0).unwrap();
            opts.set(Opt::BvSolver, "bitblast").unwrap();
            opts.set(Opt::SatSolver, solver).unwrap();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            assert_err!(bitwuzla.configure_terminator(|| true));
        }
    }
    // A system-wide Kissat lacks our patch that polls the terminate callback,
    // configuring a terminator is unsupported in that case (see
    // configure_terminator_unsupported).
    if kissat_patched() {
        for bv_solver in ["bitblast", "prop"] {
            let mut opts = Options::new();
            opts.set(Opt::SatSolver, "kissat").unwrap();
            opts.set(Opt::RewriteLevel, 0).unwrap();
            opts.set(Opt::BvSolver, bv_solver).unwrap();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            bitwuzla.configure_terminator(|| true).unwrap();
            bitwuzla.assert_formula(&b);
            assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
        }
        {
            // Configure terminator via parser.
            let mut opts = Options::new();
            opts.set(Opt::SatSolver, "kissat").unwrap();
            opts.set(Opt::RewriteLevel, 0).unwrap();
            opts.set(Opt::BvSolver, "prop").unwrap();
            let output = parser_output(&f.tm, &opts, "smt2", |parser| {
                parser.configure_terminator(|| true).unwrap();
                parser.parse_str(smt2).unwrap();
            });
            assert_eq!(output, "");
        }
    }
}

#[test]
fn terminate_sat() {
    let f = Fixture::new();
    let b = mul_assoc_consts(&f, 32);
    let smt2 = "(declare-const x (_ BitVec 32))\
                (declare-const s (_ BitVec 32))\
                (declare-const t (_ BitVec 32))\
                (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))\n";

    // not solved by bit-blasting without preprocessing, should be terminated
    // in the SAT solver when configured
    let mut solvers = Vec::new();
    if has_sat_solver("cadical") {
        solvers.push(None);
    }
    // Requires our patched Kissat, see terminate.
    if kissat_patched() {
        solvers.push(Some("kissat"));
    }
    for solver in solvers {
        let mk_opts = || {
            let mut opts = Options::new();
            if let Some(solver) = solver {
                opts.set(Opt::SatSolver, solver).unwrap();
            }
            opts.set(Opt::BvSolver, "bitblast").unwrap();
            opts.set(Opt::Preprocess, false).unwrap();
            opts
        };
        {
            let opts = mk_opts();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            bitwuzla
                .configure_terminator(time_limit_terminator(1000))
                .unwrap();
            bitwuzla.assert_formula(&b);
            assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
        }
        {
            // Configure terminator via parser.
            let opts = mk_opts();
            let output = parser_output(&f.tm, &opts, "smt2", |parser| {
                // The parser polls the terminator after each command and
                // stops without printing anything once it fires. Only
                // configure the terminator once everything up to check-sat
                // is parsed, else the time limit may expire before check-sat
                // is reached (e.g., on slow machines).
                parser.parse_str(smt2).unwrap();
                parser
                    .configure_terminator(time_limit_terminator(100))
                    .unwrap();
                parser.parse_str("(check-sat)\n").unwrap();
            });
            assert_eq!(output, "unknown\n");
        }
    }
    // Note: Only CaDiCaL and (patched) Kissat implement terminator support.
    //       Throws an exception with other SAT solvers.
    for solver in ["cms", "gimsatul"] {
        if has_sat_solver(solver) {
            let mut opts = Options::new();
            opts.set(Opt::SatSolver, solver).unwrap();
            opts.set(Opt::BvSolver, "bitblast").unwrap();
            opts.set(Opt::Preprocess, false).unwrap();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            assert_err!(bitwuzla.configure_terminator(time_limit_terminator(1000)));
        }
    }
}

#[test]
fn terminate_timeout_wrap() {
    if !has_sat_solver("cadical") {
        return;
    }
    let f = Fixture::new();
    let b = mul_assoc_consts(&f, 32);
    let mut opts = Options::new();
    opts.set(Opt::TimeLimitPer, 100).unwrap();
    opts.set(Opt::BvSolver, "bitblast").unwrap();
    opts.set(Opt::RewriteLevel, 0).unwrap();
    opts.set(Opt::Preprocess, false).unwrap();
    // not solved by bit-blasting, should be terminated in the SAT solver when
    // configured
    {
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla
            .configure_terminator(|| -> bool { panic!("user-defined terminate triggered") })
            .unwrap();
        bitwuzla.assert_formula(&b);
        let res = panic::catch_unwind(AssertUnwindSafe(|| bitwuzla.check_sat()));
        assert_eq!(
            res.unwrap_err().downcast_ref::<&str>(),
            Some(&"user-defined terminate triggered")
        );

        bitwuzla.clear_terminator();
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
    }
    {
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla.configure_terminator(|| false).unwrap();
        bitwuzla.assert_formula(&b);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
    }
}

#[test]
fn terminate_mbqi_subsolver() {
    if !has_sat_solver("cadical") {
        return;
    }
    // Regression test: the MBQI sub-solver of the quantifiers solver must
    // honor the parent terminator and configured resource limits. Otherwise a
    // hard ground query inside the MBQI sub-solve runs unboundedly past a
    // configured limit (see QuantSolver::mbqi_check).
    let f = Fixture::new();
    let bv_sort32 = f.tm.mk_bv_sort(32);
    let x = f.tm.mk_var(&bv_sort32, None);
    let y = f.tm.mk_var(&bv_sort32, None);
    let z = f.tm.mk_var(&bv_sort32, None);
    // Associativity of bvmul: a tautology whose MBQI counterexample query (the
    // distinct of the two products over three symbolic instantiation
    // constants) is hard for bit-blasting and does not terminate on its own.
    let body = f.mk(
        Kind::Equal,
        &[
            &f.mk(Kind::BvMul, &[&x, &f.mk(Kind::BvMul, &[&y, &z])]),
            &f.mk(Kind::BvMul, &[&f.mk(Kind::BvMul, &[&x, &y]), &z]),
        ],
    );
    let q = f.mk(Kind::Forall, &[&x, &y, &z, &body]);

    // A user-configured terminator must reach the MBQI sub-solver.
    {
        let opts = Options::new();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla
            .configure_terminator(time_limit_terminator(1000))
            .unwrap();
        bitwuzla.assert_formula(&q);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
    }

    // The time-limit-per resource terminator must reach the MBQI sub-solver.
    {
        let mut opts = Options::new();
        opts.set(Opt::TimeLimitPer, 1000).unwrap();
        let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
        bitwuzla.assert_formula(&q);
        assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unknown);
    }
}

#[test]
fn configure_terminator_unsupported() {
    let f = Fixture::new();
    // A system-wide Kissat lacks our patch that polls the terminate callback.
    let mut solvers = vec!["cms", "gimsatul"];
    if !kissat_patched() {
        solvers.push("kissat");
    }
    for solver in solvers {
        if has_sat_solver(solver) {
            let mut opts = Options::new();
            opts.set(Opt::BvSolver, "bitblast").unwrap();
            opts.set(Opt::SatSolver, solver).unwrap();
            let mut bitwuzla = Bitwuzla::new(&f.tm, &opts).unwrap();
            assert_err!(
                bitwuzla.configure_terminator(|| true),
                "terminator not supported in configured SAT solver"
            );
        }
    }
}
