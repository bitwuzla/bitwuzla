//! The remaining tests of test_api.cpp after the Termination function
//! section: term managers, `nthreads`, `fpexp`, the `issue*` regressions
//! and `fp_from_rational`.
//!
//! The `mk_fp_value(sort, rm, real)` / `mk_fp_value(sort, rm, num, den)`
//! overloads correspond to `mk_fp_from_real` / `mk_fp_from_rational`. Not
//! ported:
//! - `sat_factory` (External SAT solver factory): the C API has no external
//!   SAT solver factories (`bitwuzla::SatSolverFactory`,
//!   `bitwuzla::SatSolver`).
//! - `sat_cms_query_unknown_literal`, `sat_failed_per_literal` (SAT backend):
//!   they drive the C++-internal SAT solver classes (`bzla::sat::Cadical`,
//!   `bzla::sat::CryptoMiniSat`) directly.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, Parser, RoundingMode, SatResult, Term, TermManager};

use crate::common::{Fixture, TempFile, has_fpexp, has_sat_solver, parser_output};

#[test]
fn term_manager() {
    let tm1 = TermManager::new();
    let tm2 = TermManager::new();

    let t1 = tm1.mk_true();
    let t2 = tm2.mk_true();
    assert_ne!(t1, t2);

    let s11 = tm1.mk_bool_sort();
    let s12 = tm1.mk_bv_sort(8);

    tm1.mk_array_sort(&s11, &s12);
    assert_panics!(tm2.mk_array_sort(&s11, &s12));

    let mut bzla1 = Bitwuzla::new(&tm1, &Options::new()).unwrap();
    bzla1.assert_formula(&t1);
    assert_panics!(bzla1.assert_formula(&t2));

    let mut bzla2 = Bitwuzla::new(&tm2, &Options::new()).unwrap();
    bzla2.assert_formula(&t2);
    assert_panics!(bzla2.assert_formula(&t1));
}

#[test]
fn nthreads() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_nthreads.smt2",
        "(set-info :status unsat)\n\
         (set-logic QF_AUFBV)\n\
         (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))\n\
         (declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))\n\
         (declare-fun i () (_ BitVec 32))\n\
         (declare-fun c () Bool)\n\
         (assert (not (= (ite c (select a i) (select b i)) (select (ite c a b) i))))\n\
         (check-sat)\n",
    );

    let mut configs = Vec::new();
    if has_sat_solver("cadical") {
        configs.push(("cadical", 1));
        configs.push(("cadical", 5));
    }
    if has_sat_solver("cms") {
        configs.push(("cms", 5));
    }
    for (solver, nthreads) in configs {
        let mut opts = Options::new();
        opts.set(Opt::SatSolver, solver).unwrap();
        opts.set(Opt::Nthreads, nthreads).unwrap();
        let output = parser_output(&f.tm, &opts, "smt2", |parser| {
            parser.parse_file(input.path()).unwrap();
        });
        assert_eq!(output, "unsat\n", "{solver}, {nthreads} threads");
    }
}

#[test]
fn fpexp() {
    let f = Fixture::new();
    let bv1 = f.tm.mk_bv_value(&f.tm.mk_bv_sort(1), "1", 2).unwrap();
    let bv3 = f.tm.mk_bv_value(&f.tm.mk_bv_sort(3), "100", 2).unwrap();
    let bv23 = f.tm.mk_bv_value(&f.tm.mk_bv_sort(23), "100", 10).unwrap();
    let c1 = f.tm.mk_const(&f.tm.mk_bv_sort(1), None);
    let c3 = f.tm.mk_const(&f.tm.mk_bv_sort(3), None);
    let c23 = f.tm.mk_const(&f.tm.mk_bv_sort(23), None);
    if !has_fpexp() {
        assert_panics!(f.tm.mk_fp_sort(5, 13));
        assert_panics!(f.tm.mk_fp_value(&bv1, &bv3, &bv23));
        assert_panics!(f.tm.mk_term(Kind::FpFp, &[&bv1, &bv3, &bv23], &[]));
        assert_panics!(f.tm.mk_term(Kind::FpFp, &[&c1, &c3, &c23], &[]));
    } else {
        f.tm.mk_fp_sort(5, 13);
        f.tm.mk_fp_value(&bv1, &bv3, &bv23);
        f.mk(Kind::FpFp, &[&bv1, &bv3, &bv23]);
        f.mk(Kind::FpFp, &[&c1, &c3, &c23]);
    }
    f.tm.mk_fp_sort(5, 11);
    f.tm.mk_fp_sort(8, 24);
    f.tm.mk_fp_sort(11, 53);
    f.tm.mk_fp_sort(15, 113);
}

/// Print the value of `t` and of all its descendants.
fn dfs(bitwuzla: &mut Bitwuzla, t: &Term) {
    println!("{t} = {}", bitwuzla.get_value(t));
    for child in t.children() {
        dfs(bitwuzla, &child);
    }
}

#[test]
fn issue184_term_outlives_term_manager() {
    // https://github.com/bitwuzla/bitwuzla/issues/184
    //
    // A bitwuzla::Term outliving its TermManager must still see valid
    // NodeData on destruction. The fix defers NodeManager's actual
    // destruction until the last NodeData (kept alive by surviving Terms)
    // is freed; otherwise ~Term would UAF in NodeData::dec_ref.
    let (t, s) = {
        let tm = TermManager::new();
        let s = tm.mk_rm_sort();
        let t = tm.mk_rm_value(RoundingMode::Rne);
        (t, s)
    };
    assert!(t.is_value());
    assert!(s.is_rm());
}

#[test]
fn issue184_sort_alone_outlives_term_manager() {
    // Sort can outlive its TermManager independently of any Term: Sort holds
    // a TypeData* through Type, and TypeData lives in TypeManager. The
    // TypeData live-data counter on TypeManager defers its destruction in
    // exactly this scenario — without it, this test would UAF in `~Sort` /
    // `s.is_bv()`. Note that TypeManager has its own deferred destruction,
    // independent of NodeManager.
    let s = {
        let tm = TermManager::new();
        tm.mk_bv_sort(8)
    };
    assert!(s.is_bv());
    assert_eq!(s.bv_size(), 8);
}

#[test]
fn issue184_children_outlive_parent_term_manager() {
    // Children obtained via Term::children() / Term::operator[] must also
    // keep the NodeManager alive after the originating TermManager goes
    // out of scope.
    let children = {
        let tm = TermManager::new();
        let bv8 = tm.mk_bv_sort(8);
        let x = tm.mk_const(&bv8, "x");
        let y = tm.mk_const(&bv8, "y");
        let add = tm.mk_term(Kind::BvAdd, &[&x, &y], &[]);
        add.children()
    };
    for c in &children {
        assert!(c.is_const());
    }
}

#[test]
fn issue197() {
    let smt2 = "(set-info :smt-lib-version 2.6)\
                (set-logic QF_BV)\
                (set-info :status sat)\
                (declare-fun bv1 () (_ BitVec 32))\
                (declare-fun bv2 () (_ BitVec 32))\
                (define-fun minus ((x (_ BitVec 32))) (_ BitVec 32) (bvneg x))\
                (assert (= (minus bv1) bv2))";

    let tm = TermManager::new();
    let mut opt = Options::new();
    opt.set(Opt::ProduceModels, true).unwrap();
    let mut parser = Parser::new(&tm, &opt, "smt2", 2, "<stdout>").unwrap();
    parser.configure_parse_only(true);
    parser.parse_str(smt2).unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();
    let assertions = bitwuzla.get_assertions();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Sat);
    for t in &assertions {
        dfs(bitwuzla, t);
    }
}

#[test]
fn fp_from_rational() {
    let f = Fixture::new();
    let (sort, rm) = (&f.fp_sort16, &f.rm_rne);
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, "1", "0"));
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, "1", "0.0"));
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, "1", "-0"));
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, "1", ""));
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, "", "1"));
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, "-", "1"));
    assert_err!(f.tm.mk_fp_from_rational(sort, rm, ".", "1"));
    assert_err!(f.tm.mk_fp_from_real(sort, rm, ""));
    assert_err!(f.tm.mk_fp_from_real(sort, rm, "-"));
    assert_err!(f.tm.mk_fp_from_real(sort, rm, "."));
}
