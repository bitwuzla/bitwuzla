//! Parsing (test_api.cpp: Parsing).
//!
//! The C API parser writes to an output file rather than a stream: output
//! the C++ tests capture from (or print to) stdout is written to a temporary
//! file and read back. Input files are written to the temporary directory.
//! `parse(input, parse_only, parse_file)` corresponds to `parse_file` or
//! `parse_str` after `configure_parse_only(parse_only)`, and the
//! `std::istream` input of `parse(infile_name, istream, parse_only)` is passed
//! to `parse_str`. Not ported:
//! - Creating a parser with a null output stream (`parser_smt2`,
//!   `parser_btor2`): not representable.
//! - Parsing from a `std::ifstream` that failed to open (`parser_smt2`,
//!   `parser_btor2`): the C API has no stream input.

use std::collections::HashSet;

use bitwuzla::{Kind, Opt, Options, Parser, SatResult, Sort, Term, TermManager};

use crate::common::{Fixture, TempFile, parser_output};

/// `bitwuzla::parser::Parser(tm, options, language)`, which prints to stdout.
fn mk_parser(tm: &TermManager, options: &Options, language: &str) -> Parser {
    Parser::new(tm, options, language, 2, "<stdout>").unwrap()
}

/// The symbols of the declared functions of `parser`.
fn declared_fun_symbols(parser: &mut Parser) -> HashSet<String> {
    parser
        .get_declared_funs()
        .iter()
        .map(|f| f.symbol().unwrap())
        .collect()
}

#[test]
fn parser_smt2() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_parser_smt2.smt2",
        "(set-logic QF_BV)\n(check-sat)\n(exit)\n",
    );
    let options = Options::new();

    assert_err!(Parser::new(&f.tm, &options, "foo", 2, "<stdout>"));

    {
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        assert!(parser.bitwuzla().is_none());
    }
    {
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        assert_err!(
            parser.parse_file("parsex.smt2"),
            "failed to open 'parsex.smt2'"
        );
        assert_err!(
            parser.parse_file(input.path()),
            "parser in unsafe state after parse error"
        );
    }
    {
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        parser.configure_parse_only(true);
        parser.parse_file(input.path()).unwrap();
        assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
        assert_eq!(parser.get_declared_funs(), Vec::<Term>::new());
    }
}

#[test]
fn parser_smt2_string1() {
    let f = Fixture::new();
    let smt2 = "(set-logic QF_BV)\
                (declare-const a Bool)\
                (declare-const b Bool)\
                (assert (distinct a b))\
                (check-sat)\
                (exit)";
    let options = Options::new();
    {
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        parser.configure_parse_only(true);
        assert_err!(parser.parse_file(smt2), "failed to open");
    }
    {
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_parse_only(true);
            parser.parse_str(smt2).unwrap();
            assert_eq!(parser.get_declared_sorts().len(), 0);
            assert_eq!(parser.get_declared_funs().len(), 2);
        });
        assert_eq!(output, "");
    }
    {
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.parse_str(smt2).unwrap();
            assert_eq!(parser.get_declared_sorts().len(), 0);
            assert_eq!(parser.get_declared_funs().len(), 2);
        });
        assert_eq!(output, "sat\n");
    }
    {
        // parse("<string>", smt2)
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.parse_str(smt2).unwrap();
            assert_eq!(parser.get_declared_sorts().len(), 0);
            assert_eq!(parser.get_declared_funs().len(), 2);
        });
        assert_eq!(output, "sat\n");
    }
    {
        let smt2 = "(set-logic Q_BV)(exit)";
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        parser.configure_parse_only(true);
        assert_err!(parser.parse_str(smt2));
    }
    {
        let smt2 = "(set-logic QF_BV)(declare-const a Bol)(exit)";
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        parser.configure_parse_only(true);
        assert_err!(parser.parse_str(smt2));
    }
    {
        let smt2 = "(set-logic QF_BV)(declare-const a (_ BitVec))(exit)";
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        assert_err!(parser.parse_str(smt2));
    }
}

#[test]
fn parser_smt2_string2() {
    let f = Fixture::new();
    let str_decl = "(declare-const a Bool)";
    let str_true = "(assert (= a true))";
    let str_false = "(assert (= a false))";
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "smt2");
    parser.configure_parse_only(true);
    parser.parse_str(str_decl).unwrap();
    parser.parse_str(str_true).unwrap();
    parser.parse_str(str_false).unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
    let a = parser.parse_term("a").unwrap();
    let decl_funs = parser.get_declared_funs();
    assert_eq!(decl_funs, vec![a]);
    assert_eq!(decl_funs[0].symbol().as_deref(), Some("a"));
}

#[test]
fn parser_smt2_string_push_pop() {
    // the assertion levels are kept across parse calls
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "smt2");
    parser.configure_parse_only(true);
    parser
        .parse_str("(set-logic QF_BV)(push 1)(declare-const a Bool)")
        .unwrap();
    parser.parse_str("(pop 1)").unwrap();
    assert_err!(parser.parse_str("(assert a)"), "undefined symbol 'a'");
}

#[test]
fn parser_smt2_string3() {
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "smt2");
    parser.configure_parse_only(true);
    parser.parse_str("(set-logic QF_ABV)").unwrap();
    parser.parse_str("(set-info :status unsat)").unwrap();
    parser.parse_str("(declare-const v0 (_ BitVec 8))").unwrap();
    parser
        .parse_str("(declare-const v1 (_ BitVec 15))")
        .unwrap();
    parser
        .parse_str("(declare-const a0 (Array (_ BitVec 16) (_ BitVec 1) ))")
        .unwrap();
    parser
        .parse_str(
            "(assert (= #b1 (bvnot (ite (= (select (store a0 (concat v0 \
             (_ bv0 8)) (_ bv1 1)) (concat v1 (_ bv1 1))) (select a0 \
             (concat v1 (_ bv1 1)))) #b1 #b0))))",
        )
        .unwrap();
    parser.parse_str("(check-sat)").unwrap();
    assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
    parser.parse_term("v0").unwrap();
    parser.parse_term("v1").unwrap();
    parser.parse_term("a0").unwrap();
    let decl_funs_strs = declared_fun_symbols(&mut parser);
    assert!(decl_funs_strs.contains("v0"));
    assert!(decl_funs_strs.contains("v1"));
    assert!(decl_funs_strs.contains("a0"));
}

#[test]
fn parser_smt2_string_term() {
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "smt2");
    assert_eq!(parser.parse_term("true").unwrap(), f.tm.mk_true());
    assert_eq!(parser.parse_term("false").unwrap(), f.tm.mk_false());
    parser.configure_parse_only(true);
    parser.parse_str("(declare-const a Bool)").unwrap();
    let t_a = parser.parse_term("a").unwrap();
    parser.parse_str("(declare-const b (_ BitVec 16))").unwrap();
    let t_b = parser.parse_term("b").unwrap();
    parser.parse_str("(declare-const c Bool)").unwrap();
    let t_c = parser.parse_term("c").unwrap();
    assert_eq!(
        parser.parse_term("(xor a c)").unwrap(),
        f.mk(Kind::Xor, &[&t_a, &t_c])
    );
    let bv16 = f.tm.mk_bv_sort(16);
    assert_eq!(
        parser.parse_term("(bvadd b #b1011111010001010)").unwrap(),
        f.mk(
            Kind::BvAdd,
            &[
                &t_b,
                &f.tm.mk_bv_value(&bv16, "1011111010001010", 2).unwrap()
            ]
        )
    );
    assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
    assert_eq!(parser.get_declared_funs().len(), 3);
    let decl_funs_strs = declared_fun_symbols(&mut parser);
    assert!(decl_funs_strs.contains("a"));
    assert!(decl_funs_strs.contains("b"));
    assert!(decl_funs_strs.contains("c"));

    // input that does not denote a term
    for s in [
        "5",
        "5.0",
        "(and true 5 true)",
        "and",
        "!",
        "/",
        ":foo",
        ":named a",
    ] {
        let mut p = mk_parser(&f.tm, &options, "smt2");
        assert_err!(p.parse_term(s));
    }
}

#[test]
fn parser_smt2_string_term_error() {
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "smt2");
    parser.configure_parse_only(true);
    parser.parse_str("(declare-const v Bool)").unwrap();
    assert_err!(parser.parse_term("(let ((q v)) (let ((r"));
    assert_err!(
        parser.parse_term("q"),
        "parser in unsafe state after parse error"
    );
    assert_err!(
        parser.parse_sort("Bool"),
        "parser in unsafe state after parse error"
    );
}

#[test]
fn parser_smt2_string_sort() {
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "smt2");

    assert_eq!(parser.parse_sort("Bool").unwrap(), f.tm.mk_bool_sort());
    assert_eq!(
        parser.parse_sort("(_ BitVec 32)").unwrap(),
        f.tm.mk_bv_sort(32)
    );
    assert_eq!(
        parser.parse_sort("RoundingMode").unwrap(),
        f.tm.mk_rm_sort()
    );
    parser.configure_parse_only(true);
    parser.parse_str("(declare-sort m 0)").unwrap();
    let m = parser.parse_sort("m").unwrap();
    parser
        .parse_str("(define-sort FPN () (_ FloatingPoint 11 53))")
        .unwrap();
    assert_eq!(
        parser.parse_sort("(_ FloatingPoint 11 53)").unwrap(),
        parser.parse_sort("FPN").unwrap()
    );
    let decl_sorts = parser.get_declared_sorts();
    assert_eq!(decl_sorts, vec![m]);
    assert_eq!(decl_sorts[0].uninterpreted_symbol().as_deref(), Some("m"));
    assert_eq!(parser.get_declared_funs(), Vec::<Term>::new());
}

#[test]
fn parser_smt2_nested_array_sort() {
    // Array nesting depth, deep enough to exhaust the native stack if sort
    // parsing recurses per nesting level.
    let f = Fixture::new();
    let depth = 100000;
    let str_sort = format!("{}Bool{}", "(Array Bool ".repeat(depth), ")".repeat(depth));

    let mut expected = f.tm.mk_bool_sort();
    for _ in 0..depth {
        expected = f.tm.mk_array_sort(&f.tm.mk_bool_sort(), &expected);
    }

    let options = Options::new();
    {
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        assert!(parser.parse_sort(&str_sort).unwrap() == expected);
    }
    {
        let mut parser = mk_parser(&f.tm, &options, "smt2");
        parser.configure_parse_only(true);
        parser
            .parse_str(&format!("(declare-const x {str_sort})"))
            .unwrap();
        assert!(parser.parse_term("x").unwrap().sort() == expected);
    }
}

#[test]
fn parser_smt2_print_model_sat() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_parser_smt2_print_model_sat.smt2",
        "(declare-fun a () (_ BitVec 1))\n\
         (declare-fun b () (_ BitVec 1))\n\
         (declare-fun c () (_ BitVec 1))\n\
         (declare-fun d () (_ BitVec 1))\n\
         (assert (= b (ite (= (_ bv1 1) (bvand c b d a)) (_ bv0 1) (_ bv1 1))))\n\
         (set-info :status sat)\n\
         (check-sat)\n",
    );

    let mut options = Options::new();
    {
        // error, produce models not enabled
        parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_auto_print_model(true);
            assert_err!(parser.parse_file(input.path()));
        });
    }
    options.set(Opt::ProduceModels, true).unwrap();
    {
        // parse only
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_auto_print_model(true);
            parser.configure_parse_only(true);
            parser.parse_file(input.path()).unwrap();
        });
        assert_eq!(output, "");
    }
    {
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_auto_print_model(true);
            parser.parse_file(input.path()).unwrap();
        });
        assert!(output.starts_with("sat\n("), "{output}");
    }
}

#[test]
fn parser_smt2_print_model_unsat() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_parser_smt2_print_model_unsat.smt2",
        "(set-info :status unsat)\n\
         (set-logic QF_AUFBV)\n\
         (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))\n\
         (declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))\n\
         (declare-fun i () (_ BitVec 32))\n\
         (declare-fun c () Bool)\n\
         (assert (not (= (ite c (select a i) (select b i)) (select (ite c a b) i))))\n\
         (check-sat)\n",
    );

    let mut options = Options::new();
    {
        // error, produce models not enabled
        parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_auto_print_model(true);
            assert_err!(parser.parse_file(input.path()));
        });
    }
    options.set(Opt::ProduceModels, true).unwrap();
    {
        // parse only
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_auto_print_model(true);
            parser.configure_parse_only(true);
            parser.parse_file(input.path()).unwrap();
        });
        assert_eq!(output, "");
    }
    {
        let output = parser_output(&f.tm, &options, "smt2", |parser| {
            parser.configure_auto_print_model(true);
            parser.parse_file(input.path()).unwrap();
        });
        assert_eq!(output, "unsat\n");
    }
}

#[test]
fn parser_btor2() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_parser_btor2.btor2",
        "1 sort bitvec 8\n\
         2 input 1 @inp2\n\
         3 sort bitvec 3\n\
         4 one 3\n\
         5 uext 1 4 5\n\
         6 srl 1 2 5\n\
         7 sort bitvec 1\n\
         8 slice 7 6 7 7\n\
         9 constraint 8\n",
    );

    let options = Options::new();

    {
        let mut parser = mk_parser(&f.tm, &options, "btor2");
        parser.bitwuzla().unwrap();
    }
    {
        let mut parser = mk_parser(&f.tm, &options, "btor2");
        assert_err!(
            parser.parse_file("parsex.btor2"),
            "failed to open 'parsex.btor2'"
        );
    }
    {
        let mut parser = mk_parser(&f.tm, &options, "btor2");
        parser.configure_parse_only(true);
        parser.parse_file(input.path()).unwrap();
        assert_eq!(
            parser.bitwuzla().unwrap().check_sat().unwrap(),
            SatResult::Unsat
        );
        assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
        let decl_funs = parser.get_declared_funs();
        assert_eq!(decl_funs.len(), 1);
        assert_eq!(decl_funs[0].symbol().as_deref(), Some("@inp2"));
    }
}

#[test]
fn parser_btor2_string1() {
    let f = Fixture::new();
    let btor2 = "1 sort bitvec 8\n\
                 2 input 1 @inp2\n\
                 3 sort bitvec 3\n\
                 4 one 3 @one\n\
                 5 uext 1 4 5\n\
                 6 srl 1 2 5 @srl\n\
                 7 sort bitvec 1\n\
                 8 slice 7 6 7 7\n\
                 9 constraint 8\n";

    let options = Options::new();
    {
        let mut parser = mk_parser(&f.tm, &options, "btor2");
        parser.configure_parse_only(true);
        assert_err!(parser.parse_file(btor2), "failed to open");
    }
    {
        let mut parser = mk_parser(&f.tm, &options, "btor2");
        parser.configure_parse_only(true);
        parser.parse_str(btor2).unwrap();
        assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
        let decl_funs = parser.get_declared_funs();
        assert_eq!(decl_funs.len(), 1);
        assert_eq!(decl_funs[0].symbol().as_deref(), Some("@inp2"));
    }
    {
        // parse("<string>", btor2, true)
        let mut parser = mk_parser(&f.tm, &options, "btor2");
        parser.configure_parse_only(true);
        parser.parse_str(btor2).unwrap();
        assert_eq!(
            parser.bitwuzla().unwrap().check_sat().unwrap(),
            SatResult::Unsat
        );
        assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
        let decl_funs = parser.get_declared_funs();
        assert_eq!(decl_funs.len(), 1);
        assert_eq!(decl_funs[0].symbol().as_deref(), Some("@inp2"));
    }
}

#[test]
fn parser_btor2_string2() {
    let f = Fixture::new();
    let decl_sorts = "1 sort bitvec 8\n2 sort array 1 1\n";
    let decl_inputs = "3 input 2 @arr3\n4 input 2 @arr4\n5 input 2 @arr5\n";
    let decl_more_inputs = "6 sort bitvec 1\n7 input 6 @inp7\n8 input 1 @inp8\n";
    let ite9 = "9 ite 2 -7 4 5\n";
    let reads = "10 read 1 4 8\n11 read 1 9 8\n12 neq 6 10 11\n";
    let and13 = "13 and 6 -7 12";
    let root = "14 constraint 13\n";

    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "btor2");
    parser.configure_parse_only(true);
    parser.parse_str(decl_sorts).unwrap();
    parser.parse_str(decl_inputs).unwrap();
    parser.parse_str(decl_more_inputs).unwrap();
    parser.parse_str(ite9).unwrap();
    parser.parse_str(reads).unwrap();
    parser.parse_str(and13).unwrap();
    parser.parse_str(root).unwrap();
    let bitwuzla = parser.bitwuzla().unwrap();
    assert_eq!(bitwuzla.check_sat().unwrap(), SatResult::Unsat);
    assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
    assert_eq!(parser.get_declared_funs().len(), 5);
    let decl_funs_strs = declared_fun_symbols(&mut parser);
    assert!(decl_funs_strs.contains("@arr3"));
    assert!(decl_funs_strs.contains("@arr4"));
    assert!(decl_funs_strs.contains("@arr5"));
    assert!(decl_funs_strs.contains("@inp7"));
    assert!(decl_funs_strs.contains("@inp8"));
}

#[test]
fn parser_btor2_string_term() {
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "btor2");
    let bv1 = f.tm.mk_bv_sort(1);
    parser.configure_parse_only(true);
    parser.parse_str("1 sort bitvec 1").unwrap();
    assert_eq!(
        parser.parse_term("2 constd 1 1").unwrap(),
        f.tm.mk_bv_value_u64(&bv1, 1)
    );
    assert_eq!(
        parser.parse_term("3 constd 1 0").unwrap(),
        f.tm.mk_bv_value_u64(&bv1, 0)
    );
    let t_a = parser.parse_term("4 input 1 a").unwrap();
    parser.parse_str("5 sort bitvec 16").unwrap();
    assert_err!(
        parser.parse_str("5 sort bitvec 16"),
        "invalid sort id '5', already defined"
    );
    let t_b = parser.parse_term("6 input 5 b").unwrap();
    let t_c = parser.parse_term("7 input 1 c").unwrap();
    assert_eq!(
        parser.parse_term("8 xor 1 4 7").unwrap(),
        f.mk(Kind::BvXor, &[&t_a, &t_c])
    );
    parser.parse_term("9 const 5 1011111010001010").unwrap();
    let bv16 = f.tm.mk_bv_sort(16);
    assert_eq!(
        parser.parse_term("10 add 5 6 9").unwrap(),
        f.mk(
            Kind::BvAdd,
            &[
                &t_b,
                &f.tm.mk_bv_value(&bv16, "1011111010001010", 2).unwrap()
            ]
        )
    );
    assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
    assert_eq!(parser.get_declared_funs().len(), 3);
    let decl_funs_strs = declared_fun_symbols(&mut parser);
    assert!(decl_funs_strs.contains("a"));
    assert!(decl_funs_strs.contains("b"));
    assert!(decl_funs_strs.contains("c"));
}

#[test]
fn parser_btor2_string_sort() {
    let f = Fixture::new();
    let options = Options::new();
    let mut parser = mk_parser(&f.tm, &options, "btor2");

    let bv1 = parser.parse_sort("1 sort bitvec 1").unwrap();
    assert_eq!(bv1, f.tm.mk_bv_sort(1));
    assert_eq!(
        parser.parse_sort("2 sort bitvec 32").unwrap(),
        f.tm.mk_bv_sort(32)
    );
    assert_eq!(
        parser.parse_sort("3 sort array 1 1").unwrap(),
        f.tm.mk_array_sort(&bv1, &bv1)
    );
    assert_eq!(parser.get_declared_sorts(), Vec::<Sort>::new());
    assert_eq!(parser.get_declared_funs(), Vec::<Term>::new());
}

#[test]
fn parser_btor2_print_model_sat() {
    let f = Fixture::new();
    let input = TempFile::new(
        "test_api_parser_btor2_print_model_sat.btor2",
        "1 sort bitvec 32\n\
         2 input 1 x\n\
         3 input 1 y\n\
         4 add 1 -2 -3\n\
         5 add 1 2 4\n\
         6 add 1 3 5\n\
         7 const 1 11111111111111111111111111111110\n\
         8 sort bitvec 1\n\
         9 eq 8 6 7\n\
         10 constraint 9\n",
    );

    let mut options = Options::new();
    {
        // error, produce models not enabled
        parser_output(&f.tm, &options, "btor2", |parser| {
            parser.configure_auto_print_model(true);
            assert_err!(parser.parse_file(input.path()));
        });
    }
    options.set(Opt::ProduceModels, true).unwrap();
    {
        // parse only
        let output = parser_output(&f.tm, &options, "btor2", |parser| {
            parser.configure_auto_print_model(true);
            parser.configure_parse_only(true);
            parser.parse_file(input.path()).unwrap();
        });
        assert_eq!(output, "");
    }
    {
        let output = parser_output(&f.tm, &options, "btor2", |parser| {
            parser.configure_auto_print_model(true);
            parser.parse_file(input.path()).unwrap();
        });
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 3, "{output}");
        assert_eq!(lines[0], "sat");
        assert!(
            lines[1].starts_with("2 ") && lines[1].ends_with(" x"),
            "{output}"
        );
        assert!(
            lines[2].starts_with("3 ") && lines[2].ends_with(" y"),
            "{output}"
        );
    }
}
