//! Port of `examples/cpp/parse.cpp`.

use std::io::Write;

use bitwuzla::{Kind, Options, Parser, TermManager};

/// The input of `examples/smt2/quickstart.smt2` in the Bitwuzla source tree,
/// written to a temporary file so that the example is self-contained.
const QUICKSTART_SMT2: &str = "\
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-fun f ((_ BitVec 8) (_ BitVec 4)) (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert
    (distinct
        ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
        ((_ extract 3 0) (bvashr y (_ bv1 8)))))
(assert (= (f x ((_ extract 6 3) x)) y))
(assert (= (select a x) y))
(check-sat)
(get-model)
(get-value (x y f a (bvmul x x)))
(exit)
";

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();

    // Default diagnostic output stream is stderr.
    options.set_diagnostic_output_stream("<stderr>")?;

    // We will parse example file `smt2/quickstart.smt2`.
    let path =
        std::env::temp_dir().join(format!("bitwuzla-quickstart-{}.smt2", std::process::id()));
    std::fs::write(&path, QUICKSTART_SMT2).expect("failed to write the input file");
    // Create parser instance.
    let mut parser = Parser::new(&tm, &options, "smt2", 2, "<stdout>")?;

    let res = (|| -> bitwuzla::Result<()> {
        // Now parse the input file.
        println!("Expect: sat");
        print!("Bitwuzla: ");
        // The parser prints the result to stdout from C++, flush the Rust
        // side first to keep the output in order.
        std::io::stdout().flush().expect("failed to flush stdout");
        parser.parse_file(&path)?;

        // Now we retrieve the set of asserted formulas and print them.
        let assertions = parser
            .bitwuzla()
            .expect("set-logic initializes the solver")
            .get_assertions();
        println!("Assertions:");
        println!("{{");
        for a in &assertions {
            println!("  {a}");
        }
        println!("}}");

        // Now we add an assertion via parsing from string.
        parser.parse_str("(assert (distinct (select a x) y))")?;
        // Now the formula is unsat.
        let result = parser
            .bitwuzla()
            .expect("set-logic initializes the solver")
            .check_sat()?;

        println!("Expect: unsat");
        println!("Bitwuzla: {result}");

        // For illustration purposes, we now parse in some declarations and
        // terms and sorts from string.

        // Declare bit-vector sort of size 16.
        let bv16 = parser.parse_sort("(_ BitVec 16)")?;
        // Create bit-vector sort of size 16 and show that it corresponds to
        // its string representation '(_ BitVec16)'.
        assert_eq!(bv16, tm.mk_bv_sort(16));

        // Declare Boolean constants 'c' and 'd'.
        // Note: Declarations are commands (not terms) in the SMT-LIB language.
        //       Commands must be parsed in via Parser::parse_str(),
        //       Parser::parse_term() only supports parsing SMT-LIB terms.
        parser.parse_str("(declare-const c Bool)(declare-const d Bool)")?;
        // Declare bit-vector constant 'b'.
        parser.parse_str("(declare-const b (_ BitVec 16))")?;
        // Retrieve term representing 'b'.
        let b = parser.parse_term("b")?;
        // Retrieve term representing 'c'.
        let c = parser.parse_term("c")?;
        // Retrieve term representing 'd'.
        let d = parser.parse_term("d")?;
        // Create xor over 'c' and 'd' and show that it corresponds to term
        // parsed in from its string representation '(xor c d)'.
        assert_eq!(
            parser.parse_term("(xor c d)")?,
            tm.mk_term(Kind::Xor, &[&c, &d], &[])
        );
        // Create bit-vector addition over 'b' and bit-vector value
        // '1011111010001010' and show that it corresponds to the term parsed
        // in from its string representation '(bvadd b #b1011111010001010)'.
        assert_eq!(
            parser.parse_term("(bvadd b #b1011111010001010)")?,
            tm.mk_term(
                Kind::BvAdd,
                &[&b, &tm.mk_bv_value(&bv16, "1011111010001010", 2)?],
                &[]
            )
        );
        Ok(())
    })();

    let _ = std::fs::remove_file(&path);
    if let Err(e) = res {
        // We expect no error to occur.
        println!("unexpected parser error: {e}");
    }
    Ok(())
}
