//! Port of `examples/cpp/quickstart.cpp`.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();
    // Then, enable model generation.
    options.set(Opt::ProduceModels, true)?;
    // Now, for illustration purposes, we enable CaDiCaL as SAT solver
    // (CaDiCaL is already configured by default).
    // Note: This will silently fall back to one of the compiled in SAT solvers
    //       if the selected solver is not compiled in.
    options.set(Opt::SatSolver, "cadical")?;
    // Then, create a Bitwuzla instance.
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;

    // Create bit-vector sorts of size 4 and 8.
    let sortbv4 = tm.mk_bv_sort(4);
    let sortbv8 = tm.mk_bv_sort(8);
    // Create function sort.
    let sortfun = tm.mk_fun_sort(&[&sortbv8, &sortbv4], &sortbv8);
    // Create array sort.
    let sortarr = tm.mk_array_sort(&sortbv8, &sortbv8);

    // Create two bit-vector constants of that sort.
    let x = tm.mk_const(&sortbv8, "x");
    let y = tm.mk_const(&sortbv8, "y");
    // Create fun const.
    let f = tm.mk_const(&sortfun, "f");
    // Create array const.
    let a = tm.mk_const(&sortarr, "a");
    // Create bit-vector values one and two of the same sort.
    let one = tm.mk_bv_one(&sortbv8);
    // Alternatively, you can create bit-vector value one with:
    // let one = tm.mk_bv_value(&sortbv8, "1", 2)?;
    // let one = tm.mk_bv_value_u64(&sortbv8, 1);
    let two = tm.mk_bv_value_u64(&sortbv8, 2);

    // (bvsdiv x (_ bv2 8))
    let sdiv = tm.mk_term(Kind::BvSdiv, &[&x, &two], &[]);
    // (bvashr y (_ bv1 8))
    let ashr = tm.mk_term(Kind::BvAshr, &[&y, &one], &[]);
    // ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    let sdive = tm.mk_term(Kind::BvExtract, &[&sdiv], &[3, 0]);
    // ((_ extract 3 0) (bvashr x (_ bv1 8)))
    let ashre = tm.mk_term(Kind::BvExtract, &[&ashr], &[3, 0]);

    // (assert
    //     (distinct
    //         ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    //         ((_ extract 3 0) (bvashr y (_ bv1 8)))))
    bitwuzla.assert_formula(&tm.mk_term(Kind::Distinct, &[&sdive, &ashre], &[]));
    // (assert (= (f x ((_ extract 6 3) x)) y))
    bitwuzla.assert_formula(&tm.mk_term(
        Kind::Equal,
        &[
            &tm.mk_term(
                Kind::Apply,
                &[&f, &x, &tm.mk_term(Kind::BvExtract, &[&x], &[6, 3])],
                &[],
            ),
            &y,
        ],
        &[],
    ));
    // (assert (= (select a x) y))
    bitwuzla.assert_formula(&tm.mk_term(
        Kind::Equal,
        &[&tm.mk_term(Kind::ArraySelect, &[&a, &x], &[]), &y],
        &[],
    ));

    // (check-sat)
    let result = bitwuzla.check_sat()?;

    println!("Expect: sat");
    println!("Bitwuzla: {result}");

    // Print model in SMT-LIBv2 format.
    println!("Model:");
    println!("(");
    for term in [&x, &y, &f, &a] {
        let sort = term.sort();
        let symbol = term.symbol().unwrap_or_else(|| format!("@t{}", term.id()));
        print!("  (define-fun {symbol} (");
        if sort.is_fun() {
            let mut value = bitwuzla.get_value(term);
            assert_eq!(value.kind(), Kind::Lambda);
            assert_eq!(value.num_children(), 2);
            let mut children = value.children();
            while children[1].kind() == Kind::Lambda {
                assert!(children[0].is_variable());
                print!("({} {}) ", children[0], children[0].sort());
                value = children[1].clone();
                children = value.children();
            }
            assert!(children[0].is_variable());
            print!(
                "({} {})) {} ",
                children[0],
                children[0].sort(),
                sort.fun_codomain()
            );
            println!("{})", children[1]);
        } else {
            println!(") {} {})", sort, bitwuzla.get_value(term));
        }
    }
    println!(")");
    println!();

    // Print value for x, y, f and a.
    // Both x and y are bit-vector terms and their value is a bit-vector
    // value that can be printed via Term::value_str().
    println!("value of x: {}", bitwuzla.get_value(&x).value_str(2));
    println!("value of y: {}", bitwuzla.get_value(&y).value_str(2));
    println!();
    // f and a, on the other hand, are a function and array term, respectively.
    // The value of these terms is not a value term: for f, it is a lambda term,
    // and the value of a is represented as a store term. Thus we cannot use
    // Term::value_str(), but we can print the value of the terms via
    // Display (to_string()).
    println!("str() representation of value of f:");
    println!("{}", bitwuzla.get_value(&f));
    println!();
    println!("str() representation of value of a:");
    println!("{}", bitwuzla.get_value(&a));
    println!();
    println!();
    // Note that the assignment string of bit-vector terms is given as the
    // pure assignment string, either in binary, hexadecimal or decimal format,
    // whereas Display prints the value in SMT-LIB2 format (in binary, use
    // Term::to_string_fmt() for other bit-vector output formats).
    println!(
        "str() representation of value of x: {}",
        bitwuzla.get_value(&x)
    );
    println!(
        "str() representation of value of y: {}",
        bitwuzla.get_value(&y)
    );
    println!();

    // Query value of bit-vector term that does not occur in the input formula
    let v = bitwuzla.get_value(&tm.mk_term(Kind::BvMul, &[&x, &x], &[]));
    println!("value of v = x * x: {}", v.value_str(2));

    Ok(())
}
