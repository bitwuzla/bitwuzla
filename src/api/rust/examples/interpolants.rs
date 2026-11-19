//! Port of `examples/cpp/interpolants.cpp`.

use bitwuzla::{Bitwuzla, Kind, Opt, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    let tm = TermManager::new();

    let bv2 = tm.mk_bv_sort(2);
    let bv4 = tm.mk_bv_sort(4);
    let x1 = tm.mk_const(&bv2, "x1");
    let x2 = tm.mk_const(&bv2, "x2");
    let x3 = tm.mk_const(&bv2, "x3");
    let a1 = tm.mk_term(
        Kind::BvSlt,
        &[
            &tm.mk_bv_zero(&bv4),
            &tm.mk_term(
                Kind::BvSub,
                &[
                    &tm.mk_term(Kind::BvZeroExtend, &[&x1], &[2]),
                    &tm.mk_bv_one(&bv4),
                ],
                &[],
            ),
        ],
        &[],
    );
    let a2 = tm.mk_term(Kind::Equal, &[&x1, &x2], &[]);
    let a3 = tm.mk_term(
        Kind::Equal,
        &[
            &x3,
            &tm.mk_term(
                Kind::BvExtract,
                &[&tm.mk_term(
                    Kind::BvNeg,
                    &[&tm.mk_term(Kind::BvZeroExtend, &[&x2], &[2])],
                    &[],
                )],
                &[1, 0],
            ),
        ],
        &[],
    );
    let a4 = tm.mk_term(Kind::Equal, &[&x3, &tm.mk_bv_zero(&bv2)], &[]);

    let mut options = Options::new();
    options.set(Opt::ProduceInterpolants, true)?;
    options.set(Opt::InterpolantsSimp, true)?;

    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;
    bitwuzla.assert_formula(&a1);
    bitwuzla.assert_formula(&a2);
    bitwuzla.assert_formula(&a3);
    bitwuzla.assert_formula(&a4);
    bitwuzla.check_sat()?;

    // Query an interpolant for A /\ B with A = {a1, a2}.
    let interpolant = bitwuzla.get_interpolant(&[&a1, &a2])?;
    // (not (= x2 #b00))
    println!("{interpolant}");

    // Query an interpolation sequence for a sequence of A/B-partitions
    //     {
    //       ({a1},        {a2, a3, a4}),
    //       ({a1, a2},    {a3, a4}),
    //       ({a1, a2, a3, {a4})
    //     }
    // given as a list {{a1}, {a2}, {a3}} of increments of A.
    let interpolants = bitwuzla.get_interpolants(&[[&a1], [&a2], [&a3]])?;
    // [0]: (= ((_ extract 3 3) (bvadd (concat #b00 x1) #b1111)) #b0)
    // [1]: (not (= x2 #b00))
    // [2]: (not (= x3 #b00))
    println!("(");
    for itp in &interpolants {
        println!("{itp}");
    }
    println!(")");

    Ok(())
}
