//! Port of `examples/cpp/terminator.cpp`.

use std::time::{Duration, Instant};

use bitwuzla::{Bitwuzla, Kind, Opt, Options, TermManager, Terminator};

/// Terminates solving after a time limit.
struct TestTerminator {
    time_limit: Duration,
    start: Instant,
}

impl TestTerminator {
    fn new(time_limit_ms: u64) -> Self {
        Self {
            time_limit: Duration::from_millis(time_limit_ms),
            start: Instant::now(),
        }
    }
}

impl Terminator for TestTerminator {
    fn terminate(&mut self) -> bool {
        self.start.elapsed() >= self.time_limit
    }
}

fn main() -> bitwuzla::Result<()> {
    // First, create a term manager instance.
    let tm = TermManager::new();
    // Create a Bitwuzla options instance.
    let mut options = Options::new();
    // Then, create a Bitwuzla instance.
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;

    let bv = tm.mk_bv_sort(32);

    let x = tm.mk_const(&bv, None);
    let s = tm.mk_const(&bv, None);
    let t = tm.mk_const(&bv, None);

    let a = tm.mk_term(
        Kind::Distinct,
        &[
            &tm.mk_term(
                Kind::BvMul,
                &[&s, &tm.mk_term(Kind::BvMul, &[&x, &t], &[])],
                &[],
            ),
            &tm.mk_term(
                Kind::BvMul,
                &[&tm.mk_term(Kind::BvMul, &[&s, &x], &[]), &t],
                &[],
            ),
        ],
        &[],
    );

    // Now, we check that the following formula is unsat.
    // (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))
    println!("> Without terminator (with preprocessing):");
    println!("Expect: unsat");
    println!("Result: {}", bitwuzla.check_sat_assuming(&[&a])?);

    // Now, for illustration purposes, we disable preprocessing, which will
    // significantly increase solving time, and connect a terminator instance
    // that terminates after a certain time limit.
    options.set(Opt::Preprocess, false)?;
    // Create new Bitwuzla instance with reconfigured options.
    let mut bitwuzla2 = Bitwuzla::new(&tm, &options)?;
    // Configure and connect terminator.
    // Note: Any closure `FnMut() -> bool` is a terminator, e.g.,
    //       `move || start.elapsed() >= time_limit`.
    bitwuzla2.configure_terminator(TestTerminator::new(1000))?;

    // Now, we expect Bitwuzla to be terminated during the check-sat call.
    println!("> With terminator (no preprocessing):");
    println!("Expect: unknown");
    println!("Result: {}", bitwuzla2.check_sat_assuming(&[&a])?);

    Ok(())
}
