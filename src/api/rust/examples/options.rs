//! Port of `examples/cpp/options.cpp`.

use bitwuzla::{Bitwuzla, Opt, Options, TermManager};

fn main() -> bitwuzla::Result<()> {
    // First, create a Bitwuzla options instance.
    let mut options = Options::new();

    // Enable model generation, which expects a boolean configuration value.
    options.set(Opt::ProduceModels, true)?;

    // Increase the verbosity level, which expects an integer value.
    println!("Previous verbosity level: {}", options.get(Opt::Verbosity));
    options.set(Opt::Verbosity, 2)?;
    println!("Current verbosity level: {}", options.get(Opt::Verbosity));

    // Now configure an option that has modes (a choice of configuration values).
    // First, query which bit-vector solver engine is set.
    println!("Default bv solver: {}", options.get_mode(Opt::BvSolver));
    // Then, select the propagation-based local search engine as solver engine.
    options.set(Opt::BvSolver, "prop")?;
    println!("Current engine: {}", options.get_mode(Opt::BvSolver));

    // Now, create a Bitwuzla instance with a new term manager.
    let tm = TermManager::new();
    let mut bitwuzla = Bitwuzla::new(&tm, &options)?;
    // Check sat (nothing to solve, input formula is empty).
    let result = bitwuzla.check_sat()?;
    println!("Expect: sat");
    println!("Bitwuzla: {result}");

    Ok(())
}
