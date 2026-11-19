//! Port of `examples/cpp/option_info.cpp`.

use bitwuzla::{Opt, OptionKind, Options};

fn main() -> bitwuzla::Result<()> {
    // First, create a Bitwuzla options instance.
    let mut options = Options::new();
    // Set some options to illustrate current vs default value.
    options.set(Opt::ProduceModels, true)?;
    options.set(Opt::Verbosity, 2)?;
    options.set(Opt::BvSolver, "prop")?;

    // Then iterate over all available configuration options and extract info.
    for &opt in Opt::ALL {
        let info = options.info(opt);
        println!("- long name:   {}", info.lng);
        println!("  short name:  {}", info.shrt.as_deref().unwrap_or("-"));
        print!("  kind:        ");
        match &info.kind {
            OptionKind::Bool { cur, dflt } => {
                println!("bool");
                println!("  values:");
                println!("  + current:   {cur}");
                println!("  + default:   {dflt}");
            }
            OptionKind::Numeric {
                cur,
                dflt,
                min,
                max,
            } => {
                println!("numeric");
                println!("  values:");
                println!("  + current:   {cur}");
                println!("  + default:   {dflt}");
                println!("  + min:       {min}");
                println!("  + max:       {max}");
            }
            OptionKind::Mode { cur, dflt, modes } => {
                println!("modes");
                println!("  values:");
                println!("  + current:   {cur}");
                println!("  + default:   {dflt}");
                println!("  + modes:     {{ {} }}", modes.join(", "));
            }
            OptionKind::String { cur, dflt } => {
                println!("string");
                println!("  values:");
                println!("  + current:   {cur}");
                println!("  + default:   {dflt}");
            }
        }
        println!("  description: {}", info.description);
        println!();
    }

    Ok(())
}
