#include <bitwuzla/cpp/bitwuzla.h>

#include <iostream>

using namespace bitwuzla;

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;

  // Then, query which bit-vector solver engine is set.
  std::cout << "Default bv solver: " << options.get_mode(Option::BV_SOLVER)
            << std::endl;

  // Now, select the propagation-based local search engine as solver engine.
  options.set(Option::BV_SOLVER, "prop");
  std::cout << "Current engine: " << options.get_mode(Option::BV_SOLVER)
            << std::endl;

  // Then, configure some options that expect an integer configuration value.
  // First, enable model generation.
  options.set(Option::PRODUCE_MODELS, true);
  // Then, increase the verbosity level.
  options.set(Option::VERBOSITY, 2);

  // Now, create a Bitwuzla instance.
  Bitwuzla bitwuzla(options);
  // Check sat (nothing to solve, input formula is empty).
  bitwuzla.check_sat();

  return 0;
}
