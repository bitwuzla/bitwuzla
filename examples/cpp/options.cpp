/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
  std::cout << "Previous verbosity level: " << options.get(Option::VERBOSITY)
            << std::endl;
  options.set(Option::VERBOSITY, 2);
  std::cout << "Current verbosity level: " << options.get(Option::VERBOSITY)
            << std::endl;

  // Now, create a Bitwuzla instance.
  Bitwuzla bitwuzla(options);
  // Check sat (nothing to solve, input formula is empty).
  Result result = bitwuzla.check_sat();
  std::cout << "Expect: sat" << std::endl;
  std::cout << "Bitwuzla: " << result << std::endl;

  return 0;
}
