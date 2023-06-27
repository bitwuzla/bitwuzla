/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/c/bitwuzla.h>
#include <stdio.h>

int
main()
{
  // First, create a Bitwuzla options instance.
  BitwuzlaOptions* options = bitwuzla_options_new();

  // Then, query which bit-vector solver engine is set.
  printf("Default bv solver: %s\n",
         bitwuzla_get_option_mode(options, BITWUZLA_OPT_BV_SOLVER));

  // Now, select the propagation-based local search engine as solver engine.
  bitwuzla_set_option_mode(options, BITWUZLA_OPT_BV_SOLVER, "prop");
  printf("Current engine: %s\n",
         bitwuzla_get_option_mode(options, BITWUZLA_OPT_BV_SOLVER));

  // Then, configure some options that expect an integer configuration value.
  // First, enable model generation.
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  // Then, increase the verbosity level.
  bitwuzla_set_option(options, BITWUZLA_OPT_VERBOSITY, 2);

  // Now, create a Bitwuzla instance.
  Bitwuzla* bitwuzla = bitwuzla_new(options);
  // Check sat (nothing to solve, input formula is empty).
  bitwuzla_check_sat(bitwuzla);

  // Finally, delete the Bitwuzla and Bitwuzla options instance.
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);

  return 0;
}
