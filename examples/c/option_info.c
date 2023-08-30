/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
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
  // Set some options to illustrate current vs default value.
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  bitwuzla_set_option(options, BITWUZLA_OPT_VERBOSITY, 2);
  bitwuzla_set_option_mode(options, BITWUZLA_OPT_BV_SOLVER, "prop");

  // Then iterate over all available configuration options and extract info.
  BitwuzlaOptionInfo info;
  for (uint32_t i = 0; i < BITWUZLA_OPT_NUM_OPTS; ++i)
  {
    BitwuzlaOption opt = (BitwuzlaOption) i;
    bitwuzla_get_option_info(options, opt, &info);
    printf("- long name:   %s\n", info.lng);
    printf("  short name:  %s\n", (info.shrt ? info.shrt : "-"));
    printf("  kind:        ");
    if (info.is_numeric)
    {
      printf("numeric\n");
      printf("  values:\n");
      printf("  + current:   %lu\n", info.numeric.cur);
      printf("  + default:   %lu\n", info.numeric.dflt);
      printf("  + min:       %lu\n", info.numeric.min);
      printf("  + max:       %lu\n", info.numeric.max);
    }
    else
    {
      printf("modes\n");
      printf("  values:\n");
      printf("  + current:   %s\n", info.mode.cur);
      printf("  + default:   %s\n", info.mode.dflt);
      printf("  + modes:     {");
      for (size_t i = 0, n = info.mode.num_modes; i < n; ++i)
      {
        printf("%s %s", (i > 0 ? "," : ""), info.mode.modes[i]);
      }
      printf(" }\n");
    }
    printf("  description: %s\n\n", info.description);
  }
}
