#include <bitwuzla/bitwuzla.h>
#include <stdio.h>

int
main()
{
  // First, create a Bitwuzla instance.
  Bitwuzla *bzla = bitwuzla_new();

  // Then, query which solver engine is set.
  const char* engine = bitwuzla_get_option_str(bzla, BITWUZLA_OPT_ENGINE);
  printf("Default engine: %s (enum value: %u)\n",
         engine,
         bitwuzla_get_option(bzla, BITWUZLA_OPT_ENGINE));

  // Now, select the propagation-based local search engine as solver engine.
  bitwuzla_set_option_str(bzla, BITWUZLA_OPT_ENGINE, "prop");
  engine = bitwuzla_get_option_str(bzla, BITWUZLA_OPT_ENGINE);
  printf("Current engine: %s (enum value: %u)\n",
         engine,
         bitwuzla_get_option(bzla, BITWUZLA_OPT_ENGINE));

  // Then, configure some options that expect an integer configuration value.
  // First, enable model generation.
  bitwuzla_set_option(bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  // Then, increase the verbosity level.
  bitwuzla_set_option(bzla, BITWUZLA_OPT_VERBOSITY, 2);

  // Check sat (nothing to solve, input formula is empty).
  bitwuzla_check_sat(bzla);

  // Finally, delete the Bitwuzla instance.
  bitwuzla_delete(bzla);
}
