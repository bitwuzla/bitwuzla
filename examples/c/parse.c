/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <assert.h>
#include <bitwuzla/c/bitwuzla.h>
#include <bitwuzla/c/parser.h>
#include <stdlib.h>

int
main()
{
  // First, create a Bitwuzla options instance.
  BitwuzlaOptions* options = bitwuzla_options_new();

  // We will parse example file `smt2/quickstart.smt2`.
  // Create parser instance.
  FILE* infile = fopen("../smt2/quickstart.smt2", "r");
  assert(infile);
  BitwuzlaParser* parser = bitwuzla_parser_new(
      options, "../smt2/quickstart.smt2", infile, "smt2", 2, "<stdout>");

  // Now parse the input file.
  const char* err_msg = bitwuzla_parser_parse(parser, false);
  // We expect no error to occur.
  assert(err_msg == NULL);

  // Now we retrieve the set of asserted formulas and print them.
  size_t size;
  BitwuzlaTerm* assertions =
      bitwuzla_get_assertions(bitwuzla_parser_get_bitwuzla(parser), &size);
  printf("Assertions:\n");
  printf("{\n");
  for (size_t i = 0; i < size; ++i)
  {
    printf("  %s\n", bitwuzla_term_to_string(assertions[i]));
  }
  printf("}\n");

  // Finally, delete Bitwuzla parser and options instance.
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);

  return 0;
}
