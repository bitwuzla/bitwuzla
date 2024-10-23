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
  // First, create a term manager instance.
  BitwuzlaTermManager* tm = bitwuzla_term_manager_new();
  // Create a Bitwuzla options instance.
  BitwuzlaOptions* options = bitwuzla_options_new();

  // We will parse example file `smt2/quickstart.smt2`.
  // Create parser instance.
  const char* infile_name = "../smt2/quickstart.smt2";
  BitwuzlaParser* parser =
      bitwuzla_parser_new(tm, options, "smt2", 2, "<stdout>");

  // Now parse the input file.
  const char* error_msg;
  printf("Expect: sat\n");
  printf("Bitwuzla: ");
  bitwuzla_parser_parse(parser, infile_name, false, true, &error_msg);
  // We expect no error to occur.
  assert(!error_msg);

  // Now we retrieve the set of asserted formulas and print them.
  size_t size;
  const BitwuzlaTerm* assertions =
      bitwuzla_get_assertions(bitwuzla_parser_get_bitwuzla(parser), &size);
  printf("Assertions:\n");
  printf("{\n");
  for (size_t i = 0; i < size; ++i)
  {
    printf("  %s\n", bitwuzla_term_to_string(assertions[i]));
  }
  printf("}\n");

  // Now we add an assertion via parsing from string.
  bitwuzla_parser_parse(
      parser, "(assert (distinct (select a x) y))", true, false, &error_msg);
  // We expect no error to occur.
  assert(!error_msg);
  // Now the formula is unsat.
  BitwuzlaResult result =
      bitwuzla_check_sat(bitwuzla_parser_get_bitwuzla(parser));

  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n\n", bitwuzla_result_to_string(result));

  // For illustration purposes, we now parse in some declarations and terms 
  // and sorts from string.

  // Declare bit-vector sort of size 16.
  BitwuzlaSort bv16 =
      bitwuzla_parser_parse_sort(parser, "(_ BitVec 16)", &error_msg);
  // We expect no error to occur.
  assert(!error_msg);
  // Create bit-vector sort of size 16 and show that it corresponds to
  // its string representation '(_ BitVec16)'.
  assert(bv16 == bitwuzla_mk_bv_sort(tm, 16));

  // Declare Boolean constants 'c' and 'd'.
  // Note: Declarations are commands (not terms) in the SMT-LIB language.
  //       Commands must be parsed in via bitwuzla_parser_parse(),
  //       bitwuzla_parser_parse_term() only supports parsing SMT-LIB terms.
  bitwuzla_parser_parse(parser,
                        "(declare-const c Bool)(declare-const d Bool)",
                        true,
                        false,
                        &error_msg);
  // Declare bit-vector constant 'b'.
  bitwuzla_parser_parse(
      parser, "(declare-const b (_ BitVec 16))", true, false, &error_msg);
  // We expect no error to occur.
  assert(!error_msg);
  // Retrieve term representing 'b'.
  BitwuzlaTerm b = bitwuzla_parser_parse_term(parser, "b", &error_msg);
  // We expect no error to occur.
  assert(!error_msg);
  // Retrieve term representing 'c'.
  BitwuzlaTerm c = bitwuzla_parser_parse_term(parser, "c", &error_msg);
  // We expect no error to occur.
  assert(!error_msg);
  // Retrieve term representing 'd'.
  BitwuzlaTerm d = bitwuzla_parser_parse_term(parser, "d", &error_msg);
  // We expect no error to occur.
  assert(!error_msg);
  // Create xor over 'a' and 'c' and show that it corresponds to term
  // parsed in from its string representation '(xor c d)'.
  assert(bitwuzla_parser_parse_term(parser, "(xor c d)", &error_msg)
         == bitwuzla_mk_term2(tm, BITWUZLA_KIND_XOR, c, d));
  // Create bit-vector addition over 'b' and bit-vector value
  // '1011111010001010' and show that it corresponds to the term parsed in
  // from its string representation '(bvadd b #b1011111010001010)'.
  assert(bitwuzla_parser_parse_term(
             parser, "(bvadd b #b1011111010001010)", &error_msg)
         == bitwuzla_mk_term2(
             tm,
             BITWUZLA_KIND_BV_ADD,
             b,
             bitwuzla_mk_bv_value(tm, bv16, "1011111010001010", 2)));
  // Finally, delete Bitwuzla parser, options, and term manager instance.
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
  bitwuzla_term_manager_delete(tm);

  return 0;
}
