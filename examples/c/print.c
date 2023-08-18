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
#include <stdio.h>

int
main()
{
  // First, create a Bitwuzla options instance.
  BitwuzlaOptions* options = bitwuzla_options_new();
  // Then, create a Bitwuzla instance.
  Bitwuzla* bitwuzla = bitwuzla_new(options);
  // Create some sorts.
  BitwuzlaSort bv8           = bitwuzla_mk_bv_sort(8);
  BitwuzlaSort bv32          = bitwuzla_mk_bv_sort(32);
  BitwuzlaSort fp16          = bitwuzla_mk_fp_sort(5, 11);
  BitwuzlaSort fun_domain[3] = {bv8, fp16, bv32};
  BitwuzlaSort fun_sort      = bitwuzla_mk_fun_sort(3, fun_domain, fp16);
  // Create terms.
  BitwuzlaTerm b      = bitwuzla_mk_const(bitwuzla_mk_bool_sort(), "b");
  BitwuzlaTerm bv     = bitwuzla_mk_const(bv8, "bv");
  BitwuzlaTerm fp     = bitwuzla_mk_const(fp16, "fp");
  BitwuzlaTerm fun    = bitwuzla_mk_const(fun_sort, "fun");
  BitwuzlaTerm zero   = bitwuzla_mk_bv_zero(bv8);
  BitwuzlaTerm ones   = bitwuzla_mk_bv_ones(bitwuzla_mk_bv_sort(23));
  BitwuzlaTerm z      = bitwuzla_mk_var(bv8, "z");
  BitwuzlaTerm q      = bitwuzla_mk_var(bv8, "q");
  BitwuzlaTerm lambda = bitwuzla_mk_term2(
      BITWUZLA_KIND_LAMBDA, z, bitwuzla_mk_term2(BITWUZLA_KIND_BV_ADD, z, bv));
  BitwuzlaTerm args[4] = {
      fun,
      bv,
      fp,
      bitwuzla_mk_term1_indexed1(BITWUZLA_KIND_BV_ZERO_EXTEND, ones, 9)};
  BitwuzlaTerm fpleq = bitwuzla_mk_term2(
      BITWUZLA_KIND_FP_LEQ, bitwuzla_mk_term(BITWUZLA_KIND_APPLY, 4, args), fp);
  BitwuzlaTerm exists = bitwuzla_mk_term2(
      BITWUZLA_KIND_EXISTS,
      q,
      bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL,
                        zero,
                        bitwuzla_mk_term2(BITWUZLA_KIND_BV_MUL, bv, q)));
  // Assert formulas.
  bitwuzla_assert(bitwuzla, b);
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL,
                        bitwuzla_mk_term2(BITWUZLA_KIND_APPLY, lambda, bv),
                        zero));
  bitwuzla_assert(bitwuzla, exists);
  bitwuzla_assert(bitwuzla, fpleq);

  // Print sort.
  printf("Print bit-vector sort of size 32:\n");
  printf("---------------------------------\n");
  printf("bitwuzla_sort_print():     ");
  bitwuzla_sort_print(bv32, stdout);
  printf("\n");
  printf("bitwuzla_sort_to_string(): %s\n\n", bitwuzla_sort_to_string(bv32));

  // Print terms.
  // Note: bitwuzla_term_to_string() uses the binary bv output format (not
  //       configurable).
  printf("Print term [binary bv output format]:\n");
  printf("-------------------------------------\n");
  printf("bitwuzla_term_print():     ");
  bitwuzla_term_print(fpleq, stdout, 2);
  printf("\n");
  printf("bitwuzla_term_to_string(): %s\n\n", bitwuzla_term_to_string(fpleq));

  printf("Print term [hexadecimal bv output format]:\n");
  printf("------------------------------------------\n");
  printf("bitwuzla_term_print():     ");
  bitwuzla_term_print(fpleq, stdout, 16);
  printf("\n");
  printf("bitwuzla_term_to_string(): %s\n\n", bitwuzla_term_to_string(fpleq));

  printf("Print term [decimal bv output format]:\n");
  printf("--------------------------------------\n");
  printf("bitwuzla_term_print():     ");
  bitwuzla_term_print(fpleq, stdout, 10);
  printf("\n");
  printf("bitwuzla_term_to_string(): %s\n\n", bitwuzla_term_to_string(fpleq));

  // Print asserted formulas using binary bit-vector output format.
  {
    printf("Print formula [binary bv output format]:\n");
    printf("----------------------------------------\n");
    bitwuzla_print_formula(bitwuzla, "smt2", stdout, 2);
    printf("\n");
  }

  // Print asserted formulas using hexadecimal bit-vector output format.
  {
    printf("Print formula [hexadecimal bv output format]:\n");
    printf("----------------------------------------\n");
    bitwuzla_print_formula(bitwuzla, "smt2", stdout, 16);
    printf("\n");
  }

  // Print asserted formulas using decimal bit-vector output format.
  {
    printf("Print formula [decimal bv output format]:\n");
    printf("----------------------------------------\n");
    bitwuzla_print_formula(bitwuzla, "smt2", stdout, 10);
  }
  return 0;
}
