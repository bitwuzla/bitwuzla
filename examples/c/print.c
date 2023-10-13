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
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
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
  BitwuzlaTerm rm     = bitwuzla_mk_const(bitwuzla_mk_rm_sort(), "rm");
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
  // Note: Hexadecimal bv output format is ignored if the value is not of size
  //       divisible by 4.
  printf("Print term:\n");
  printf("-----------\n");
  printf("bitwuzla_term_print():                         ");
  bitwuzla_term_print(rm, stdout);
  printf("\n");
  printf("bitwuzla_term_print_fmt()     [dec (ignored)]: ");
  bitwuzla_term_print_fmt(rm, stdout, 10);
  printf("\n");
  printf("bitwuzla_term_to_string():                     %s\n",
         bitwuzla_term_to_string(rm));
  printf("bitwuzla_term_to_string_fmt() [hex (ignored)]: %s\n",
         bitwuzla_term_to_string_fmt(rm, 10));
  printf("\n");
  printf("bitwuzla_term_print()         [bin]: ");
  bitwuzla_term_print(zero, stdout);
  printf("\n");
  printf("bitwuzla_term_print_fmt()     [dec]: ");
  bitwuzla_term_print_fmt(zero, stdout, 10);
  printf("\n");
  printf("bitwuzla_term_print_fmt()     [hex]: ");
  bitwuzla_term_print_fmt(zero, stdout, 16);
  printf("\n");
  printf("bitwuzla_term_to_string()     [bin]: %s\n",
         bitwuzla_term_to_string(zero));
  printf("bitwuzla_term_to_string_fmt() [dec]: %s\n",
         bitwuzla_term_to_string_fmt(zero, 10));
  printf("bitwuzla_term_to_string_fmt() [hex]: %s\n",
         bitwuzla_term_to_string_fmt(zero, 16));
  printf("\n");
  printf("bitwuzla_term_print_fmt()     [bin]:           ");
  bitwuzla_term_print_fmt(fpleq, stdout, 2);
  printf("\n");
  printf("bitwuzla_term_print_fmt()     [dec]:           ");
  bitwuzla_term_print_fmt(fpleq, stdout, 10);
  printf("\n");
  printf("bitwuzla_term_print_fmt()     [hex (ignored)]: ");
  bitwuzla_term_print_fmt(fpleq, stdout, 16);
  printf("\n");
  printf("bitwuzla_term_to_string_fmt() [bin]:           %s\n",
         bitwuzla_term_to_string_fmt(fpleq, 2));
  printf("bitwuzla_term_to_string_fmt() [dec]:           %s\n",
         bitwuzla_term_to_string_fmt(fpleq, 10));
  printf("bitwuzla_term_to_string_fmt() [hex (ignored)]: %s\n",
         bitwuzla_term_to_string_fmt(fpleq, 16));
  printf("\n");

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
    printf("\n");
  }

  bitwuzla_check_sat(bitwuzla);

  // Print values.
  printf("Print value of Boolean predicate:\n");
  printf("---------------------------------\n");
  BitwuzlaTerm fpleq_val    = bitwuzla_get_value(bitwuzla, fpleq);
  bool fpleq_val_bool       = bitwuzla_term_value_get_bool(fpleq_val);
  const char* fpleq_val_str = bitwuzla_term_value_get_str(fpleq_val);
  printf("%s: %*u [bool]\n", bitwuzla_term_to_string(fpleq), 4, fpleq_val_bool);
  printf("%s: %*s [const char*]\n\n",
         bitwuzla_term_to_string(fpleq),
         4,
         fpleq_val_str);

  printf("Print value of bv const:\n");
  printf("------------------------\n");
  BitwuzlaTerm bv_val = bitwuzla_get_value(bitwuzla, bv);
  printf("%s: %*s [const char*] (bin)\n",
         bitwuzla_term_to_string(bv),
         8,
         bitwuzla_term_value_get_str(bv_val));
  printf("%s: %*s [const char*] (dec)\n",
         bitwuzla_term_to_string(bv),
         8,
         bitwuzla_term_value_get_str_fmt(bv_val, 10));
  printf("%s: %*s [const char*] (hex)\n\n",
         bitwuzla_term_to_string(bv),
         8,
         bitwuzla_term_value_get_str_fmt(bv_val, 16));

  printf("Print value of RoundingMode const:\n");
  printf("----------------------------------\n");
  BitwuzlaTerm rm_val = bitwuzla_get_value(bitwuzla, rm);
  BitwuzlaRoundingMode rm_val_rm = bitwuzla_term_value_get_rm(rm_val);
  const char* rm_val_str         = bitwuzla_term_value_get_str(rm_val);
  printf("%s: %s [BitwuzlaRoundingMode]\n",
         bitwuzla_term_to_string(rm),
         bitwuzla_rm_to_string(rm_val_rm));
  printf("%s: %s [const char*]\n\n", bitwuzla_term_to_string(rm), rm_val_str);

  BitwuzlaTerm fp_val = bitwuzla_get_value(bitwuzla, fp);

  printf("Print value of fp const via bitwuzla_term_value_get_str(_fmt):\n");
  printf("--------------------------------------------------------------\n");
  printf("%s: %*s [const char*] (bin) \n",
         bitwuzla_term_to_string(fp),
         16,
         bitwuzla_term_value_get_str(fp_val));
  printf("%s: %*s [const char*] (dec [ignored]) \n",
         bitwuzla_term_to_string(fp),
         16,
         bitwuzla_term_value_get_str_fmt(fp_val, 10));
  printf("%s: %*s [const char*] (hex [ignored]) \n\n",
         bitwuzla_term_to_string(fp),
         16,
         bitwuzla_term_value_get_str_fmt(fp_val, 16));

  printf("Print value of fp const via bitwuzla_term_value_get_fp_ieee():\n");
  printf("--------------------------------------------------------------\n");
  const char* sign;
  const char* exponent;
  const char* significand;
  bitwuzla_term_value_get_fp_ieee(fp_val, &sign, &exponent, &significand, 2);
  printf("%s: (%s %*s %*s) (bin)\n",
         bitwuzla_term_to_string(fp),
         sign,
         5,
         exponent,
         11,
         significand);
  bitwuzla_term_value_get_fp_ieee(fp_val, &sign, &exponent, &significand, 10);
  printf("%s: (%s %*s %*s) (dec)\n",
         bitwuzla_term_to_string(fp),
         sign,
         5,
         exponent,
         11,
         significand);
  bitwuzla_term_value_get_fp_ieee(fp_val, &sign, &exponent, &significand, 16);
  printf("%s: (%s %*s %*s) (hex)\n",
         bitwuzla_term_to_string(fp),
         sign,
         5,
         exponent,
         11,
         significand);
  return 0;
}
