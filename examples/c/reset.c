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
  BitwuzlaResult result;

  // First, create a Bitwuzla options instance.
  BitwuzlaOptions* options = bitwuzla_options_new();
  // (set-option :produce-models false)
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 0);

  // Then, create a Bitwuzla instance.
  Bitwuzla* bitwuzla = bitwuzla_new(options);

  // Create a bit-vector sort of size 3.
  BitwuzlaSort sortbv3 = bitwuzla_mk_bv_sort(3);

  // (declare-const x (_ BitVec 3))
  BitwuzlaTerm x = bitwuzla_mk_const(sortbv3, "x");

  // (assert (= x #b010))
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          BITWUZLA_KIND_EQUAL, x, bitwuzla_mk_bv_value_uint64(sortbv3, 2)));
  // (check-sat)
  result = bitwuzla_check_sat(bitwuzla);
  printf("Expect: sat\n");
  printf("Bitwuzla: %s\n", bitwuzla_result_to_string(result));

  bitwuzla_delete(bitwuzla);

  // (set-option :produce-models true)
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, true);

  // (reset)
  // Note: Bitwuzla does not provide an explicit API function for reset since
  //       this is achieved by simply discarding the current Bitwuzla instance
  //       and creating a new one.
  bitwuzla = bitwuzla_new(options);

  // (declare-const a ( Array (_ BitVec 2) (_ BitVec 3)))
  BitwuzlaSort sortbv2 = bitwuzla_mk_bv_sort(2);
  BitwuzlaTerm a =
      bitwuzla_mk_const(bitwuzla_mk_array_sort(sortbv2, sortbv3), "a");

  // (assert (= x #b011))
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          BITWUZLA_KIND_EQUAL, x, bitwuzla_mk_bv_value_uint64(sortbv3, 3)));
  // (assert (= x (select a #b01)))
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          BITWUZLA_KIND_EQUAL,
          x,
          bitwuzla_mk_term2(BITWUZLA_KIND_ARRAY_SELECT,
                            a,
                            bitwuzla_mk_bv_value_uint64(sortbv2, 1))));
  // (check-sat)
  result = bitwuzla_check_sat(bitwuzla);
  printf("Expect: sat\n");
  printf("Bitwuzla: %s\n", bitwuzla_result_to_string(result));
  // (get-model)
  printf("(\n");
  printf("  (define-fun %s () ", bitwuzla_term_get_symbol(x));
  printf("%s ", bitwuzla_sort_to_string(bitwuzla_term_get_sort(x)));
  printf("%s)\n", bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, x)));
  printf("  (define-fun %s () ", bitwuzla_term_get_symbol(a));
  printf("%s ", bitwuzla_sort_to_string(bitwuzla_term_get_sort(a)));
  printf("%s)\n", bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, a)));
  printf(")\n");

  return 0;
}
