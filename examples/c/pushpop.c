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
  // Then, create a Bitwuzla instance.
  Bitwuzla* bitwuzla = bitwuzla_new(options);

  // Create a bit-vector sort of size 1.
  BitwuzlaSort sortbv1 = bitwuzla_mk_bv_sort(1);
  // Create a bit-vector sort of size 2.
  BitwuzlaSort sortbv2 = bitwuzla_mk_bv_sort(2);

  // Create bit-vector variables.
  // (declare-const o0 (_ BitVec 1))
  BitwuzlaTerm o0 = bitwuzla_mk_const(sortbv1, "o0");
  // (declare-const o1 (_ BitVec 1))
  BitwuzlaTerm o1 = bitwuzla_mk_const(sortbv1, "o1");
  // (declare-const s0 (_ BitVec 2))
  BitwuzlaTerm s0 = bitwuzla_mk_const(sortbv2, "s0");
  // (declare-const s1 (_ BitVec 2))
  BitwuzlaTerm s1 = bitwuzla_mk_const(sortbv2, "s1");
  // (declare-const s2 (_ BitVec 2))
  BitwuzlaTerm s2 = bitwuzla_mk_const(sortbv2, "s2");
  // (declare-const goal (_ BitVec 2))
  BitwuzlaTerm goal = bitwuzla_mk_const(sortbv2, "goal");

  // Create bit-vector values zero, one, three.
  BitwuzlaTerm zero  = bitwuzla_mk_bv_zero(sortbv2);
  BitwuzlaTerm one1  = bitwuzla_mk_bv_one(sortbv1);
  BitwuzlaTerm one2  = bitwuzla_mk_bv_one(sortbv2);
  BitwuzlaTerm three = bitwuzla_mk_bv_value_uint64(sortbv2, 3);

  // Add some assertions.
  bitwuzla_assert(bitwuzla, bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, s0, zero));
  bitwuzla_assert(bitwuzla,
                  bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, goal, three));

  // Push, assert, check sat and pop.
  bitwuzla_push(bitwuzla, 1);
  bitwuzla_assert(bitwuzla, bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, s0, goal));
  BitwuzlaResult result = bitwuzla_check_sat(bitwuzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n", bitwuzla_result_to_string(result));
  bitwuzla_pop(bitwuzla, 1);

  // (assert (= s1 (ite (= o0 (_ sortbv1 1)) (bvadd s0 one) s0)))
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          BITWUZLA_KIND_EQUAL,
          s1,
          bitwuzla_mk_term3(BITWUZLA_KIND_ITE,
                            bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, o0, one1),
                            bitwuzla_mk_term2(BITWUZLA_KIND_BV_ADD, s0, one2),
                            s0)));

  // Push, assert, check sat and pop.
  bitwuzla_push(bitwuzla, 1);
  bitwuzla_assert(bitwuzla, bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, s1, goal));
  result = bitwuzla_check_sat(bitwuzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n", bitwuzla_result_to_string(result));
  bitwuzla_pop(bitwuzla, 1);

  // (assert (= s2 (ite (= o1 (_ sortbv1 1)) (bvadd s1 one) s1)))
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          BITWUZLA_KIND_EQUAL,
          s2,
          bitwuzla_mk_term3(BITWUZLA_KIND_ITE,
                            bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, o1, one1),
                            bitwuzla_mk_term2(BITWUZLA_KIND_BV_ADD, s1, one2),
                            s1)));

  // Push, assert, check sat and pop.
  bitwuzla_push(bitwuzla, 1);
  bitwuzla_assert(bitwuzla, bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL, s2, goal));
  result = bitwuzla_check_sat(bitwuzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n", bitwuzla_result_to_string(result));
  bitwuzla_pop(bitwuzla, 1);

  // Finally, delete the Bitwuzla and Bitwuzla options instance.
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);

  return 0;
}
