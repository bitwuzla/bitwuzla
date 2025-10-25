/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
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
  BitwuzlaTermManager* tm = bitwuzla_term_manager_new();

  BitwuzlaSort bv2 = bitwuzla_mk_bv_sort(tm, 2);
  BitwuzlaSort bv4 = bitwuzla_mk_bv_sort(tm, 4);
  BitwuzlaTerm x1  = bitwuzla_mk_const(tm, bv2, "x1");
  BitwuzlaTerm x2  = bitwuzla_mk_const(tm, bv2, "x2");
  BitwuzlaTerm x3  = bitwuzla_mk_const(tm, bv2, "x3");
  BitwuzlaTerm a1  = bitwuzla_mk_term2(
      tm,
      BITWUZLA_KIND_BV_SLT,
      bitwuzla_mk_bv_zero(tm, bv4),
      bitwuzla_mk_term2(
          tm,
          BITWUZLA_KIND_BV_SUB,
          bitwuzla_mk_term1_indexed1(tm, BITWUZLA_KIND_BV_ZERO_EXTEND, x1, 2),
          bitwuzla_mk_bv_one(tm, bv4)));
  BitwuzlaTerm a2 = bitwuzla_mk_term2(tm, BITWUZLA_KIND_EQUAL, x1, x2);
  BitwuzlaTerm a3 = bitwuzla_mk_term2(
      tm,
      BITWUZLA_KIND_EQUAL,
      x3,
      bitwuzla_mk_term1_indexed2(
          tm,
          BITWUZLA_KIND_BV_EXTRACT,
          bitwuzla_mk_term1(tm,
                            BITWUZLA_KIND_BV_NEG,
                            bitwuzla_mk_term1_indexed1(
                                tm, BITWUZLA_KIND_BV_ZERO_EXTEND, x2, 2)),
          1,
          0));
  BitwuzlaTerm a4 = bitwuzla_mk_term2(
      tm, BITWUZLA_KIND_EQUAL, x3, bitwuzla_mk_bv_zero(tm, bv2));

  BitwuzlaOptions* options = bitwuzla_options_new();
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_INTERPOLANTS, 1);
  bitwuzla_set_option(options, BITWUZLA_OPT_INTERPOLANTS_SIMP, 1);

  Bitwuzla* bitwuzla = bitwuzla_new(tm, options);
  bitwuzla_assert(bitwuzla, a1);
  bitwuzla_assert(bitwuzla, a2);
  bitwuzla_assert(bitwuzla, a3);
  bitwuzla_assert(bitwuzla, a4);
  bitwuzla_check_sat(bitwuzla);

  // Query an interpolant for A /\ B with A = {a1, a2}.
  BitwuzlaTerm A[2]        = {a1, a2};
  BitwuzlaTerm interpolant = bitwuzla_get_interpolant(bitwuzla, 2, A);
  // (not (= x2 #b00))
  bitwuzla_term_print(interpolant, stdout);

  // Query an interpolation sequence for a sequence of A/B-partitions
  //     {
  //       ({a1},        {a2, a3, a4}),
  //       ({a1, a2},    {a3, a4}),
  //       ({a1, a2, a3, {a4})
  //     }
  // given as a list {{a1}, {a2}, {a3}} of increments of A.
  BitwuzlaTerm A1[1]  = {a1};
  BitwuzlaTerm A2[1]  = {a2};
  BitwuzlaTerm A3[1]  = {a3};
  BitwuzlaTerm* As[3] = {A1, A2, A3};
  uint32_t Asc[3]     = {1, 1, 1};
  size_t size;
  BitwuzlaTerm* interpolants =
      bitwuzla_get_interpolants(bitwuzla, 3, Asc, As, &size);
  // [0]: (= ((_ extract 3 3) (bvadd (concat #b00 x1) #b1111)) #b0)
  // [1]: (not (= x2 #b00))
  // [2]: (not (= x3 #b00))
  printf("\n(\n");
  for (uint32_t i = 0; i < size; ++i)
  {
    bitwuzla_term_print(interpolants[i], stdout);
    printf("\n");
  }
  printf(")\n");
}
