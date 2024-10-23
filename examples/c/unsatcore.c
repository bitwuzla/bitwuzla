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
  // First, create a term manager instance.
  BitwuzlaTermManager *tm = bitwuzla_term_manager_new();
  // Create a Bitwuzla options instance.
  BitwuzlaOptions *options = bitwuzla_options_new();
  // Then, enable unsat core extraction.
  // Note: Unsat core extraction is disabled by default.
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_CORES, 1);
  // Then, create a Bitwuzla instance.
  Bitwuzla *bitwuzla = bitwuzla_new(tm, options);

  // Create a bit-vector sort of size 2.
  BitwuzlaSort sortbv2 = bitwuzla_mk_bv_sort(tm, 2);
  // Create a bit-vector sort of size 4.
  BitwuzlaSort sortbv4 = bitwuzla_mk_bv_sort(tm, 4);
  // Create Float16 floatinf-point sort.
  BitwuzlaSort sortfp16 = bitwuzla_mk_fp_sort(tm, 5, 11);

  // Create bit-vector variables.
  // (declare-const x0 (_ BitVec 4))
  BitwuzlaTerm x0 = bitwuzla_mk_const(tm, sortbv4, "x0");
  // (declare-const x1 (_ BitVec 2))
  BitwuzlaTerm x1 = bitwuzla_mk_const(tm, sortbv2, "x1");
  // (declare-const x2 (_ BitVec 2))
  BitwuzlaTerm x2 = bitwuzla_mk_const(tm, sortbv2, "x2");
  // (declare-const x3 (_ BitVec 2))
  BitwuzlaTerm x3 = bitwuzla_mk_const(tm, sortbv2, "x3");
  // (declare-const x4 Float16)
  BitwuzlaTerm x4 = bitwuzla_mk_const(tm, sortfp16, "x4");

  // Create FP positive zero.
  BitwuzlaTerm fpzero = bitwuzla_mk_fp_pos_zero(tm, sortfp16);
  // Create BV zero of size 4.
  BitwuzlaTerm bvzero = bitwuzla_mk_bv_zero(tm, sortbv4);

  // (define-fun f0 ((a Float16)) Bool (fp.gt a (_ +zero 5 11)))
  BitwuzlaTerm a_f0 = bitwuzla_mk_var(tm, sortfp16, "a_f0");
  BitwuzlaTerm f0   = bitwuzla_mk_term2(
      tm,
      BITWUZLA_KIND_LAMBDA,
      a_f0,
      bitwuzla_mk_term2(tm, BITWUZLA_KIND_FP_GT, a_f0, fpzero));

  // (define-fun f1 ((a Float16)) (_ BitVec 4) (ite (f0 a) x0 #b0000))
  BitwuzlaTerm a_f1 = bitwuzla_mk_var(tm, sortfp16, "a_f1");
  BitwuzlaTerm f1   = bitwuzla_mk_term2(
      tm,
      BITWUZLA_KIND_LAMBDA,
      a_f1,
      bitwuzla_mk_term3(tm,
                        BITWUZLA_KIND_ITE,
                        bitwuzla_mk_term2(tm, BITWUZLA_KIND_APPLY, f0, a_f1),
                        x0,
                        bvzero));

  // (define-fun f2 ((a Float16)) (_ BitVec 2) ((_ extract 1 0) (f1 a)))
  BitwuzlaTerm a_f2 = bitwuzla_mk_var(tm, sortfp16, "a_f2");
  BitwuzlaTerm f2   = bitwuzla_mk_term2(
      tm,
      BITWUZLA_KIND_LAMBDA,
      a_f2,
      bitwuzla_mk_term1_indexed2(
          tm,
          BITWUZLA_KIND_BV_EXTRACT,
          bitwuzla_mk_term2(tm, BITWUZLA_KIND_APPLY, f1, a_f2),
          1,
          0));

  // (assert (! (bvult x2 (f2 (_ +zero 5 11))) :named a0))
  BitwuzlaTerm a0 =
      bitwuzla_mk_term2(tm,
                        BITWUZLA_KIND_BV_ULT,
                        x2,
                        bitwuzla_mk_term2(tm, BITWUZLA_KIND_APPLY, f2, fpzero));
  bitwuzla_assert(bitwuzla, a0);

  // (assert (! (= x1 x2 x3) :named a1))
  BitwuzlaTerm a1 = bitwuzla_mk_term3(tm, BITWUZLA_KIND_EQUAL, x1, x2, x3);
  bitwuzla_assert(bitwuzla, a1);

  // (assert (!(= x4 ((_ to_fp_unsigned 5 11) RNE x3)) :named a2))
  BitwuzlaTerm a2 = bitwuzla_mk_term2(
      tm,
      BITWUZLA_KIND_EQUAL,
      x4,
      bitwuzla_mk_term2_indexed2(tm,
                                 BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                 bitwuzla_mk_rm_value(tm, BITWUZLA_RM_RNE),
                                 x3,
                                 5,
                                 11));
  bitwuzla_assert(bitwuzla, a2);

  // (check-sat)
  BitwuzlaResult result = bitwuzla_check_sat(bitwuzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n", bitwuzla_result_to_string(result));

  // (get-unsat-core)
  size_t unsat_core_size;
  const BitwuzlaTerm *unsat_core =
      bitwuzla_get_unsat_core(bitwuzla, &unsat_core_size);
  printf("Unsat Core:\n{\n");
  for (uint32_t i = 0; i < unsat_core_size; ++i)
  {
    printf(" %s\n", bitwuzla_term_to_string(unsat_core[i]));
  }
  printf("}\n");

  // Finally, delete the Bitwuzla solver, options, and term manager instances.
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
  bitwuzla_term_manager_delete(tm);

  return 0;
}
