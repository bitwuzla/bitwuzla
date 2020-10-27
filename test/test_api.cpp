/**
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

class TestApi : public TestBitwuzla
{
};

TEST_F(TestApi, term_fun_get_domain_sorts)
{
  BitwuzlaSort bv_sort32 = bitwuzla_mk_bv_sort(d_bzla, 32);
  BitwuzlaSort bv_sort8  = bitwuzla_mk_bv_sort(d_bzla, 8);
  BitwuzlaTerm *bv_term  = bitwuzla_mk_const(d_bzla, bv_sort32, "bv");
  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sort(bv_term), "");

  BitwuzlaSort array_sort = bitwuzla_mk_array_sort(d_bzla, bv_sort32, bv_sort8);
  BitwuzlaTerm *array_term   = bitwuzla_mk_const(d_bzla, array_sort, "array");
  const BitwuzlaSort *isorts = bitwuzla_term_fun_get_domain_sorts(array_term);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort32, isorts[0]));
  ASSERT_EQ(isorts[1], (BitwuzlaSort) 0);

  BitwuzlaSort domain[]  = {bv_sort32, bv_sort8, bv_sort32};
  BitwuzlaSort fun_sort  = bitwuzla_mk_fun_sort(d_bzla, 3, domain, bv_sort8);
  BitwuzlaTerm *fun_term = bitwuzla_mk_const(d_bzla, fun_sort, "fun");
  const BitwuzlaSort *dsorts = bitwuzla_term_fun_get_domain_sorts(fun_term);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort32, dsorts[0]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort8, dsorts[1]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort32, dsorts[2]));
  ASSERT_EQ(dsorts[3], (BitwuzlaSort) 0);
}
