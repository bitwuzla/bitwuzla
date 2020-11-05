/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019-2020 Aina Niemetz
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include <bitset>

#include "test.h"

extern "C" {
#include "bzlabv.h"
#include "bzlaexp.h"
#include "bzlafp.h"
}

class TestFp : public TestBitwuzla
{
};

class TestFpInternal : public TestBzla
{
 protected:
  void test_fp_as_bv(std::string sign, std::string exp, std::string sig)
  {
    assert(sign.size() == 1);

    BzlaSortId sort_fp, sort_sign, sort_exp, sort_sig;
    BzlaNode *node_fp, *node_bv_sign, *node_bv_exp, *node_bv_sig;
    BzlaBitVector *bv_sign, *bv_exp, *bv_sig;
    BzlaBitVector *res_sign, *res_exp, *res_sig;
    BzlaFloatingPoint *fp;
    uint32_t bw_sig, bw_exp;

    bv_sign = bzla_bv_char_to_bv(d_bzla->mm, sign.c_str());
    bv_exp  = bzla_bv_char_to_bv(d_bzla->mm, exp.c_str());
    bv_sig  = bzla_bv_char_to_bv(d_bzla->mm, sig.c_str());

    bw_exp = exp.size();
    bw_sig = sig.size() + 1;

    sort_sign = bzla_sort_bv(d_bzla, 1);
    sort_exp  = bzla_sort_bv(d_bzla, bw_exp);
    sort_sig  = bzla_sort_bv(d_bzla, bw_sig);

    node_bv_sign = bzla_exp_bv_const(d_bzla, bv_sign);
    node_bv_exp  = bzla_exp_bv_const(d_bzla, bv_exp);
    node_bv_sig  = bzla_exp_bv_const(d_bzla, bv_sig);

    sort_fp = bzla_sort_fp(d_bzla, bw_exp, bw_sig);
    node_fp = bzla_exp_fp_const(d_bzla, node_bv_sign, node_bv_exp, node_bv_sig);

    fp = bzla_fp_get_fp(node_fp);
    bzla_fp_as_bv(d_bzla, fp, &res_sign, &res_exp, &res_sig);
    if (bzla_fp_is_nan(d_bzla, fp))
    {
      BzlaFloatingPoint *nan = bzla_fp_nan(d_bzla, sort_fp);
      ASSERT_EQ(bzla_fp_compare(fp, nan), 0);
      bzla_fp_free(d_bzla, nan);
    }
    else
    {
      ASSERT_EQ(bzla_bv_compare(bv_sign, res_sign), 0);
      ASSERT_EQ(bzla_bv_compare(bv_exp, res_exp), 0);
      ASSERT_EQ(bzla_bv_compare(bv_sig, res_sig), 0);
    }

    bzla_node_release(d_bzla, node_fp);
    bzla_sort_release(d_bzla, sort_fp);
    bzla_node_release(d_bzla, node_bv_sig);
    bzla_node_release(d_bzla, node_bv_exp);
    bzla_node_release(d_bzla, node_bv_sign);
    bzla_sort_release(d_bzla, sort_sig);
    bzla_sort_release(d_bzla, sort_exp);
    bzla_sort_release(d_bzla, sort_sign);
    bzla_bv_free(d_bzla->mm, bv_sig);
    bzla_bv_free(d_bzla->mm, bv_exp);
    bzla_bv_free(d_bzla->mm, bv_sign);
    bzla_bv_free(d_bzla->mm, res_sig);
    bzla_bv_free(d_bzla->mm, res_exp);
    bzla_bv_free(d_bzla->mm, res_sign);
  }
};

TEST_F(TestFp, sort_fp)
{
  BitwuzlaSort *f16, *f32, *f64, *f128;

  f16 = bitwuzla_mk_fp_sort(d_bzla, 5, 11);
  ASSERT_TRUE(bitwuzla_sort_is_fp(d_bzla, f16));

  f32 = bitwuzla_mk_fp_sort(d_bzla, 8, 24);
  ASSERT_TRUE(bitwuzla_sort_is_fp(d_bzla, f32));

  f64 = bitwuzla_mk_fp_sort(d_bzla, 11, 53);
  ASSERT_TRUE(bitwuzla_sort_is_fp(d_bzla, f64));

  f128 = bitwuzla_mk_fp_sort(d_bzla, 15, 113);
  ASSERT_TRUE(bitwuzla_sort_is_fp(d_bzla, f128));
}

TEST_F(TestFp, sort_rm)
{
  BitwuzlaSort *rm;

  rm = bitwuzla_mk_rm_sort(d_bzla);
  ASSERT_TRUE(bitwuzla_sort_is_rm(d_bzla, rm));
}

TEST_F(TestFpInternal, fp_as_bv)
{
  for (uint64_t i = 0; i < (1u << 5); ++i)
  {
    std::stringstream ss;
    std::string exp = std::bitset<5>(i).to_string();
    for (uint64_t j = 0; j < (1u << 10); ++j)
    {
      std::stringstream ss;
      std::string sig = std::bitset<10>(j).to_string();
      test_fp_as_bv("0", exp.c_str(), sig.c_str());
      test_fp_as_bv("1", exp.c_str(), sig.c_str());
    }
  }
}

TEST_F(TestFpInternal, fp_is_const)
{
  BzlaSortId f16      = bzla_sort_fp(d_bzla, 5, 11);
  BzlaSortId f32      = bzla_sort_fp(d_bzla, 8, 24);
  BzlaSortId f64      = bzla_sort_fp(d_bzla, 11, 53);
  BzlaSortId f128     = bzla_sort_fp(d_bzla, 15, 113);
  BzlaSortId sorts[4] = {f16, f32, f64, f128};

  for (uint32_t i = 0; i < 4; i++)
  {
    BzlaNode *pzero = bzla_exp_fp_pos_zero(d_bzla, sorts[i]);
    ASSERT_TRUE(bzla_node_is_fp_const_pos_zero(d_bzla, pzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_zero(d_bzla, pzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_inf(d_bzla, pzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_inf(d_bzla, pzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_nan(d_bzla, pzero));
    bzla_node_release(d_bzla, pzero);

    BzlaNode *nzero = bzla_exp_fp_neg_zero(d_bzla, sorts[i]);
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_zero(d_bzla, nzero));
    ASSERT_TRUE(bzla_node_is_fp_const_neg_zero(d_bzla, nzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_inf(d_bzla, nzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_inf(d_bzla, nzero));
    ASSERT_TRUE(!bzla_node_is_fp_const_nan(d_bzla, nzero));
    bzla_node_release(d_bzla, nzero);

    BzlaNode *pinf = bzla_exp_fp_pos_inf(d_bzla, sorts[i]);
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_zero(d_bzla, pinf));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_zero(d_bzla, pinf));
    ASSERT_TRUE(bzla_node_is_fp_const_pos_inf(d_bzla, pinf));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_inf(d_bzla, pinf));
    ASSERT_TRUE(!bzla_node_is_fp_const_nan(d_bzla, pinf));
    bzla_node_release(d_bzla, pinf);

    BzlaNode *ninf = bzla_exp_fp_neg_inf(d_bzla, sorts[i]);
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_zero(d_bzla, ninf));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_zero(d_bzla, ninf));
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_inf(d_bzla, ninf));
    ASSERT_TRUE(bzla_node_is_fp_const_neg_inf(d_bzla, ninf));
    ASSERT_TRUE(!bzla_node_is_fp_const_nan(d_bzla, ninf));
    bzla_node_release(d_bzla, ninf);

    BzlaNode *nan = bzla_exp_fp_nan(d_bzla, sorts[i]);
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_zero(d_bzla, nan));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_zero(d_bzla, nan));
    ASSERT_TRUE(!bzla_node_is_fp_const_pos_inf(d_bzla, nan));
    ASSERT_TRUE(!bzla_node_is_fp_const_neg_inf(d_bzla, nan));
    ASSERT_TRUE(bzla_node_is_fp_const_nan(d_bzla, nan));
    bzla_node_release(d_bzla, nan);
  }

  bzla_sort_release(d_bzla, f16);
  bzla_sort_release(d_bzla, f32);
  bzla_sort_release(d_bzla, f64);
  bzla_sort_release(d_bzla, f128);
}
