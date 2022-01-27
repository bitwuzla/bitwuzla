/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <bitset>
#include <vector>

#include "test.h"

extern "C" {
#include "bzlabv.h"
#include "bzlabvprop.h"
#include "bzlaessutils.h"
#include "bzlaexp.h"
#include "bzlaproputils.h"
}

using CreateBinExpFunc   = std::add_pointer<decltype(bzla_exp_bv_and)>::type;
using CreateSliceExpFunc = std::add_pointer<decltype(bzla_exp_bv_slice)>::type;

class TestEssUtils : public TestBzla
{
 protected:
  static constexpr int32_t TEST_ESSUTILS_BW = 3;

  std::vector<std::string> d_values;

  void SetUp() override
  {
    TestBzla::SetUp();
    d_mm = d_bzla->mm;
    initialize_values(TEST_ESSUTILS_BW);
  }

  /* Initialize all possible values for 3-valued constants of bit-width bw */
  void initialize_values(uint32_t bw)
  {
    assert(bw);

    uint32_t psize, num_consts = 1;
    char bit = '0';

    for (uint32_t i = 0; i < bw; i++) num_consts *= 3;
    psize = num_consts;

    std::vector<std::vector<char>> values(psize, std::vector<char>(bw));
    for (size_t i = 0; i < bw; i++)
    {
      psize = psize / 3;
      for (size_t j = 0; j < num_consts; j++)
      {
        values[j][i] = bit;
        if ((j + 1) % psize == 0)
        {
          bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
        }
      }
    }

    for (auto char_vec : values)
    {
      d_values.push_back(std::string(char_vec.begin(), char_vec.end()));
    }
  }

  void test_is_ess_binary_const(BzlaPropIsEssFun is_ess,
                                CreateBinExpFunc create_exp_func,
                                uint32_t pos_x)
  {
    test_is_ess_binary(is_ess, create_exp_func, pos_x, true);
  }

  void test_is_ess_binary(BzlaPropIsEssFun is_ess,
                          CreateBinExpFunc create_exp_func,
                          uint32_t pos_x,
                          bool const_bits = false)
  {
    std::vector<std::string> s_values;
    BzlaBvDomain *s;
    BzlaBitVector *x, *t;
    bool res, status;
    uint32_t pos_s, nval_x, nval_t;

    uint32_t bw_x = TEST_ESSUTILS_BW;
    uint32_t bw_s = TEST_ESSUTILS_BW;
    uint32_t bw_t = TEST_ESSUTILS_BW;

    pos_s = 1 - pos_x;

    /* we test if x is essential wrt to constant bits in s */

    if (const_bits)
    {
      s_values = d_values;
    }
    else
    {
      /* s is unconstrained (no const bits) */
      s_values.push_back("xxx");
    }

    if (create_exp_func == bzla_exp_bv_ult || create_exp_func == bzla_exp_bv_slt
        || create_exp_func == bzla_exp_eq)
    {
      bw_t = 1;
    }
    else if (create_exp_func == bzla_exp_bv_concat)
    {
      bw_s = 2; /* decrease number of tests for concat */
      bw_t = bw_s + bw_x;
    }

    nval_x = 1 << bw_s;
    nval_t = 1 << bw_t;
    for (const std::string &s_value : s_values)
    {
      s = bzla_bvdomain_new_from_char(d_mm, s_value.c_str());
      for (uint32_t i = 0; i < nval_x; i++)
      {
        x = bzla_bv_uint64_to_bv(d_mm, i, bw_s);
        for (uint32_t j = 0; j < nval_t; j++)
        {
          t = bzla_bv_uint64_to_bv(d_mm, j, bw_t);

          BzlaPropInfo pi;
          memset(&pi, 0, sizeof(BzlaPropInfo));
          pi.pos_x        = pos_x;
          pi.bv[pos_x]    = x;
          pi.bvd[pos_s]   = s;
          pi.target_value = t;

          res    = is_ess(d_bzla, &pi, pos_x);
          status = check_sat_is_ess_binary(create_exp_func, s, t, x, pos_s);
          if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

          if (res != status)
          {
            char *vx = bzla_bv_to_char(d_mm, x);
            char *vt = bzla_bv_to_char(d_mm, t);
            std::cout << "pos_x: " << pos_x << std::endl;
            std::cout << "pos_s: " << pos_s << std::endl;
            std::cout << "t: " << vt << std::endl;
            std::cout << "s: " << s_value << std::endl;
            std::cout << "x: " << vx << std::endl;
            std::cout << "is_ess(" << pos_x << "): " << res << std::endl;
            bzla_mem_freestr(d_mm, vx);
            bzla_mem_freestr(d_mm, vt);
          }

          assert(res == status);
          ASSERT_EQ(res, status);
          bzla_bv_free(d_mm, t);
        }
        bzla_bv_free(d_mm, x);
      }
      bzla_bvdomain_free(d_mm, s);
    }
  }

  void test_is_ess_cond(uint32_t pos_x, bool const_bits)
  {
    std::vector<std::string> s0_values, s1_values;
    BzlaBvDomain *s0, *s1;
    BzlaBitVector *x, *t;
    std::vector<BzlaBitVector *> bvs0_values, bvs1_values;
    char *vt, *vx, *vs0, *vs1;
    bool res, status;
    uint32_t bw_x, bw = TEST_ESSUTILS_BW;
    uint32_t nval, nval_x, pos_s0, pos_s1;
    BzlaBvDomainGenerator gen;

    if (pos_x == 0)
    {
      bw_x   = 1;
      pos_s0 = 1;
      pos_s1 = 2;
      if (const_bits)
      {
        s0_values = d_values;
        s1_values = d_values;
      }
      else
      {
        s0_values.push_back("xxx");
        s1_values.push_back("xxx");
      }
    }
    else
    {
      pos_s0 = pos_x == 0 ? 1 : 0;
      pos_s1 = pos_x == 2 ? 1 : 2;
      bw_x   = bw;
      if (const_bits)
      {
        s0_values.push_back("x");
        s0_values.push_back("0");
        s0_values.push_back("1");
        s1_values = d_values;
      }
      else
      {
        s0_values.push_back("x");
        s1_values.push_back("xxx");
      }
    }
    nval   = 1 << bw;
    nval_x = 1 << bw_x;

    for (const std::string &s0_value : s0_values)
    {
      s0 = bzla_bvdomain_new_from_char(d_mm, s0_value.c_str());
      for (const std::string &s1_value : s1_values)
      {
        s1 = bzla_bvdomain_new_from_char(d_mm, s1_value.c_str());
        for (uint32_t j = 0; j < nval_x; j++)
        {
          x  = bzla_bv_uint64_to_bv(d_mm, j, bw_x);
          vx = bzla_bv_to_char(d_mm, x);
          for (uint32_t k = 0; k < nval; k++)
          {
            t  = bzla_bv_uint64_to_bv(d_mm, k, bw);
            vt = bzla_bv_to_char(d_mm, t);

            if (bzla_bvdomain_is_fixed(d_mm, s0))
            {
              bvs0_values.push_back(bzla_bv_copy(d_mm, s0->lo));
            }
            else
            {
              bzla_bvdomain_gen_init(d_mm, 0, &gen, s0);
              while (bzla_bvdomain_gen_has_next(&gen))
              {
                bvs0_values.push_back(
                    bzla_bv_copy(d_mm, bzla_bvdomain_gen_next(&gen)));
              }
              bzla_bvdomain_gen_delete(&gen);
            }
            if (bzla_bvdomain_is_fixed(d_mm, s1))
            {
              bvs1_values.push_back(bzla_bv_copy(d_mm, s1->lo));
            }
            else
            {
              bzla_bvdomain_gen_init(d_mm, 0, &gen, s1);
              while (bzla_bvdomain_gen_has_next(&gen))
              {
                bvs1_values.push_back(
                    bzla_bv_copy(d_mm, bzla_bvdomain_gen_next(&gen)));
              }
              bzla_bvdomain_gen_delete(&gen);
            }
            for (BzlaBitVector *bvs0 : bvs0_values)
            {
              vs0 = bzla_bv_to_char(d_mm, bvs0);
              for (BzlaBitVector *bvs1 : bvs1_values)
              {
                vs1 = bzla_bv_to_char(d_mm, bvs1);
                BzlaPropInfo pi;
                memset(&pi, 0, sizeof(BzlaPropInfo));
                pi.pos_x        = pos_x;
                pi.bvd[pos_s0]  = s0;
                pi.bvd[pos_s1]  = s1;
                pi.bv[pos_x]    = x;
                pi.bv[pos_s0]   = bvs0;
                pi.bv[pos_s1]   = bvs1;
                pi.target_value = t;

                if (const_bits)
                {
                  res = bzla_is_ess_cond_const(d_bzla, &pi, pos_x);
                }
                else
                {
                  res = bzla_is_ess_cond(d_bzla, &pi, pos_x);
                }
                status = check_sat_is_ess_cond(x, t, s0, s1, pos_x);
                if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

                if (res != status)
                {
                  std::cout << "pos_x: " << pos_x << std::endl;
                  std::cout << "t: " << vt << std::endl;
                  std::cout << "x: " << vx << std::endl;
                  std::cout << "s0: " << s0_value << std::endl;
                  std::cout << "s1: " << s1_value << std::endl;
                  std::cout << "vs0: " << vs0 << std::endl;
                  std::cout << "vs1: " << vs1 << std::endl;
                }

                ASSERT_EQ(res, status);
                bzla_mem_freestr(d_mm, vs1);
              }
              bzla_mem_freestr(d_mm, vs0);
            }
            for (BzlaBitVector *bvs0 : bvs0_values)
            {
              bzla_bv_free(d_mm, bvs0);
            }
            for (BzlaBitVector *bvs1 : bvs1_values)
            {
              bzla_bv_free(d_mm, bvs1);
            }
            bvs0_values.clear();
            bvs1_values.clear();
            bzla_bv_free(d_mm, t);
            bzla_mem_freestr(d_mm, vt);
          }
          bzla_bv_free(d_mm, x);
          bzla_mem_freestr(d_mm, vx);
        }
        bzla_bvdomain_free(d_mm, s1);
      }
      bzla_bvdomain_free(d_mm, s0);
    }
  }

  void test_is_ess_slice(BzlaPropIsEssFun is_ess, bool const_bits)
  {
    BzlaBitVector *t, *x;
    char *vt, *vx;
    (void) const_bits;

    uint32_t bw_x = TEST_ESSUTILS_BW;

    for (uint32_t j = 0, n = 1 << bw_x; j < n; j++)
    {
      x  = bzla_bv_uint64_to_bv(d_mm, j, bw_x);
      vx = bzla_bv_to_char(d_mm, x);
      for (uint32_t lower = 0; lower < bw_x; ++lower)
      {
        for (uint32_t upper = lower; upper < bw_x; ++upper)
        {
          uint32_t bw_t   = upper - lower + 1;
          uint32_t nval_t = 1 << bw_t;
          for (uint32_t i = 0; i < nval_t; ++i)
          {
            t  = bzla_bv_uint64_to_bv(d_mm, i, bw_t);
            vt = bzla_bv_to_char(d_mm, t);

            BzlaSortId sort = bzla_sort_bv(d_bzla, bw_x);
            BzlaNode *var   = bzla_exp_var(d_bzla, sort, nullptr);
            bzla_sort_release(d_bzla, sort);
            BzlaNode *slice =
                bzla_node_create_bv_slice(d_bzla, var, upper, lower);
            bzla_node_release(d_bzla, var);

            BzlaPropInfo pi;
            memset(&pi, 0, sizeof(BzlaPropInfo));
            pi.exp          = slice;
            pi.bv[0]        = x;
            pi.target_value = t;

            bool res    = is_ess(d_bzla, &pi, 0);
            bool status = check_sat_is_ess_slice(x, t, upper, lower);

            if (res != status)
            {
              std::cout << "upper: " << upper << std::endl;
              std::cout << "lower: " << lower << std::endl;
              std::cout << "t: " << vt << std::endl;
              std::cout << "x: " << vx << std::endl;
            }

            ASSERT_EQ(res, status);
            bzla_bv_free(d_mm, t);
            bzla_mem_freestr(d_mm, vt);
            bzla_node_release(d_bzla, slice);
          }
        }
      }
      bzla_mem_freestr(d_mm, vx);
      bzla_bv_free(d_mm, x);
    }
  }

  bool check_sat_is_ess_binary(CreateBinExpFunc create_exp_func,
                               BzlaBvDomain *s,
                               BzlaBitVector *t,
                               BzlaBitVector *x,
                               uint32_t pos_x)
  {
    BzlaSortId sort;
    BzlaNode *ns, *nslo, *nshi, *nx, *nt;
    BzlaNode *andhi, *orlo, *eq, *exp;

    Bzla *bzla = bzla_new();

    sort = bzla_sort_bv(bzla, bzla_bv_get_width(s->lo));
    ns   = bzla_exp_var(bzla, sort, 0);

    nslo = bzla_exp_bv_const(bzla, s->lo);
    nshi = bzla_exp_bv_const(bzla, s->hi);

    /* assert const bits for s */
    andhi = bzla_exp_bv_and(bzla, ns, nshi);
    eq    = bzla_exp_eq(bzla, andhi, ns);
    bzla_assert_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    orlo = bzla_exp_bv_or(bzla, ns, nslo);
    eq   = bzla_exp_eq(bzla, orlo, ns);
    bzla_assert_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    /* s <> x = t  for operator <> */

    nx = bzla_exp_bv_const(bzla, x);
    nt = bzla_exp_bv_const(bzla, t);

    if (pos_x == 0)
    {
      exp = create_exp_func(bzla, ns, nx);
    }
    else
    {
      assert(pos_x == 1);
      exp = create_exp_func(bzla, nx, ns);
    }

    eq = bzla_exp_eq(bzla, exp, nt);
    bzla_assert_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    int32_t status = bzla_check_sat(bzla, -1, -1);
    assert(status == BZLA_RESULT_SAT || status == BZLA_RESULT_UNSAT);

    bzla_sort_release(bzla, sort);
    bzla_node_release(bzla, exp);
    bzla_node_release(bzla, ns);
    bzla_node_release(bzla, nslo);
    bzla_node_release(bzla, nshi);
    bzla_node_release(bzla, nx);
    bzla_node_release(bzla, nt);
    bzla_node_release(bzla, andhi);
    bzla_node_release(bzla, orlo);

    bzla_delete(bzla);

    return status == BZLA_RESULT_UNSAT;
  }

  bool check_sat_is_ess_cond(BzlaBitVector *x,
                             BzlaBitVector *t,
                             BzlaBvDomain *s0,
                             BzlaBvDomain *s1,
                             uint32_t pos_x)
  {
    BzlaSortId ss0, ss1;
    BzlaNode *nx, *ns0lo, *ns0hi, *ns1lo, *ns1hi, *ns0, *ns1, *nt;
    BzlaNode *ands0hi, *ands1hi, *ors0lo, *ors1lo, *eq, *eqs, *exp;
    int32_t status;

    Bzla *bzla = bzla_new();

    ss0 = bzla_sort_bv(bzla, bzla_bv_get_width(s0->lo));
    ns0 = bzla_exp_var(bzla, ss0, "s0");

    ss1 = bzla_sort_bv(bzla, bzla_bv_get_width(s1->lo));
    ns1 = bzla_exp_var(bzla, ss1, "s1");

    ns0lo = bzla_exp_bv_const(bzla, s0->lo);

    ns1lo = bzla_exp_bv_const(bzla, s1->lo);

    ns0hi = bzla_exp_bv_const(bzla, s0->hi);

    ns1hi = bzla_exp_bv_const(bzla, s1->hi);

    nx = bzla_exp_bv_const(bzla, x);
    nt = bzla_exp_bv_const(bzla, t);

    if (pos_x == 0)
    {
      exp = bzla_exp_cond(bzla, nx, ns0, ns1);
    }
    else if (pos_x == 1)
    {
      exp = bzla_exp_cond(bzla, ns0, nx, ns1);
    }
    else
    {
      assert(pos_x == 2);
      exp = bzla_exp_cond(bzla, ns0, ns1, nx);
    }

    eq = bzla_exp_eq(bzla, exp, nt);
    bzla_assert_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    /* assert const bits for s0 and check */
    ands0hi = bzla_exp_bv_and(bzla, ns0, ns0hi);
    eqs     = bzla_exp_eq(bzla, ands0hi, ns0);
    bzla_assert_exp(bzla, eqs);
    bzla_node_release(bzla, eqs);
    bzla_node_release(bzla, ands0hi);
    ors0lo = bzla_exp_bv_or(bzla, ns0, ns0lo);
    eqs    = bzla_exp_eq(bzla, ors0lo, ns0);
    bzla_assert_exp(bzla, eqs);
    bzla_node_release(bzla, eqs);
    bzla_node_release(bzla, ors0lo);
    /* assert const bits for s1 */
    ands1hi = bzla_exp_bv_and(bzla, ns1, ns1hi);
    eqs     = bzla_exp_eq(bzla, ands1hi, ns1);
    bzla_assert_exp(bzla, eqs);
    bzla_node_release(bzla, eqs);
    ors1lo = bzla_exp_bv_or(bzla, ns1, ns1lo);
    eqs    = bzla_exp_eq(bzla, ors1lo, ns1);
    bzla_assert_exp(bzla, eqs);
    bzla_node_release(bzla, eqs);

    status = bzla_check_sat(bzla, -1, -1);
    assert(status == BZLA_RESULT_SAT || status == BZLA_RESULT_UNSAT);

    bzla_node_release(bzla, ands1hi);
    bzla_node_release(bzla, ors1lo);

    bzla_sort_release(bzla, ss0);
    bzla_sort_release(bzla, ss1);
    bzla_node_release(bzla, exp);
    bzla_node_release(bzla, nx);
    bzla_node_release(bzla, ns0lo);
    bzla_node_release(bzla, ns0hi);
    bzla_node_release(bzla, ns1lo);
    bzla_node_release(bzla, ns1hi);
    bzla_node_release(bzla, ns0);
    bzla_node_release(bzla, ns1);
    bzla_node_release(bzla, nt);

    bzla_delete(bzla);
    return status == BZLA_RESULT_UNSAT;
  }

  bool check_sat_is_ess_slice(BzlaBitVector *x,
                              BzlaBitVector *t,
                              uint32_t upper,
                              uint32_t lower)
  {
    BzlaNode *nx, *nt;
    BzlaNode *eq, *exp;

    Bzla *bzla = bzla_new();

    nt = bzla_exp_bv_const(bzla, t);
    nx = bzla_exp_bv_const(bzla, x);

    exp = bzla_exp_bv_slice(bzla, nx, upper, lower);
    eq  = bzla_exp_eq(bzla, exp, nt);
    bzla_assert_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    int32_t status = bzla_check_sat(bzla, -1, -1);
    assert(status == BZLA_RESULT_SAT || status == BZLA_RESULT_UNSAT);

    bzla_node_release(bzla, exp);
    bzla_node_release(bzla, nx);
    bzla_node_release(bzla, nt);

    bzla_delete(bzla);

    return status == BZLA_RESULT_UNSAT;
  }

  BzlaMemMgr *d_mm;
};

/* Test is_ess_*_const functions. */

TEST_F(TestEssUtils, is_ess_add_const)
{
  test_is_ess_binary_const(bzla_is_ess_add_const, bzla_exp_bv_add, 0);
}

TEST_F(TestEssUtils, is_ess_and_const)
{
  test_is_ess_binary_const(bzla_is_ess_and_const, bzla_exp_bv_and, 0);
}

TEST_F(TestEssUtils, is_ess_xor_const)
{
  test_is_ess_binary_const(bzla_is_ess_xor_const, bzla_exp_bv_xor, 0);
}

TEST_F(TestEssUtils, is_ess_concat_const)
{
  test_is_ess_binary_const(bzla_is_ess_concat_const, bzla_exp_bv_concat, 0);
  test_is_ess_binary_const(bzla_is_ess_concat_const, bzla_exp_bv_concat, 1);
}

TEST_F(TestEssUtils, is_ess_eq_const)
{
  test_is_ess_binary_const(bzla_is_ess_eq_const, bzla_exp_eq, 0);
}

TEST_F(TestEssUtils, is_ess_ult_const)
{
  test_is_ess_binary_const(bzla_is_ess_ult_const, bzla_exp_bv_ult, 0);
  test_is_ess_binary_const(bzla_is_ess_ult_const, bzla_exp_bv_ult, 1);
}

TEST_F(TestEssUtils, is_ess_slt_const)
{
  test_is_ess_binary_const(bzla_is_ess_slt_const, bzla_exp_bv_slt, 0);
  test_is_ess_binary_const(bzla_is_ess_slt_const, bzla_exp_bv_slt, 1);
}

TEST_F(TestEssUtils, is_ess_slice_const)
{
  test_is_ess_slice(bzla_is_ess_slice_const, true);
}

TEST_F(TestEssUtils, is_ess_sll_const)
{
  test_is_ess_binary_const(bzla_is_ess_sll_const, bzla_exp_bv_sll, 0);
  test_is_ess_binary_const(bzla_is_ess_sll_const, bzla_exp_bv_sll, 1);
}

TEST_F(TestEssUtils, is_ess_srl_const)
{
  test_is_ess_binary_const(bzla_is_ess_srl_const, bzla_exp_bv_srl, 0);
  test_is_ess_binary_const(bzla_is_ess_srl_const, bzla_exp_bv_srl, 1);
}

TEST_F(TestEssUtils, is_ess_sra_const)
{
  test_is_ess_binary_const(bzla_is_ess_sra_const, bzla_exp_bv_sra, 0);
  test_is_ess_binary_const(bzla_is_ess_sra_const, bzla_exp_bv_sra, 1);
}

TEST_F(TestEssUtils, is_ess_mul_const)
{
  test_is_ess_binary_const(bzla_is_ess_mul_const, bzla_exp_bv_mul, 0);
}

TEST_F(TestEssUtils, is_ess_urem_const)
{
  test_is_ess_binary_const(bzla_is_ess_urem_const, bzla_exp_bv_urem, 0);
  test_is_ess_binary_const(bzla_is_ess_urem_const, bzla_exp_bv_urem, 1);
}

TEST_F(TestEssUtils, is_ess_udiv_const)
{
  test_is_ess_binary_const(bzla_is_ess_udiv_const, bzla_exp_bv_udiv, 0);
  test_is_ess_binary_const(bzla_is_ess_udiv_const, bzla_exp_bv_udiv, 1);
}

TEST_F(TestEssUtils, is_ess_cond_const)
{
  test_is_ess_cond(0, true);
  test_is_ess_cond(1, true);
  test_is_ess_cond(2, true);
}

/* Test is_ess_* functions (no const bits). */

TEST_F(TestEssUtils, is_ess_add)
{
  test_is_ess_binary(bzla_is_ess_add, bzla_exp_bv_add, 0);
}

TEST_F(TestEssUtils, is_ess_and)
{
  test_is_ess_binary(bzla_is_ess_and, bzla_exp_bv_and, 0);
}

TEST_F(TestEssUtils, is_ess_xor)
{
  test_is_ess_binary(bzla_is_ess_xor, bzla_exp_bv_xor, 0);
}

TEST_F(TestEssUtils, is_ess_concat)
{
  test_is_ess_binary(bzla_is_ess_concat, bzla_exp_bv_concat, 0);
  test_is_ess_binary(bzla_is_ess_concat, bzla_exp_bv_concat, 1);
}

TEST_F(TestEssUtils, is_ess_eq)
{
  test_is_ess_binary(bzla_is_ess_eq, bzla_exp_eq, 0);
}

TEST_F(TestEssUtils, is_ess_mul)
{
  test_is_ess_binary(bzla_is_ess_mul, bzla_exp_bv_mul, 0);
}

TEST_F(TestEssUtils, is_ess_slice)
{
  test_is_ess_slice(bzla_is_ess_slice, false);
}

TEST_F(TestEssUtils, is_ess_sll)
{
  test_is_ess_binary(bzla_is_ess_sll, bzla_exp_bv_sll, 0);
  test_is_ess_binary(bzla_is_ess_sll, bzla_exp_bv_sll, 1);
}

TEST_F(TestEssUtils, is_ess_srl)
{
  test_is_ess_binary(bzla_is_ess_srl, bzla_exp_bv_srl, 0);
  test_is_ess_binary(bzla_is_ess_srl, bzla_exp_bv_srl, 1);
}

TEST_F(TestEssUtils, is_ess_sra)
{
  test_is_ess_binary(bzla_is_ess_sra, bzla_exp_bv_sra, 0);
  test_is_ess_binary(bzla_is_ess_sra, bzla_exp_bv_sra, 1);
}

TEST_F(TestEssUtils, is_ess_udiv)
{
  test_is_ess_binary(bzla_is_ess_udiv, bzla_exp_bv_udiv, 0);
  test_is_ess_binary(bzla_is_ess_udiv, bzla_exp_bv_udiv, 1);
}

TEST_F(TestEssUtils, is_ess_ult)
{
  test_is_ess_binary(bzla_is_ess_ult, bzla_exp_bv_ult, 0);
  test_is_ess_binary(bzla_is_ess_ult, bzla_exp_bv_ult, 1);
}

TEST_F(TestEssUtils, is_ess_slt)
{
  test_is_ess_binary(bzla_is_ess_slt, bzla_exp_bv_slt, 0);
  test_is_ess_binary(bzla_is_ess_slt, bzla_exp_bv_slt, 1);
}

TEST_F(TestEssUtils, is_ess_urem)
{
  test_is_ess_binary(bzla_is_ess_urem, bzla_exp_bv_urem, 0);
  test_is_ess_binary(bzla_is_ess_urem, bzla_exp_bv_urem, 1);
}

TEST_F(TestEssUtils, is_ess_cond)
{
  test_is_ess_cond(0, false);
  test_is_ess_cond(1, false);
  test_is_ess_cond(2, false);
}
