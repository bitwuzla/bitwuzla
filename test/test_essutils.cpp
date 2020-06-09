/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include <bitset>
#include <vector>

#include "test.h"

extern "C" {
#include "boolector.h"
#include "bzlabv.h"
#include "bzlabvprop.h"
#include "bzlaessutils.h"
#include "bzlaexp.h"
#include "bzlaproputils.h"
}

using CreateBinExpFunc   = std::add_pointer<decltype(boolector_bv_and)>::type;
using CreateSliceExpFunc = std::add_pointer<decltype(boolector_bv_slice)>::type;

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
    char *vx, *vt;
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

    if (create_exp_func == boolector_bv_ult
        || create_exp_func == boolector_bv_slt
        || create_exp_func == boolector_eq)
    {
      bw_t = 1;
    }
    else if (create_exp_func == boolector_bv_concat)
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
        x  = bzla_bv_uint64_to_bv(d_mm, i, bw_s);
        vx = bzla_bv_to_char(d_mm, x);
        for (uint32_t j = 0; j < nval_t; j++)
        {
          t  = bzla_bv_uint64_to_bv(d_mm, j, bw_t);
          vt = bzla_bv_to_char(d_mm, t);

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
            std::cout << "pos_x: " << pos_x << std::endl;
            std::cout << "pos_s: " << pos_s << std::endl;
            std::cout << "t: " << vt << std::endl;
            std::cout << "s: " << s_value << std::endl;
            std::cout << "x: " << vx << std::endl;
            std::cout << "is_ess(" << pos_x << "): " << res << std::endl;
          }

          assert(res == status);
          ASSERT_EQ(res, status);
          bzla_bv_free(d_mm, t);
          bzla_mem_freestr(d_mm, vt);
        }
        bzla_bv_free(d_mm, x);
        bzla_mem_freestr(d_mm, vx);
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
    BoolectorSort sx;
    BoolectorNode *nx, *nxlo, *nxhi, *ns, *nt;
    BoolectorNode *andhi, *orlo, *eq, *exp;
    char *vx, *vt, *vslo, *vshi;

    Bzla *bzla = boolector_new();

    boolector_set_opt(bzla, BZLA_OPT_INCREMENTAL, 1);

    vx = bzla_bv_to_char(d_mm, x);
    vt = bzla_bv_to_char(d_mm, t);

    sx = boolector_bv_sort(bzla, bzla_bv_get_width(s->lo));
    nx = boolector_var(bzla, sx, 0);

    vslo = bzla_bv_to_char(d_mm, s->lo);
    nxlo = boolector_bv_const(bzla, vslo);

    vshi = bzla_bv_to_char(d_mm, s->hi);
    nxhi = boolector_bv_const(bzla, vshi);

    /* assume const bits for s */
    andhi = boolector_bv_and(bzla, nx, nxhi);
    eq    = boolector_eq(bzla, andhi, nx);
    boolector_assume(bzla, eq);
    boolector_release(bzla, eq);

    orlo = boolector_bv_or(bzla, nx, nxlo);
    eq   = boolector_eq(bzla, orlo, nx);
    boolector_assume(bzla, eq);
    boolector_release(bzla, eq);

    /* s <> x = t  for operator <> */

    ns = boolector_bv_const(bzla, vx);
    nt = boolector_bv_const(bzla, vt);

    if (pos_x == 0)
      exp = create_exp_func(bzla, nx, ns);
    else
    {
      assert(pos_x == 1);
      exp = create_exp_func(bzla, ns, nx);
    }

    eq = boolector_eq(bzla, exp, nt);
    boolector_assume(bzla, eq);
    boolector_release(bzla, eq);

    int32_t status = boolector_sat(bzla);
    assert(status == BOOLECTOR_SAT || status == BOOLECTOR_UNSAT);

    boolector_release_sort(bzla, sx);
    boolector_release(bzla, exp);
    boolector_release(bzla, nx);
    boolector_release(bzla, nxlo);
    boolector_release(bzla, nxhi);
    boolector_release(bzla, ns);
    boolector_release(bzla, nt);
    boolector_release(bzla, andhi);
    boolector_release(bzla, orlo);

    bzla_mem_freestr(d_mm, vx);
    bzla_mem_freestr(d_mm, vt);
    bzla_mem_freestr(d_mm, vslo);
    bzla_mem_freestr(d_mm, vshi);
    boolector_delete(bzla);

    return status == BOOLECTOR_UNSAT;
  }

  bool check_sat_is_ess_cond(BzlaBitVector *x,
                             BzlaBitVector *t,
                             BzlaBvDomain *s0,
                             BzlaBvDomain *s1,
                             uint32_t pos_x)
  {
    BoolectorSort ss0, ss1;
    BoolectorNode *nx, *ns0lo, *ns0hi, *ns1lo, *ns1hi, *ns0, *ns1, *nt;
    BoolectorNode *ands0hi, *ands1hi, *ors0lo, *ors1lo, *eq, *eqs, *exp;
    char *vx, *vt, *vs0lo, *vs1lo, *vs0hi, *vs1hi;
    int32_t status;

    Bzla *bzla = boolector_new();

    boolector_set_opt(bzla, BZLA_OPT_INCREMENTAL, 1);

    vx = bzla_bv_to_char(d_mm, x);
    vt = bzla_bv_to_char(d_mm, t);

    ss0 = boolector_bv_sort(bzla, bzla_bv_get_width(s0->lo));
    ns0 = boolector_var(bzla, ss0, "s0");

    ss1 = boolector_bv_sort(bzla, bzla_bv_get_width(s1->lo));
    ns1 = boolector_var(bzla, ss1, "s1");

    vs0lo = bzla_bv_to_char(d_mm, s0->lo);
    ns0lo = boolector_bv_const(bzla, vs0lo);

    vs1lo = bzla_bv_to_char(d_mm, s1->lo);
    ns1lo = boolector_bv_const(bzla, vs1lo);

    vs0hi = bzla_bv_to_char(d_mm, s0->hi);
    ns0hi = boolector_bv_const(bzla, vs0hi);

    vs1hi = bzla_bv_to_char(d_mm, s1->hi);
    ns1hi = boolector_bv_const(bzla, vs1hi);

    nx = boolector_bv_const(bzla, vx);
    nt = boolector_bv_const(bzla, vt);

    if (pos_x == 0)
    {
      exp = boolector_cond(bzla, nx, ns0, ns1);
    }
    else if (pos_x == 1)
    {
      exp = boolector_cond(bzla, ns0, nx, ns1);
    }
    else
    {
      assert(pos_x == 2);
      exp = boolector_cond(bzla, ns0, ns1, nx);
    }

    eq = boolector_eq(bzla, exp, nt);
    boolector_assert(bzla, eq);
    boolector_release(bzla, eq);

    /* assert const bits for s0 and check */
    ands0hi = boolector_bv_and(bzla, ns0, ns0hi);
    eqs     = boolector_eq(bzla, ands0hi, ns0);
    boolector_assert(bzla, eqs);
    boolector_release(bzla, eqs);
    boolector_release(bzla, ands0hi);
    ors0lo = boolector_bv_or(bzla, ns0, ns0lo);
    eqs    = boolector_eq(bzla, ors0lo, ns0);
    boolector_assert(bzla, eqs);
    boolector_release(bzla, eqs);
    boolector_release(bzla, ors0lo);
    /* assert const bits for s1 */
    ands1hi = boolector_bv_and(bzla, ns1, ns1hi);
    eqs     = boolector_eq(bzla, ands1hi, ns1);
    boolector_assert(bzla, eqs);
    boolector_release(bzla, eqs);
    ors1lo = boolector_bv_or(bzla, ns1, ns1lo);
    eqs    = boolector_eq(bzla, ors1lo, ns1);
    boolector_assert(bzla, eqs);
    boolector_release(bzla, eqs);

    status = boolector_sat(bzla);
    assert(status == BOOLECTOR_SAT || status == BOOLECTOR_UNSAT);

    boolector_release(bzla, ands1hi);
    boolector_release(bzla, ors1lo);

    boolector_release_sort(bzla, ss0);
    boolector_release_sort(bzla, ss1);
    boolector_release(bzla, exp);
    boolector_release(bzla, nx);
    boolector_release(bzla, ns0lo);
    boolector_release(bzla, ns0hi);
    boolector_release(bzla, ns1lo);
    boolector_release(bzla, ns1hi);
    boolector_release(bzla, ns0);
    boolector_release(bzla, ns1);
    boolector_release(bzla, nt);

    bzla_mem_freestr(d_mm, vx);
    bzla_mem_freestr(d_mm, vt);
    bzla_mem_freestr(d_mm, vs0lo);
    bzla_mem_freestr(d_mm, vs0hi);
    bzla_mem_freestr(d_mm, vs1lo);
    bzla_mem_freestr(d_mm, vs1hi);
    boolector_delete(bzla);
    return status == BOOLECTOR_UNSAT;
  }

  bool check_sat_is_ess_slice(BzlaBitVector *x,
                              BzlaBitVector *t,
                              uint32_t upper,
                              uint32_t lower)
  {
    BoolectorNode *nx, *nt;
    BoolectorNode *eq, *exp;
    char *vt, *vx;

    Bzla *bzla = boolector_new();

    boolector_set_opt(bzla, BZLA_OPT_INCREMENTAL, 1);

    vt = bzla_bv_to_char(d_mm, t);
    vx = bzla_bv_to_char(d_mm, x);

    nt = boolector_bv_const(bzla, vt);
    nx = boolector_bv_const(bzla, vx);

    exp = boolector_bv_slice(bzla, nx, upper, lower);
    eq  = boolector_eq(bzla, exp, nt);
    boolector_assume(bzla, eq);
    boolector_release(bzla, eq);

    int32_t status = boolector_sat(bzla);
    assert(status == BOOLECTOR_SAT || status == BOOLECTOR_UNSAT);

    boolector_release(bzla, exp);
    boolector_release(bzla, nx);
    boolector_release(bzla, nt);

    bzla_mem_freestr(d_mm, vt);
    bzla_mem_freestr(d_mm, vx);
    boolector_delete(bzla);

    return status == BOOLECTOR_UNSAT;
  }

  BzlaMemMgr *d_mm;
};

/* Test is_ess_*_const functions. */

TEST_F(TestEssUtils, is_ess_add_const)
{
  test_is_ess_binary_const(bzla_is_ess_add_const, boolector_bv_add, 0);
}

TEST_F(TestEssUtils, is_ess_and_const)
{
  test_is_ess_binary_const(bzla_is_ess_and_const, boolector_bv_and, 0);
}

TEST_F(TestEssUtils, is_ess_concat_const)
{
  test_is_ess_binary_const(bzla_is_ess_concat_const, boolector_bv_concat, 0);
  test_is_ess_binary_const(bzla_is_ess_concat_const, boolector_bv_concat, 1);
}

TEST_F(TestEssUtils, is_ess_eq_const)
{
  test_is_ess_binary_const(bzla_is_ess_eq_const, boolector_eq, 0);
}

TEST_F(TestEssUtils, is_ess_ult_const)
{
  test_is_ess_binary_const(bzla_is_ess_ult_const, boolector_bv_ult, 0);
  test_is_ess_binary_const(bzla_is_ess_ult_const, boolector_bv_ult, 1);
}

TEST_F(TestEssUtils, is_ess_slt_const)
{
  test_is_ess_binary_const(bzla_is_ess_slt_const, boolector_bv_slt, 0);
  test_is_ess_binary_const(bzla_is_ess_slt_const, boolector_bv_slt, 1);
}

TEST_F(TestEssUtils, is_ess_slice_const)
{
  test_is_ess_slice(bzla_is_ess_slice_const, true);
}

TEST_F(TestEssUtils, is_ess_sll_const)
{
  test_is_ess_binary_const(bzla_is_ess_sll_const, boolector_bv_sll, 0);
  test_is_ess_binary_const(bzla_is_ess_sll_const, boolector_bv_sll, 1);
}

TEST_F(TestEssUtils, is_ess_srl_const)
{
  test_is_ess_binary_const(bzla_is_ess_srl_const, boolector_bv_srl, 0);
  test_is_ess_binary_const(bzla_is_ess_srl_const, boolector_bv_srl, 1);
}

TEST_F(TestEssUtils, is_ess_sra_const)
{
  test_is_ess_binary_const(bzla_is_ess_sra_const, boolector_bv_sra, 0);
  test_is_ess_binary_const(bzla_is_ess_sra_const, boolector_bv_sra, 1);
}

TEST_F(TestEssUtils, is_ess_mul_const)
{
  test_is_ess_binary_const(bzla_is_ess_mul_const, boolector_bv_mul, 0);
}

TEST_F(TestEssUtils, is_ess_urem_const)
{
  test_is_ess_binary_const(bzla_is_ess_urem_const, boolector_bv_urem, 0);
  test_is_ess_binary_const(bzla_is_ess_urem_const, boolector_bv_urem, 1);
}

TEST_F(TestEssUtils, is_ess_udiv_const)
{
  test_is_ess_binary_const(bzla_is_ess_udiv_const, boolector_bv_udiv, 0);
  test_is_ess_binary_const(bzla_is_ess_udiv_const, boolector_bv_udiv, 1);
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
  test_is_ess_binary(bzla_is_ess_add, boolector_bv_add, 0);
}

TEST_F(TestEssUtils, is_ess_and)
{
  test_is_ess_binary(bzla_is_ess_and, boolector_bv_and, 0);
}

TEST_F(TestEssUtils, is_ess_concat)
{
  test_is_ess_binary(bzla_is_ess_concat, boolector_bv_concat, 0);
  test_is_ess_binary(bzla_is_ess_concat, boolector_bv_concat, 1);
}

TEST_F(TestEssUtils, is_ess_eq)
{
  test_is_ess_binary(bzla_is_ess_eq, boolector_eq, 0);
}

TEST_F(TestEssUtils, is_ess_mul)
{
  test_is_ess_binary(bzla_is_ess_mul, boolector_bv_mul, 0);
}

TEST_F(TestEssUtils, is_ess_slice)
{
  test_is_ess_slice(bzla_is_ess_slice, false);
}

TEST_F(TestEssUtils, is_ess_sll)
{
  test_is_ess_binary(bzla_is_ess_sll, boolector_bv_sll, 0);
  test_is_ess_binary(bzla_is_ess_sll, boolector_bv_sll, 1);
}

TEST_F(TestEssUtils, is_ess_srl)
{
  test_is_ess_binary(bzla_is_ess_srl, boolector_bv_srl, 0);
  test_is_ess_binary(bzla_is_ess_srl, boolector_bv_srl, 1);
}

TEST_F(TestEssUtils, is_ess_sra)
{
  test_is_ess_binary(bzla_is_ess_sra, boolector_bv_sra, 0);
  test_is_ess_binary(bzla_is_ess_sra, boolector_bv_sra, 1);
}

TEST_F(TestEssUtils, is_ess_udiv)
{
  test_is_ess_binary(bzla_is_ess_udiv, boolector_bv_udiv, 0);
  test_is_ess_binary(bzla_is_ess_udiv, boolector_bv_udiv, 1);
}

TEST_F(TestEssUtils, is_ess_ult)
{
  test_is_ess_binary(bzla_is_ess_ult, boolector_bv_ult, 0);
  test_is_ess_binary(bzla_is_ess_ult, boolector_bv_ult, 1);
}

TEST_F(TestEssUtils, is_ess_slt)
{
  test_is_ess_binary(bzla_is_ess_slt, boolector_bv_slt, 0);
  test_is_ess_binary(bzla_is_ess_slt, boolector_bv_slt, 1);
}

TEST_F(TestEssUtils, is_ess_urem)
{
  test_is_ess_binary(bzla_is_ess_urem, boolector_bv_urem, 0);
  test_is_ess_binary(bzla_is_ess_urem, boolector_bv_urem, 1);
}

TEST_F(TestEssUtils, is_ess_cond)
{
  test_is_ess_cond(0, false);
  test_is_ess_cond(1, false);
  test_is_ess_cond(2, false);
}
