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
#include "bzlaexp.h"
#include "bzlainvutils.h"
#include "bzlaproputils.h"
}

using CreateBinExpFunc   = std::add_pointer<decltype(bzla_exp_bv_and)>::type;
using CreateSliceExpFunc = std::add_pointer<decltype(bzla_exp_bv_slice)>::type;

class TestInvUtils : public TestBzla
{
 protected:
  static constexpr int32_t TEST_INVUTILS_BW = 3;

  std::vector<std::string> d_values;

  void SetUp() override
  {
    TestBzla::SetUp();
    d_mm = d_bzla->mm;
    initialize_values(TEST_INVUTILS_BW);
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

  void test_is_inv_binary_const(BzlaPropIsInvFun is_inv,
                                CreateBinExpFunc create_exp_func,
                                uint32_t pos_x)
  {
    test_is_inv_binary(is_inv, create_exp_func, pos_x, true);
  }

  void test_is_inv_binary(BzlaPropIsInvFun is_inv,
                          CreateBinExpFunc create_exp_func,
                          uint32_t pos_x,
                          bool const_bits = false)
  {
    std::vector<std::string> x_values;
    BzlaBvDomain *x;
    BzlaBitVector *s, *t;
    char *vs, *vt;
    bool res, status;

    uint32_t bw_x = TEST_INVUTILS_BW;
    uint32_t bw_s = TEST_INVUTILS_BW;
    uint32_t bw_t = TEST_INVUTILS_BW;

    if (const_bits)
    {
      x_values = d_values;
    }
    else
    {
      /* x is unconstrained (no const bits) */
      x_values.push_back("xxx");
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

    uint32_t nval_s = 1 << bw_s;
    uint32_t nval_t = 1 << bw_t;
    for (const std::string &x_value : x_values)
    {
      x = bzla_bvdomain_new_from_char(d_mm, x_value.c_str());
      for (uint32_t i = 0; i < nval_s; i++)
      {
        s  = bzla_bv_uint64_to_bv(d_mm, i, bw_s);
        vs = bzla_bv_to_char(d_mm, s);
        for (uint32_t j = 0; j < nval_t; j++)
        {
          t  = bzla_bv_uint64_to_bv(d_mm, j, bw_t);
          vt = bzla_bv_to_char(d_mm, t);

          BzlaPropInfo pi;
          memset(&pi, 0, sizeof(BzlaPropInfo));
          pi.pos_x         = pos_x;
          pi.bv[1 - pos_x] = s;
          pi.bvd[pos_x]    = x;
          pi.target_value  = t;

          res    = is_inv(d_bzla, &pi);
          status = check_sat_is_inv_binary(create_exp_func, x, t, s, pos_x);
          if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

          if (res != status)
          {
            std::cout << "pos_x: " << pos_x << std::endl;
            std::cout << "t: " << vt << std::endl;
            std::cout << "x: " << x_value << std::endl;
            std::cout << "s: " << vs << std::endl;
          }

          assert(res == status);
          ASSERT_EQ(res, status);
          bzla_bv_free(d_mm, t);
          bzla_mem_freestr(d_mm, vt);
        }
        bzla_bv_free(d_mm, s);
        bzla_mem_freestr(d_mm, vs);
      }
      bzla_bvdomain_free(d_mm, x);
    }
  }

  void test_is_inv_cond(uint32_t pos_x, bool const_bits)
  {
    std::vector<std::string> x_values;
    BzlaBvDomain *x;
    BzlaBitVector *s0, *s1, *t;
    char *vs0, *vs1, *vt;
    bool res, status;
    uint32_t bw_s0, bw_s1, bw = TEST_INVUTILS_BW;
    uint32_t nval, nval_s0, nval_s1;

    if (pos_x)
    {
      bw_s0 = 1;
      bw_s1 = bw;
      if (const_bits)
      {
        x_values = d_values;
      }
      else
      {
        x_values.push_back("xxx");
      }
    }
    else
    {
      bw_s0 = bw;
      bw_s1 = bw;
      if (const_bits)
      {
        x_values.push_back("x");
        x_values.push_back("0");
        x_values.push_back("1");
      }
      else
      {
        x_values.push_back("x");
      }
    }
    nval    = 1 << bw;
    nval_s0 = 1 << bw_s0;
    nval_s1 = 1 << bw_s1;

    for (const std::string &x_value : x_values)
    {
      x = bzla_bvdomain_new_from_char(d_mm, x_value.c_str());
      for (uint32_t i = 0; i < nval_s0; i++)
      {
        s0  = bzla_bv_uint64_to_bv(d_mm, i, bw_s0);
        vs0 = bzla_bv_to_char(d_mm, s0);
        for (uint32_t j = 0; j < nval_s1; j++)
        {
          s1  = bzla_bv_uint64_to_bv(d_mm, j, bw_s1);
          vs1 = bzla_bv_to_char(d_mm, s1);
          for (uint32_t k = 0; k < nval; k++)
          {
            t  = bzla_bv_uint64_to_bv(d_mm, k, bw);
            vt = bzla_bv_to_char(d_mm, t);

            BzlaPropInfo pi;
            memset(&pi, 0, sizeof(BzlaPropInfo));
            pi.pos_x      = pos_x;
            pi.bvd[pos_x] = x;
            if (pos_x == 0)
            {
              pi.bv[1] = s0;
              pi.bv[2] = s1;
            }
            else if (pos_x == 1)
            {
              pi.bv[0] = s0;
              pi.bv[2] = s1;
            }
            else
            {
              pi.bv[0] = s0;
              pi.bv[1] = s1;
            }
            pi.bvd[pos_x]   = x;
            pi.target_value = t;

            if (const_bits)
            {
              res = bzla_is_inv_cond_const(d_bzla, &pi);
            }
            else
            {
              res = bzla_is_inv_cond(d_bzla, &pi);
            }
            status = check_sat_is_inv_cond(x, t, s0, s1, pos_x);
            if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

            if (res != status)
            {
              std::cout << "pos_x: " << pos_x << std::endl;
              std::cout << "t: " << vt << std::endl;
              std::cout << "x: " << x_value << std::endl;
              std::cout << "s0: " << vs0 << std::endl;
              std::cout << "s1: " << vs1 << std::endl;
            }

            ASSERT_EQ(res, status);
            bzla_bv_free(d_mm, t);
            bzla_mem_freestr(d_mm, vt);
          }
          bzla_bv_free(d_mm, s1);
          bzla_mem_freestr(d_mm, vs1);
        }
        bzla_bv_free(d_mm, s0);
        bzla_mem_freestr(d_mm, vs0);
      }
      bzla_bvdomain_free(d_mm, x);
    }
  }

  void test_is_inv_slice(BzlaPropIsInvFun is_inv, bool const_bits)
  {
    std::vector<std::string> x_values;
    BzlaBvDomain *x;
    BzlaBitVector *t;
    char *vt;

    uint32_t bw_x = TEST_INVUTILS_BW;

    if (const_bits)
    {
      x_values = d_values;
    }
    else
    {
      /* x is unconstrained (no const bits) */
      x_values.push_back("xxx");
    }

    for (const std::string &x_value : x_values)
    {
      x = bzla_bvdomain_new_from_char(d_mm, x_value.c_str());
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
            pi.bvd[0]       = x;
            pi.target_value = t;

            bool res    = is_inv(d_bzla, &pi);
            bool status = check_sat_is_inv_slice(x, t, upper, lower);

            bzla_node_release(d_bzla, slice);

            if (res != status)
            {
              std::cout << "upper: " << upper << std::endl;
              std::cout << "lower: " << lower << std::endl;
              std::cout << "t: " << vt << std::endl;
              std::cout << "x: " << x_value << std::endl;
            }

            ASSERT_EQ(res, status);
            bzla_bv_free(d_mm, t);
            bzla_mem_freestr(d_mm, vt);
          }
        }
      }
      bzla_bvdomain_free(d_mm, x);
    }
  }

  bool check_sat_is_inv_binary(CreateBinExpFunc create_exp_func,
                               BzlaBvDomain *x,
                               BzlaBitVector *t,
                               BzlaBitVector *s,
                               uint32_t pos_x)
  {
    BzlaSortId sx;
    BzlaNode *nx, *nxlo, *nxhi, *ns, *nt;
    BzlaNode *andhi, *orlo, *eq, *exp;

    Bzla *bzla = bzla_new();

    bzla_opt_set(bzla, BZLA_OPT_INCREMENTAL, 1);

    sx = bzla_sort_bv(bzla, bzla_bv_get_width(x->lo));
    nx = bzla_exp_var(bzla, sx, 0);

    nxlo = bzla_exp_bv_const(bzla, x->lo);

    nxhi = bzla_exp_bv_const(bzla, x->hi);

    /* assume const bits for x */
    andhi = bzla_exp_bv_and(bzla, nx, nxhi);
    eq    = bzla_exp_eq(bzla, andhi, nx);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    orlo = bzla_exp_bv_or(bzla, nx, nxlo);
    eq   = bzla_exp_eq(bzla, orlo, nx);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    /* x <> s = t  for operator <> */

    ns = bzla_exp_bv_const(bzla, s);
    nt = bzla_exp_bv_const(bzla, t);

    if (pos_x == 0)
      exp = create_exp_func(bzla, nx, ns);
    else
    {
      assert(pos_x == 1);
      exp = create_exp_func(bzla, ns, nx);
    }

    eq = bzla_exp_eq(bzla, exp, nt);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    int32_t status = bzla_check_sat(bzla, -1, -1);
    assert(status == BZLA_RESULT_SAT || status == BZLA_RESULT_UNSAT);

    bzla_sort_release(bzla, sx);
    bzla_node_release(bzla, exp);
    bzla_node_release(bzla, nx);
    bzla_node_release(bzla, nxlo);
    bzla_node_release(bzla, nxhi);
    bzla_node_release(bzla, ns);
    bzla_node_release(bzla, nt);
    bzla_node_release(bzla, andhi);
    bzla_node_release(bzla, orlo);

    bzla_delete(bzla);

    return status == BZLA_RESULT_SAT;
  }

  bool check_sat_is_inv_cond(BzlaBvDomain *x,
                             BzlaBitVector *t,
                             BzlaBitVector *s0,
                             BzlaBitVector *s1,
                             uint32_t pos_x)
  {
    BzlaSortId sx;
    BzlaNode *nx, *nxlo, *nxhi, *ns0, *ns1, *nt;
    BzlaNode *andhi, *orlo, *eq, *exp;

    Bzla *bzla = bzla_new();

    bzla_opt_set(bzla, BZLA_OPT_INCREMENTAL, 1);

    sx = bzla_sort_bv(bzla, bzla_bv_get_width(x->lo));
    nx = bzla_exp_var(bzla, sx, 0);

    nxlo = bzla_exp_bv_const(bzla, x->lo);

    nxhi = bzla_exp_bv_const(bzla, x->hi);

    /* assume const bits for x */
    andhi = bzla_exp_bv_and(bzla, nx, nxhi);
    eq    = bzla_exp_eq(bzla, andhi, nx);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    orlo = bzla_exp_bv_or(bzla, nx, nxlo);
    eq   = bzla_exp_eq(bzla, orlo, nx);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    ns0 = bzla_exp_bv_const(bzla, s0);
    ns1 = bzla_exp_bv_const(bzla, s1);
    nt  = bzla_exp_bv_const(bzla, t);

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
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    int32_t status = bzla_check_sat(bzla, -1, -1);
    assert(status == BZLA_RESULT_SAT || status == BZLA_RESULT_UNSAT);

    bzla_sort_release(bzla, sx);
    bzla_node_release(bzla, exp);
    bzla_node_release(bzla, nx);
    bzla_node_release(bzla, nxlo);
    bzla_node_release(bzla, nxhi);
    bzla_node_release(bzla, ns0);
    bzla_node_release(bzla, ns1);
    bzla_node_release(bzla, nt);
    bzla_node_release(bzla, andhi);
    bzla_node_release(bzla, orlo);

    bzla_delete(bzla);

    return status == BZLA_RESULT_SAT;
  }

  bool check_sat_is_inv_slice(BzlaBvDomain *x,
                              BzlaBitVector *t,
                              uint32_t upper,
                              uint32_t lower)
  {
    BzlaSortId sx;
    BzlaNode *nx, *nxlo, *nxhi, *nt;
    BzlaNode *andhi, *orlo, *eq, *exp;

    Bzla *bzla = bzla_new();

    bzla_opt_set(bzla, BZLA_OPT_INCREMENTAL, 1);

    sx = bzla_sort_bv(bzla, bzla_bv_get_width(x->lo));
    nx = bzla_exp_var(bzla, sx, 0);

    nxlo = bzla_exp_bv_const(bzla, x->lo);

    nxhi = bzla_exp_bv_const(bzla, x->hi);

    /* assume const bits for x */
    andhi = bzla_exp_bv_and(bzla, nx, nxhi);
    eq    = bzla_exp_eq(bzla, andhi, nx);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    orlo = bzla_exp_bv_or(bzla, nx, nxlo);
    eq   = bzla_exp_eq(bzla, orlo, nx);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    /* x <> s = t  for operator <> */

    nt = bzla_exp_bv_const(bzla, t);

    exp = bzla_exp_bv_slice(bzla, nx, upper, lower);
    eq  = bzla_exp_eq(bzla, exp, nt);
    bzla_assume_exp(bzla, eq);
    bzla_node_release(bzla, eq);

    int32_t status = bzla_check_sat(bzla, -1, -1);
    assert(status == BZLA_RESULT_SAT || status == BZLA_RESULT_UNSAT);

    bzla_sort_release(bzla, sx);
    bzla_node_release(bzla, exp);
    bzla_node_release(bzla, nx);
    bzla_node_release(bzla, nxlo);
    bzla_node_release(bzla, nxhi);
    bzla_node_release(bzla, nt);
    bzla_node_release(bzla, andhi);
    bzla_node_release(bzla, orlo);

    bzla_delete(bzla);

    return status == BZLA_RESULT_SAT;
  }

  BzlaMemMgr *d_mm;
};

/* Test is_inv_*_const functions. */

TEST_F(TestInvUtils, is_inv_add_const)
{
  test_is_inv_binary_const(bzla_is_inv_add_const, bzla_exp_bv_add, 0);
}

TEST_F(TestInvUtils, is_inv_and_const)
{
  test_is_inv_binary_const(bzla_is_inv_and_const, bzla_exp_bv_and, 0);
}

TEST_F(TestInvUtils, is_inv_xor_const)
{
  test_is_inv_binary_const(bzla_is_inv_xor_const, bzla_exp_bv_xor, 0);
}

TEST_F(TestInvUtils, is_inv_concat_const)
{
  test_is_inv_binary_const(bzla_is_inv_concat_const, bzla_exp_bv_concat, 0);
  test_is_inv_binary_const(bzla_is_inv_concat_const, bzla_exp_bv_concat, 1);
}

TEST_F(TestInvUtils, is_inv_eq_const)
{
  test_is_inv_binary_const(bzla_is_inv_eq_const, bzla_exp_eq, 0);
}

TEST_F(TestInvUtils, is_inv_ult_const)
{
  test_is_inv_binary_const(bzla_is_inv_ult_const, bzla_exp_bv_ult, 0);
  test_is_inv_binary_const(bzla_is_inv_ult_const, bzla_exp_bv_ult, 1);
}

TEST_F(TestInvUtils, is_inv_slt_const)
{
  test_is_inv_binary_const(bzla_is_inv_slt_const, bzla_exp_bv_slt, 0);
  test_is_inv_binary_const(bzla_is_inv_slt_const, bzla_exp_bv_slt, 1);
}

TEST_F(TestInvUtils, is_inv_slice_const)
{
  test_is_inv_slice(bzla_is_inv_slice_const, true);
}

TEST_F(TestInvUtils, is_inv_sll_const)
{
  test_is_inv_binary_const(bzla_is_inv_sll_const, bzla_exp_bv_sll, 0);
  test_is_inv_binary_const(bzla_is_inv_sll_const, bzla_exp_bv_sll, 1);
}

TEST_F(TestInvUtils, is_inv_srl_const)
{
  test_is_inv_binary_const(bzla_is_inv_srl_const, bzla_exp_bv_srl, 0);
  test_is_inv_binary_const(bzla_is_inv_srl_const, bzla_exp_bv_srl, 1);
}

TEST_F(TestInvUtils, is_inv_sra_const)
{
  test_is_inv_binary_const(bzla_is_inv_sra_const, bzla_exp_bv_sra, 0);
  test_is_inv_binary_const(bzla_is_inv_sra_const, bzla_exp_bv_sra, 1);
}

TEST_F(TestInvUtils, is_inv_mul_const)
{
  test_is_inv_binary_const(bzla_is_inv_mul_const, bzla_exp_bv_mul, 0);
}

TEST_F(TestInvUtils, is_inv_urem_const)
{
  test_is_inv_binary_const(bzla_is_inv_urem_const, bzla_exp_bv_urem, 0);
  test_is_inv_binary_const(bzla_is_inv_urem_const, bzla_exp_bv_urem, 1);
}

TEST_F(TestInvUtils, is_inv_udiv_const)
{
  test_is_inv_binary_const(bzla_is_inv_udiv_const, bzla_exp_bv_udiv, 0);
  test_is_inv_binary_const(bzla_is_inv_udiv_const, bzla_exp_bv_udiv, 1);
}

TEST_F(TestInvUtils, is_inv_cond_const)
{
  test_is_inv_cond(0, true);
  test_is_inv_cond(1, true);
  test_is_inv_cond(2, true);
}

/* Test is_inv_* functions (no const bits). */

TEST_F(TestInvUtils, is_inv_add)
{
  test_is_inv_binary(bzla_is_inv_add, bzla_exp_bv_add, 0);
}

TEST_F(TestInvUtils, is_inv_and)
{
  test_is_inv_binary(bzla_is_inv_and, bzla_exp_bv_and, 0);
}

TEST_F(TestInvUtils, is_inv_xor)
{
  test_is_inv_binary(bzla_is_inv_xor, bzla_exp_bv_xor, 0);
}

TEST_F(TestInvUtils, is_inv_concat)
{
  test_is_inv_binary(bzla_is_inv_concat, bzla_exp_bv_concat, 0);
  test_is_inv_binary(bzla_is_inv_concat, bzla_exp_bv_concat, 1);
}

TEST_F(TestInvUtils, is_inv_eq)
{
  test_is_inv_binary(bzla_is_inv_eq, bzla_exp_eq, 0);
}

TEST_F(TestInvUtils, is_inv_mul)
{
  test_is_inv_binary(bzla_is_inv_mul, bzla_exp_bv_mul, 0);
}

TEST_F(TestInvUtils, is_inv_slice)
{
  test_is_inv_slice(bzla_is_inv_slice, false);
}

TEST_F(TestInvUtils, is_inv_sll)
{
  test_is_inv_binary(bzla_is_inv_sll, bzla_exp_bv_sll, 0);
  test_is_inv_binary(bzla_is_inv_sll, bzla_exp_bv_sll, 1);
}

TEST_F(TestInvUtils, is_inv_srl)
{
  test_is_inv_binary(bzla_is_inv_srl, bzla_exp_bv_srl, 0);
  test_is_inv_binary(bzla_is_inv_srl, bzla_exp_bv_srl, 1);
}

TEST_F(TestInvUtils, is_inv_sra)
{
  test_is_inv_binary(bzla_is_inv_sra, bzla_exp_bv_sra, 0);
  test_is_inv_binary(bzla_is_inv_sra, bzla_exp_bv_sra, 1);
}

TEST_F(TestInvUtils, is_inv_udiv)
{
  test_is_inv_binary(bzla_is_inv_udiv, bzla_exp_bv_udiv, 0);
  test_is_inv_binary(bzla_is_inv_udiv, bzla_exp_bv_udiv, 1);
}

TEST_F(TestInvUtils, is_inv_ult)
{
  test_is_inv_binary(bzla_is_inv_ult, bzla_exp_bv_ult, 0);
  test_is_inv_binary(bzla_is_inv_ult, bzla_exp_bv_ult, 1);
}

TEST_F(TestInvUtils, is_inv_slt)
{
  test_is_inv_binary(bzla_is_inv_slt, bzla_exp_bv_slt, 0);
  test_is_inv_binary(bzla_is_inv_slt, bzla_exp_bv_slt, 1);
}

TEST_F(TestInvUtils, is_inv_urem)
{
  test_is_inv_binary(bzla_is_inv_urem, bzla_exp_bv_urem, 0);
  test_is_inv_binary(bzla_is_inv_urem, bzla_exp_bv_urem, 1);
}

TEST_F(TestInvUtils, is_inv_cond)
{
  test_is_inv_cond(0, false);
  test_is_inv_cond(1, false);
  test_is_inv_cond(2, false);
}
