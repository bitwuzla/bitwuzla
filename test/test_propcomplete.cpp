/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#include "test.h"

extern "C" {
#include "bzlabv.h"
#include "bzlabvprop.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlainvutils.h"
#include "bzlanode.h"
#include "bzlaproputils.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "utils/bzlautil.h"
}

class TestPropComplete : public TestBzla
{
 protected:
  static constexpr uint32_t TEST_PROP_INV_COMPLETE_BW      = 4u;
  static constexpr uint64_t TEST_PROP_INV_COMPLETE_N_TESTS = 1000u;

  void SetUp() override
  {
    TestBzla::SetUp();

    d_bzla->slv       = bzla_new_prop_solver(d_bzla);
    d_bzla->slv->bzla = d_bzla;
    d_mm              = d_bzla->mm;
    d_rng             = d_bzla->rng;
    d_domains         = BZLA_PROP_SOLVER(d_bzla)->domains;

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    bzla_opt_set(d_bzla, BZLA_OPT_RW_LEVEL, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_RW_SORT_EXP, 0);
    // we configure everything needed for const bits tests manually
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_CONST_BITS, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_EQ_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_AND_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_ASHR, 1);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_XOR, 1);

    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_generate(d_bzla, d_bzla->bv_model, d_bzla->fun_model, 0);
  }

  void clear_domains()
  {
    BzlaIntHashTableIterator iit;
    bzla_iter_hashint_init(&iit, d_domains);
    while (bzla_iter_hashint_has_next(&iit))
    {
      int32_t key = bzla_iter_hashint_next(&iit);
      bzla_bvdomain_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_hashint_map_get(d_domains, key)->as_ptr));
      bzla_hashint_map_remove(d_domains, key, 0);
    }
    assert(d_domains->count == 0);
  }

  void init_prop_info(BzlaPropInfo *pi,
                      BzlaNode *exp,
                      int32_t pos_x,
                      BzlaBitVector *t,
                      BzlaBitVector *s0,
                      BzlaBitVector *s1,
                      BzlaBitVector *s2,
                      BzlaBvDomain *d0,
                      BzlaBvDomain *d1,
                      BzlaBvDomain *d2)
  {
    pi->exp          = exp;
    pi->pos_x        = pos_x;
    pi->target_value = t;
    pi->bv[0]        = s0;
    pi->bv[1]        = s1;
    pi->bv[2]        = s2;
    pi->bvd[0]       = d0;
    pi->bvd[1]       = d1;
    pi->bvd[2]       = d2;
    pi->res_x        = 0;
  }

  /**
   * Check the result of a previous inverse value computation. Given 's'
   * (the assignment of the other operand) and 't' (the target value of the
   * operation) we expect that we determine an inverse value 'x_bv' for the
   * operand at index 'idx_x'.
   *
   * We use this to check that a value 's' that was previously determined as
   * the inverse value for an operation given 't' and 'x_bv', produces 'x_bv'
   * as inverse value, i.e., we essentially reverse the inverse value
   * computation with respect to the operands.
   *
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to s and t.
   * val_fun   : The function to compute the value for x given s and t.
   * pi        : The struct containing all information needed for is_inv checks
   *             and invers/consistent value computation.
   */
  void check_result(BzlaPropIsInvFun is_inv_fun,
                    BzlaPropComputeValueFun val_fun,
                    BzlaPropInfo *pi)
  {
    assert(val_fun);
    assert(pi);
    assert(d_domains);

    uint64_t k;
    uint32_t idx_x;
    BzlaBitVector *res;
    const BzlaBitVector *s, *t, *x_bv;

    /* the index of x, the operand we solve for */
    idx_x = pi->pos_x;
    /* the assignment of the other operand */
    s = pi->bv[idx_x ? 0 : 1];
    /* the target value */
    t = pi->target_value;
    /* the expected assignment of x */
    x_bv = pi->bv[idx_x];

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      pi->res_x = 0;
      if (is_inv_fun)
      {
        ASSERT_TRUE(is_inv_fun(d_bzla, pi));
      }
      res = val_fun(d_bzla, pi);
      ASSERT_NE(res, nullptr);
      if (pi->res_x) bzla_bvdomain_free(d_mm, pi->res_x);
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    if (!res)
    {
      std::cout << "x: ";
      bzla_bv_print(x_bv);
      std::cout << "t: ";
      bzla_bv_print(t);
      std::cout << "s: ";
      bzla_bv_print(s);
      std::cout << "idx_x: " << idx_x << std::endl;
    }
    ASSERT_NE(res, nullptr);
    ASSERT_EQ(bzla_bv_compare(res, x_bv), 0);
    bzla_bv_free(d_mm, res);
  }

  /**
   * Same as check_result but for cond.
   *
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to s0, s1 and t.
   * val_fun   : The function to compute the value for x given s0, s1 and t.
   * pi        : The struct containing all information needed for is_inv checks
   *             and invers/consistent value computation.
   */
  void check_result_cond(BzlaPropIsInvFun is_inv_fun,
                         BzlaPropComputeValueFun val_fun,
                         BzlaPropInfo *pi)
  {
    assert(val_fun);
    assert(pi);
    assert(d_domains);

    uint32_t idx_x;
    uint64_t k;
    BzlaBitVector *res, *tmp;
    const BzlaBitVector *x_bv, *s0, *s1, *t;

    /* the index of x, the operand we solve for */
    idx_x = pi->pos_x;
    /* the assignment of the other operands */
    s0 = pi->bv[idx_x == 0 ? 1 : 0];
    s1 = pi->bv[idx_x == 2 ? 1 : 2];
    /* the target value */
    t = pi->target_value;
    /* the expected assignment of x */
    x_bv = pi->bv[pi->pos_x];

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      pi->res_x = 0;
      if (is_inv_fun)
      {
        ASSERT_TRUE(is_inv_fun(d_bzla, pi));
      }
      res = val_fun(d_bzla, pi);
      if (pi->res_x) bzla_bvdomain_free(d_mm, pi->res_x);
      ASSERT_NE(res, nullptr);
      if ((idx_x == 1 && bzla_bv_is_zero(s0))
          || (idx_x == 2 && bzla_bv_is_one(s0)))
      {
        /* In case of cond, the implementation is not complete on purpose:
         * We don't care about disabled branches, and will never produce all
         * possible values for them. */
        break;
      }
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    if (!res)
    {
      std::cout << "x: ";
      bzla_bv_print(x_bv);
      std::cout << "t: ";
      bzla_bv_print(t);
      std::cout << "s0: ";
      bzla_bv_print(s0);
      std::cout << "s1: ";
      bzla_bv_print(s1);
      std::cout << "idx_x: " << idx_x << std::endl;
    }
    ASSERT_NE(res, nullptr);
    tmp = bzla_bv_ite(d_mm,
                      idx_x == 0 ? res : pi->bv[0],
                      idx_x == 1 ? res : pi->bv[1],
                      idx_x == 2 ? res : pi->bv[2]);
    ASSERT_EQ(bzla_bv_compare(tmp, t), 0);
    bzla_bv_free(d_mm, tmp);
    bzla_bv_free(d_mm, res);
  }

  /**
   * Test if for a binary operation s0 <> s1 = t, the inverse value computation
   * for the first operand produces value s0, and the inverse value computation
   * for the second operand produces value s1.
   *
   * exp_fun   : The function to create the node representing operation <>.
   * bv_fun    : The function to create the bit-vector result of operation
   *             s0 <> s1.
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to s and t.
   * val_fun   : The function to compute the value for x given s and t.
   */
  void check_binary(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                    BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                             const BzlaBitVector *,
                                             const BzlaBitVector *),
                    BzlaPropIsInvFun is_inv_fun,
                    BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *t;
    BzlaPropInfo pi;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = exp_fun(d_bzla, e[0], e[1]);

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        t    = bv_fun(d_mm, s[0], s[1]);
        init_prop_info(&pi, exp, 0, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        init_prop_info(&pi, exp, 1, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }

  /** Same as check_binary but for cond.  */
  void check_cond(BzlaPropIsInvFun is_inv_fun, BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j, k;
    BzlaNode *exp, *e[3];
    BzlaSortId sort, sort1;
    BzlaBitVector *s[3], *t;
    BzlaPropInfo pi;

    bw    = TEST_PROP_INV_COMPLETE_BW;
    sort  = bzla_sort_bv(d_bzla, bw);
    sort1 = bzla_sort_bv(d_bzla, 1);
    e[0]  = bzla_exp_var(d_bzla, sort1, 0);
    e[1]  = bzla_exp_var(d_bzla, sort, 0);
    e[2]  = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    bzla_sort_release(d_bzla, sort1);
    exp = bzla_exp_cond(d_bzla, e[0], e[1], e[2]);

    for (i = 0; i < (uint32_t)(1 << 1); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, 1);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        for (k = 0; k < (uint32_t)(1 << bw); k++)
        {
          s[2] = bzla_bv_uint64_to_bv(d_mm, k, bw);
          t    = bzla_bv_ite(d_mm, s[0], s[1], s[2]);
          init_prop_info(&pi, exp, 0, t, s[0], s[1], s[2], 0, 0, 0);
          check_result_cond(is_inv_fun, val_fun, &pi);
          init_prop_info(&pi, exp, 1, t, s[0], s[1], s[2], 0, 0, 0);
          check_result_cond(is_inv_fun, val_fun, &pi);
          init_prop_info(&pi, exp, 2, t, s[0], s[1], s[2], 0, 0, 0);
          check_result_cond(is_inv_fun, val_fun, &pi);
          bzla_bv_free(d_mm, s[2]);
          bzla_bv_free(d_mm, t);
        }
        bzla_bv_free(d_mm, s[1]);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, e[2]);
    bzla_node_release(d_bzla, exp);
  }

  /** Same as check_binary but for slice.  */
  void check_slice(BzlaPropIsInvFun is_inv_fun, BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t up, lo, i, k;
    BzlaNode *exp, *e;
    BzlaBitVector *t, *x, *res;
    BzlaSortId sort;
    BzlaPropInfo pi;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e    = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);

    for (lo = 0; lo < bw; lo++)
    {
      for (up = lo; up < bw; up++)
      {
        exp = bzla_exp_bv_slice(d_bzla, e, up, lo);
        for (i = 0; i < (uint32_t)(1 << bw); i++)
        {
          x = bzla_bv_uint64_to_bv(d_mm, i, bw);
          t = bzla_bv_slice(d_mm, x, up, lo);
          init_prop_info(&pi, exp, 0, t, x, 0, 0, 0, 0, 0);
          /* test and check result */
          for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
          {
            pi.res_x = 0;
            if (is_inv_fun)
            {
              assert(is_inv_fun(d_bzla, &pi));
            }
            res = val_fun(d_bzla, &pi);
            ASSERT_NE(res, nullptr);
            if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
            if (!bzla_bv_compare(res, x)) break;
            bzla_bv_free(d_mm, res);
            res = 0;
          }
          ASSERT_NE(res, nullptr);
          ASSERT_EQ(bzla_bv_compare(res, x), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, x);
          bzla_bv_free(d_mm, t);
        }
        bzla_node_release(d_bzla, exp);
      }
    }
    bzla_node_release(d_bzla, e);
  }

  /**
   * Test if for a shift operation s0 <> s1 = t, the inverse value computation
   * for the first operand produces value s0, and the inverse value computation
   * for the second operand produces value s1.
   *
   * exp_fun      : The function to create the node representing operation <>.
   * bv_fun       : The function to create the bit-vector result of operation
   *                s0 <> s1.
   * is_inv_fun   : The function to test if given operator is invertible with
   *                respect to s and t.
   * val_fun      : The function to compute the value for x given s and t.
   */
  void check_shift(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                   BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                            const BzlaBitVector *,
                                            const BzlaBitVector *),
                   BzlaPropIsInvFun is_inv_fun,
                   BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *t;
    BzlaPropInfo pi;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = exp_fun(d_bzla, e[0], e[1]);

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        t    = bv_fun(d_mm, s[0], s[1]);
        init_prop_info(&pi, exp, 0, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        init_prop_info(&pi, exp, 1, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }

  void check_inv_lt_sext(uint32_t bw    = TEST_PROP_INV_COMPLETE_BW,
                         bool is_signed = false)
  {
    uint64_t i, j;
    uint32_t pos_x, nsext;
    BzlaNode *exp, *v, *e[2];
    BzlaBitVector *s[2], *t, *bv_sext;
    BzlaPropInfo pi;
    BzlaSortId sort_v, sort;
    BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *);
    BzlaBitVector *(*bv_fun)(
        BzlaMemMgr *, const BzlaBitVector *, const BzlaBitVector *);
    BzlaPropIsInvFun is_inv_fun;
    BzlaPropComputeValueFun val_fun;

    nsext = bw > 3 ? 2 : 1;
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT, 1);

    if (is_signed)
    {
      bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
      exp_fun    = bzla_exp_bv_slt;
      bv_fun     = bzla_bv_slt;
      is_inv_fun = bzla_is_inv_slt;
      val_fun    = bzla_proputils_inv_slt;
    }
    else
    {
      exp_fun    = bzla_exp_bv_ult;
      bv_fun     = bzla_bv_ult;
      is_inv_fun = bzla_is_inv_ult;
      val_fun    = bzla_proputils_inv_ult;
    }

    /* Disable rewriting in order to preserve sign extension structure. */
    bzla_opt_set(d_bzla, BZLA_OPT_RW_LEVEL, 0);

    sort_v = bzla_sort_bv(d_bzla, bw - nsext);
    sort   = bzla_sort_bv(d_bzla, bw);
    v      = bzla_exp_var(d_bzla, sort_v, 0);

    for (pos_x = 0; pos_x < 2; ++pos_x)
    {
      e[1 - pos_x] = bzla_exp_var(d_bzla, sort, 0);
      e[pos_x]     = bzla_exp_bv_sext(d_bzla, v, nsext);
      exp          = exp_fun(d_bzla, e[0], e[1]);
      bzla_node_release(d_bzla, e[0]);
      bzla_node_release(d_bzla, e[1]);

      for (i = 0; i < (uint32_t)(1 << (bw - nsext)); i++)
      {
        bv_sext  = bzla_bv_uint64_to_bv(d_mm, i, bw - nsext);
        s[pos_x] = bzla_bv_sext(d_mm, bv_sext, nsext);
        for (j = 0; j < (uint32_t)(1 << bw); j++)
        {
          s[1 - pos_x] = bzla_bv_uint64_to_bv(d_mm, j, bw);
          t            = bv_fun(d_mm, s[0], s[1]);

          /* domains are initialized later */
          init_prop_info(&pi, exp, pos_x, t, s[0], s[1], 0, 0, 0, 0);
          check_result(is_inv_fun, val_fun, &pi);

          bzla_bv_free(d_mm, s[1 - pos_x]);
          bzla_bv_free(d_mm, t);
        }
        bzla_bv_free(d_mm, s[pos_x]);
        bzla_bv_free(d_mm, bv_sext);
      }

      bzla_node_release(d_bzla, exp);
    }

    bzla_node_release(d_bzla, v);
    bzla_sort_release(d_bzla, sort_v);
    bzla_sort_release(d_bzla, sort);
  }

  void check_inv_lt_concat(uint32_t bw    = TEST_PROP_INV_COMPLETE_BW,
                           bool is_signed = false)
  {
    uint64_t i, j;
    uint32_t pos_x, bw_v0;
    BzlaNode *exp, *v0, *v1, *e[2];
    BzlaBitVector *s[2], *t;
    BzlaPropInfo pi;
    BzlaSortId sort_v0, sort_v1, sort;
    BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *);
    BzlaBitVector *(*bv_fun)(
        BzlaMemMgr *, const BzlaBitVector *, const BzlaBitVector *);
    BzlaPropIsInvFun is_inv_fun;
    BzlaPropComputeValueFun val_fun;

    bw_v0 = bw / 2;
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT, 1);

    if (is_signed)
    {
      bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
      exp_fun    = bzla_exp_bv_slt;
      bv_fun     = bzla_bv_slt;
      is_inv_fun = bzla_is_inv_slt;
      val_fun    = bzla_proputils_inv_slt;
    }
    else
    {
      exp_fun    = bzla_exp_bv_ult;
      bv_fun     = bzla_bv_ult;
      is_inv_fun = bzla_is_inv_ult;
      val_fun    = bzla_proputils_inv_ult;
    }

    /* Disable rewriting in order to preserve sign extension structure. */
    bzla_opt_set(d_bzla, BZLA_OPT_RW_LEVEL, 0);

    sort_v0 = bzla_sort_bv(d_bzla, bw_v0);
    sort_v1 = bzla_sort_bv(d_bzla, bw - bw_v0);
    sort    = bzla_sort_bv(d_bzla, bw);
    v0      = bzla_exp_var(d_bzla, sort_v0, 0);
    v1      = bzla_exp_var(d_bzla, sort_v1, 0);

    for (pos_x = 0; pos_x < 2; ++pos_x)
    {
      e[1 - pos_x] = bzla_exp_var(d_bzla, sort, 0);
      e[pos_x]     = bzla_exp_bv_concat(d_bzla, v0, v1);
      exp          = exp_fun(d_bzla, e[0], e[1]);
      bzla_node_release(d_bzla, e[0]);
      bzla_node_release(d_bzla, e[1]);

      for (i = 0; i < (uint32_t)(1 << bw); i++)
      {
        s[pos_x] = bzla_bv_uint64_to_bv(d_mm, i, bw);
        for (j = 0; j < (uint32_t)(1 << bw); j++)
        {
          s[1 - pos_x] = bzla_bv_uint64_to_bv(d_mm, j, bw);
          t            = bv_fun(d_mm, s[0], s[1]);

          /* domains are initialized later */
          init_prop_info(&pi, exp, pos_x, t, s[0], s[1], 0, 0, 0, 0);
          check_result(is_inv_fun, val_fun, &pi);

          bzla_bv_free(d_mm, s[1 - pos_x]);
          bzla_bv_free(d_mm, t);
        }
        bzla_bv_free(d_mm, s[pos_x]);
      }

      bzla_node_release(d_bzla, exp);
    }

    bzla_node_release(d_bzla, v0);
    bzla_node_release(d_bzla, v1);
    bzla_sort_release(d_bzla, sort_v0);
    bzla_sort_release(d_bzla, sort_v1);
    bzla_sort_release(d_bzla, sort);
  }

  /**
   * Test if for x & s = t and s & x = t, the consistent value and inverse value
   * computation always produces t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t const bits.
   */
  void check_conf_and(uint32_t bw, bool use_domains)
  {
    (void) bw;
    uint64_t i, j;
    BzlaNode *exp, *cexp[2], *e[2], *ce[2];
    BzlaSortId sort;
    BzlaBitVector *t, *s[2], *res, *tmp, *tmp2;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = bzla_exp_bv_and(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_and_const;
      cons_fun   = bzla_proputils_cons_and_const;
      bzla_synthesize_exp(d_bzla, exp, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }
    else
    {
      is_inv_fun = bzla_is_inv_and;
      cons_fun   = bzla_proputils_cons_and;
    }

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0]    = bzla_bv_uint64_to_bv(d_mm, i, bw);
      s[1]    = bzla_bv_uint64_to_bv(d_mm, i, bw);
      ce[0]   = bzla_exp_bv_const(d_bzla, s[0]);
      ce[1]   = bzla_exp_bv_const(d_bzla, s[1]);
      cexp[0] = bzla_exp_bv_and(d_bzla, ce[0], e[1]);
      cexp[1] = bzla_exp_bv_and(d_bzla, e[0], ce[1]);

      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        t   = bzla_bv_uint64_to_bv(d_mm, j, bw);
        tmp = bzla_bv_and(d_mm, s[0], t);
        slv = 0;
        if (bzla_bv_compare(tmp, t))
        {
        PROP_COMPLETE_CONF_AND_TESTS:
          /* prop engine: all conflicts are treated as fixable */

          /* idx_x = 0 */
          init_prop_info(&pi, exp, 0, t, s[0], s[1], 0, x0, x1, 0);
          ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
          res = cons_fun(d_bzla, &pi);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, t, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, t), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);
          if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

          init_prop_info(&pi, cexp[1], 0, t, s[0], s[1], 0, x0, x1, 0);
          ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
          res = cons_fun(d_bzla, &pi);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, t, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, t), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);
          if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

          /* idx_x = 1 */
          init_prop_info(&pi, exp, 1, t, s[0], s[1], 0, x0, x1, 0);
          ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
          res = cons_fun(d_bzla, &pi);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, t, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, t), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);
          if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

          init_prop_info(&pi, cexp[0], 1, t, s[0], s[1], 0, x0, x1, 0);
          ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
          res = cons_fun(d_bzla, &pi);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, t, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, t), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);
          if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

          if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS)
            goto DONE;

          /* sls engine: only fixable if non-const inputs */
          slv         = d_bzla->slv;
          d_bzla->slv = bzla_new_sls_solver(d_bzla);
          bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

          goto PROP_COMPLETE_CONF_AND_TESTS;
        DONE:
          assert(slv);
          bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
          d_bzla->slv->api.delet(d_bzla->slv);
          d_bzla->slv = slv;
        }
        bzla_bv_free(d_mm, t);
        bzla_bv_free(d_mm, tmp);
      }
      bzla_node_release(d_bzla, cexp[0]);
      bzla_node_release(d_bzla, cexp[1]);
      bzla_node_release(d_bzla, ce[0]);
      bzla_node_release(d_bzla, ce[1]);
      bzla_bv_free(d_mm, s[0]);
      bzla_bv_free(d_mm, s[1]);
    }

    clear_domains();

    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Test if for x < s = t and s < x = t (unsigned), the consistent value and
   * inverse value computation always produces t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_ult(uint32_t bw, bool use_domains)
  {
    (void) bw;
    BzlaNode *exp, *e[2], *cexp, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *t, *s, *zero, *bvmax;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = bzla_exp_bv_ult(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_ult_const;
      cons_fun   = bzla_proputils_cons_ult_const;
      bzla_synthesize_exp(d_bzla, exp, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }
    else
    {
      is_inv_fun = bzla_is_inv_ult;
      cons_fun   = bzla_proputils_cons_ult;
    }

    zero  = bzla_bv_zero(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);
    t     = bzla_bv_one(d_mm, 1);

    /* prop engine: all conflicts are treated as fixable */

    slv = 0;
  PROP_COMPLETE_CONF_ULT_TESTS:
    /* 1...1 < e[1] */
    s = bzla_bv_ones(d_mm, bw);
    init_prop_info(&pi, exp, 1, t, s, 0, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_compare(res, zero), 0);
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    ce   = bzla_exp_bv_const(d_bzla, s);
    cexp = bzla_exp_bv_ult(d_bzla, ce, e[1]);
    init_prop_info(&pi, cexp, 1, t, s, 0, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_compare(res, zero), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cexp);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, s);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    /* e[0] < 0 */
    s = bzla_bv_zero(d_mm, bw);
    init_prop_info(&pi, exp, 0, t, 0, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_compare(res, bvmax), 0);
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    ce   = bzla_exp_bv_const(d_bzla, s);
    cexp = bzla_exp_bv_ult(d_bzla, e[0], ce);
    init_prop_info(&pi, cexp, 0, t, 0, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_compare(res, bvmax), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cexp);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, s);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_COMPLETE_CONF_ULT_TESTS;

  DONE:
    assert(slv);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    clear_domains();

    bzla_bv_free(d_mm, t);
    bzla_bv_free(d_mm, zero);
    bzla_bv_free(d_mm, bvmax);

    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Test if for x < s = t and s < x = t (signed), the consistent value and
   * inverse value computation always produces t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_slt(uint32_t bw, bool use_domains)
  {
    (void) bw;
    BzlaNode *exp, *e[2], *cexp, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *t, *s, *min_signed, *max_signed;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = bzla_exp_bv_slt(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_slt_const;
      cons_fun   = bzla_proputils_cons_slt_const;
      bzla_synthesize_exp(d_bzla, exp, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }
    else
    {
      is_inv_fun = bzla_is_inv_slt;
      cons_fun   = bzla_proputils_cons_slt;
    }

    min_signed = bzla_bv_min_signed(d_mm, bw);
    max_signed = bzla_bv_max_signed(d_mm, bw);
    t          = bzla_bv_one(d_mm, 1);

    /* prop engine: all conflicts are treated as fixable */

    slv = 0;
  PROP_COMPLETE_CONF_SLT_TESTS:
    /* 1...1 < e[1] */
    s = bzla_bv_max_signed(d_mm, bw);
    init_prop_info(&pi, exp, 1, t, s, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    assert(bzla_bv_signed_compare(res, min_signed) > 0);
    ASSERT_GT(bzla_bv_signed_compare(res, min_signed), 0);
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    ce   = bzla_exp_bv_const(d_bzla, s);
    cexp = bzla_exp_bv_slt(d_bzla, ce, e[1]);
    init_prop_info(&pi, cexp, 1, t, s, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_signed_compare(res, min_signed), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cexp);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, s);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    /* e[0] < min_signed */
    s = bzla_bv_min_signed(d_mm, bw);
    init_prop_info(&pi, exp, 0, t, s, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    assert(bzla_bv_signed_compare(res, max_signed) < 0);
    ASSERT_LT(bzla_bv_signed_compare(res, max_signed), 0);
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    ce   = bzla_exp_bv_const(d_bzla, s);
    cexp = bzla_exp_bv_slt(d_bzla, e[0], ce);
    init_prop_info(&pi, cexp, 0, t, s, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_signed_compare(res, max_signed), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cexp);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, s);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_COMPLETE_CONF_SLT_TESTS;

  DONE:
    assert(slv);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    clear_domains();

    bzla_bv_free(d_mm, t);
    bzla_bv_free(d_mm, min_signed);
    bzla_bv_free(d_mm, max_signed);

    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Test if for x << s = t and s << x = t, the consistent value and inverse
   * value computation always produces a value t when solved for x where the
   * shifted bits match the corresponding bits in the shifted operand.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_sll(uint32_t bw, bool use_domains)
  {
    (void) bw;
    BzlaNode *sll, *e[2];
    BzlaSortId sort;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    sll = bzla_exp_bv_sll(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      bzla_synthesize_exp(d_bzla, sll, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, sll);
    }

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_SLL_TESTS:
    /* s << e[1] = bvsll */

    /* -> shifted bits must match */
    switch (bw)
    {
      case 2:
        check_conf_shift(1, sll, "sll", "00", "01", 0, use_domains);
        check_conf_shift(1, sll, "sll", "00", "10", 1, use_domains);
        check_conf_shift(1, sll, "sll", "00", "11", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "01", "11", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "10", "01", 0, use_domains);
        check_conf_shift(1, sll, "sll", "10", "11", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "11", "01", 0, use_domains);
        break;

      case 4:
        check_conf_shift(1, sll, "sll", "0000", "0010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "0000", "1000", 3, use_domains);
        check_conf_shift(1, sll, "sll", "0000", "0110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "0000", "1110", 1, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "0001", "0110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "0001", "1100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "0001", "1010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "0001", "1110", 1, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "1000", "0110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1000", "1100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "1000", "1010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1000", "1110", 1, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "1010", "0110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1010", "1100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "1010", "1110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1010", "1111", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "0110", "0111", 0, use_domains);
        check_conf_shift(1, sll, "sll", "0110", "0010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "0110", "1010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "0110", "1111", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "1111", "1010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1111", "0110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1111", "0010", 1, use_domains);
        check_conf_shift(1, sll, "sll", "1111", "0011", 0, use_domains);
        break;

      case 8:
        check_conf_shift(1, sll, "sll", "00000000", "11111110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "00000000", "10101010", 1, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "00000100", "00111100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "00000100", "11110000", 4, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "00100000", "11001100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "00100000", "01000010", 1, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "01010101", "10101110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "01010101", "10100100", 2, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "11111110", "10111100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "11111110", "11111101", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "01111111", "10111100", 2, use_domains);
        check_conf_shift(1, sll, "sll", "01111111", "11111101", 0, use_domains);
        ///
        check_conf_shift(1, sll, "sll", "11111111", "10111110", 1, use_domains);
        check_conf_shift(1, sll, "sll", "11111111", "11111101", 0, use_domains);
        break;

      default: break;
    }

    /* e[0] << s = bvsll
     * -> LSBs shifted must be zero */
    switch (bw)
    {
      case 2:
        check_conf_shift(0, sll, "sll", "01", "01", 0, use_domains);
        check_conf_shift(0, sll, "sll", "01", "11", 0, use_domains);
        break;
      case 4:
        check_conf_shift(0, sll, "sll", "0001", "0001", 0, use_domains);
        check_conf_shift(0, sll, "sll", "0010", "0110", 0, use_domains);
        check_conf_shift(0, sll, "sll", "0011", "1100", 0, use_domains);
        break;
      case 8:
        check_conf_shift(0, sll, "sll", "00000001", "00000011", 0, use_domains);
        check_conf_shift(0, sll, "sll", "00000010", "00001110", 0, use_domains);
        check_conf_shift(0, sll, "sll", "00000011", "00001100", 0, use_domains);
        check_conf_shift(0, sll, "sll", "00000100", "11111100", 0, use_domains);
        check_conf_shift(0, sll, "sll", "00000101", "00011000", 0, use_domains);
        check_conf_shift(0, sll, "sll", "00000110", "11001100", 0, use_domains);
        check_conf_shift(0, sll, "sll", "00000111", "11000000", 0, use_domains);
        break;
      default: break;
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_INV_CONF_SLL_TESTS;

  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    clear_domains();

    bzla_node_release(d_bzla, sll);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Test if for x >> s = t and s >> x = t, the consistent value and inverse
   * value computation always produces a value t when solved for x where the
   * shifted bits match the corresponding bits in the shifted operand.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_srl(uint32_t bw, bool use_domains)
  {
    (void) bw;
    BzlaNode *srl, *e[2];
    BzlaSortId sort;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    srl = bzla_exp_bv_srl(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      bzla_synthesize_exp(d_bzla, srl, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, srl);
    }

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_SRL_TESTS:
    /* s >> e[1] = bvsrl */

    /* -> shifted bits must match */
    switch (bw)
    {
      case 2:
        check_conf_shift(1, srl, "srl", "00", "01", 1, use_domains);
        check_conf_shift(1, srl, "srl", "00", "10", 0, use_domains);
        check_conf_shift(1, srl, "srl", "00", "11", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "01", "10", 0, use_domains);
        check_conf_shift(1, srl, "srl", "01", "11", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "10", "11", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "11", "10", 0, use_domains);
        break;

      case 4:
        check_conf_shift(1, srl, "srl", "0000", "0010", 2, use_domains);
        check_conf_shift(1, srl, "srl", "0000", "1000", 0, use_domains);
        check_conf_shift(1, srl, "srl", "0000", "0110", 1, use_domains);
        check_conf_shift(1, srl, "srl", "0000", "1110", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "0001", "0110", 1, use_domains);
        check_conf_shift(1, srl, "srl", "0001", "0011", 2, use_domains);
        check_conf_shift(1, srl, "srl", "0001", "0101", 1, use_domains);
        check_conf_shift(1, srl, "srl", "0001", "0111", 1, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "1000", "0110", 1, use_domains);
        check_conf_shift(1, srl, "srl", "1000", "0011", 2, use_domains);
        check_conf_shift(1, srl, "srl", "1000", "0101", 1, use_domains);
        check_conf_shift(1, srl, "srl", "1000", "0111", 1, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "1010", "0110", 1, use_domains);
        check_conf_shift(1, srl, "srl", "1010", "0011", 2, use_domains);
        check_conf_shift(1, srl, "srl", "1010", "0111", 1, use_domains);
        check_conf_shift(1, srl, "srl", "1010", "1111", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "0110", "0111", 1, use_domains);
        check_conf_shift(1, srl, "srl", "0110", "0010", 2, use_domains);
        check_conf_shift(1, srl, "srl", "0110", "1010", 0, use_domains);
        check_conf_shift(1, srl, "srl", "0110", "1111", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "1111", "0101", 1, use_domains);
        check_conf_shift(1, srl, "srl", "1111", "0110", 1, use_domains);
        check_conf_shift(1, srl, "srl", "1111", "0010", 2, use_domains);
        check_conf_shift(1, srl, "srl", "1111", "0100", 1, use_domains);
        break;

      case 8:
        check_conf_shift(1, srl, "srl", "00000000", "01111111", 1, use_domains);
        check_conf_shift(1, srl, "srl", "00000000", "01010101", 1, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "00000100", "00111100", 2, use_domains);
        check_conf_shift(1, srl, "srl", "00000100", "00001111", 4, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "00100000", "11001100", 0, use_domains);
        check_conf_shift(1, srl, "srl", "00100000", "01000010", 1, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "01010101", "01010111", 1, use_domains);
        check_conf_shift(1, srl, "srl", "01010101", "00101001", 2, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "11111110", "10111100", 0, use_domains);
        check_conf_shift(1, srl, "srl", "11111110", "11111101", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "01111111", "00101111", 2, use_domains);
        check_conf_shift(1, srl, "srl", "01111111", "11111101", 0, use_domains);
        ///
        check_conf_shift(1, srl, "srl", "11111111", "01011111", 1, use_domains);
        check_conf_shift(1, srl, "srl", "11111111", "11111101", 0, use_domains);
        break;

      default: break;
    }

    /* e[0] << s = bvsrl
     * -> LSBs shifted must be zero */
    switch (bw)
    {
      case 2:
        check_conf_shift(0, srl, "srl", "01", "10", 0, use_domains);
        check_conf_shift(0, srl, "srl", "01", "11", 0, use_domains);
        break;
      case 4:
        check_conf_shift(0, srl, "srl", "0001", "1000", 0, use_domains);
        check_conf_shift(0, srl, "srl", "0010", "0110", 0, use_domains);
        check_conf_shift(0, srl, "srl", "0011", "0011", 0, use_domains);
        break;
      case 8:
        check_conf_shift(0, srl, "srl", "00000001", "11000000", 0, use_domains);
        check_conf_shift(0, srl, "srl", "00000010", "01110000", 0, use_domains);
        check_conf_shift(0, srl, "srl", "00000011", "00110000", 0, use_domains);
        check_conf_shift(0, srl, "srl", "00000100", "00111111", 0, use_domains);
        check_conf_shift(0, srl, "srl", "00000101", "00011000", 0, use_domains);
        check_conf_shift(0, srl, "srl", "00000110", "00110011", 0, use_domains);
        check_conf_shift(0, srl, "srl", "00000111", "00000011", 0, use_domains);
        break;
      default: break;
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_INV_CONF_SRL_TESTS;

  DONE:
    bzla_node_release(d_bzla, srl);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);

    clear_domains();

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;
  }

  /**
   * Given x * s = t and s * x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_mul(uint32_t bw, bool use_domains)
  {
    (void) bw;
    uint32_t i, j, k, r;
    BzlaNode *mul, *e[2];
    BzlaSortId sort;
    BzlaBitVector *t, *s;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    mul = bzla_exp_bv_mul(d_bzla, e[0], e[1]);

    /* prop engine: all conflicts are treated as fixable */

  PROP_COMPLETE_CONF_MUL_TESTS:
    /* s = 0 but t > 0 */
    s = bzla_bv_zero(d_mm, bw);
    for (k = 0; k < 10; k++)
    {
      t = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
      while (bzla_bv_is_zero(t))
      {
        bzla_bv_free(d_mm, t);
        t = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
      }
      check_conf_mul_result(mul, t, s, use_domains);
      bzla_bv_free(d_mm, t);
    }
    bzla_bv_free(d_mm, s);

    /* t is odd but s is even */
    for (k = 0; k < 10; k++)
    {
      t = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
      if (!bzla_bv_get_bit(t, 0)) bzla_bv_set_bit(t, 0, 1);
      s = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
      if (bzla_bv_get_bit(s, 0)) bzla_bv_set_bit(s, 0, 0);
      check_conf_mul_result(mul, t, s, use_domains);
      bzla_bv_free(d_mm, t);
      bzla_bv_free(d_mm, s);
    }

    /* s = 2^i and number of 0-LSBs in t < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 1; bw > 1 && i < bw; i++)
      {
        s = bzla_bv_zero(d_mm, bw);
        bzla_bv_set_bit(s, i, 1);
        t = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
        r = bzla_rng_pick_rand(d_bzla->rng, 0, i - 1);
        for (j = 0; j < r; j++) bzla_bv_set_bit(t, j, 0);
        if (!bzla_bv_get_bit(t, r)) bzla_bv_set_bit(t, r, 1);
        check_conf_mul_result(mul, t, s, use_domains);
        bzla_bv_free(d_mm, t);
        bzla_bv_free(d_mm, s);
      }
    }

    /* s = 2^i * m and number of 0-LSBs in t < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 0; bw > 1 && i < 10; i++)
      {
        s = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
        while (bzla_bv_power_of_two(s) >= 0)
        {
          bzla_bv_free(d_mm, s);
          s = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
        }
        if (bzla_bv_get_bit(s, 0))
        {
          r = bzla_rng_pick_rand(d_bzla->rng, 1, bw - 1);
          for (j = 0; j < r; j++) bzla_bv_set_bit(s, j, 0);
        }
        else
        {
          for (j = 0; j < bw; j++)
            if (bzla_bv_get_bit(s, j)) break;
        }
        t = bzla_bv_new_random(d_mm, d_bzla->rng, bw);
        r = bzla_rng_pick_rand(d_bzla->rng, 0, j - 1);
        for (j = 0; j < r; j++) bzla_bv_set_bit(t, j, 0);
        if (!bzla_bv_get_bit(t, r)) bzla_bv_set_bit(t, r, 1);
        check_conf_mul_result(mul, t, s, use_domains);
        bzla_bv_free(d_mm, t);
        bzla_bv_free(d_mm, s);
      }
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);
    goto PROP_COMPLETE_CONF_MUL_TESTS;

  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    bzla_node_release(d_bzla, mul);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Given x / s = t and s / x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_udiv(uint32_t bw, bool use_domains)
  {
    (void) bw;
    int32_t k;
    BzlaNode *udiv, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s, *bvudiv, *bvmax, *zero, *tmp, *tmp2;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    udiv = bzla_exp_bv_udiv(d_bzla, e[0], e[1]);

    zero  = bzla_bv_zero(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_COMPLETE_CONF_UDIV_TESTS:
    /* s / e[1] = bvudiv */
    /* s = 1...1 and bvudiv = 0 */
    s      = bzla_bv_copy(d_mm, bvmax);
    bvudiv = bzla_bv_zero(d_mm, bw);
    check_conf_udiv_result(1, udiv, bvudiv, s, use_domains);
    bzla_bv_free(d_mm, bvudiv);
    bzla_bv_free(d_mm, s);
    /* s < bvudiv */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      s   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      tmp    = bzla_bv_inc(d_mm, s);
      tmp2   = bzla_bv_dec(d_mm, bvmax);
      bvudiv = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      check_conf_udiv_result(1, udiv, bvudiv, s, use_domains);
      bzla_bv_free(d_mm, bvudiv);
      bzla_bv_free(d_mm, s);
    }
    /* e[0] / s = bvudiv */
    /* s = 0 and bvudiv < 1...1 */
    for (k = 0; k < 10; k++)
    {
      s      = bzla_bv_zero(d_mm, bw);
      tmp    = bzla_bv_dec(d_mm, bvmax);
      bvudiv = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      check_conf_udiv_result(0, udiv, bvudiv, s, use_domains);
      bzla_bv_free(d_mm, bvudiv);
      bzla_bv_free(d_mm, s);
    }
    /* bvudiv = 1...1 and s > 1 */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      bvudiv = bzla_bv_copy(d_mm, bvmax);
      tmp    = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      s      = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(d_mm, tmp);
      check_conf_udiv_result(0, udiv, bvudiv, s, use_domains);
      bzla_bv_free(d_mm, bvudiv);
      bzla_bv_free(d_mm, s);
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_COMPLETE_CONF_UDIV_TESTS;
  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    bzla_bv_free(d_mm, bvmax);
    bzla_bv_free(d_mm, zero);

    bzla_node_release(d_bzla, udiv);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Given x % s = t and s % x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_urem(uint32_t bw, bool use_domains)
  {
    (void) bw;
    int32_t k;
    BzlaNode *exp, *e[2], *cexp, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *s, *t, *bvmax, *zero, *two, *tmp, *tmp2;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = bzla_exp_bv_urem(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_urem_const;
      cons_fun   = bzla_proputils_cons_urem_const;
      bzla_synthesize_exp(d_bzla, exp, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }
    else
    {
      is_inv_fun = bzla_is_inv_urem;
      cons_fun   = bzla_proputils_cons_urem;
    }

    zero  = bzla_bv_zero(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

    slv = 0;
  PROP_COMPLETE_CONF_UREM_TESTS:
    /* s % e[1] = t */
    /* t = 1...1 and s < 1...1 */
    t = bzla_bv_copy(d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp = bzla_bv_dec(d_mm, bvmax);
      s   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, zero, tmp);
      init_prop_info(&pi, exp, 1, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_TRUE(bzla_bv_is_zero(res));
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      init_prop_info(&pi, cexp, 1, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_TRUE(bzla_bv_is_zero(res));
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, s);
    }
    bzla_bv_free(d_mm, t);
    /* s < t */
    for (k = 0; k < 10; k++)
    {
      tmp = bzla_bv_inc(d_mm, zero);
      t   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(d_mm, tmp);
      tmp = bzla_bv_dec(d_mm, t);
      s   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      init_prop_info(&pi, exp, 1, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      init_prop_info(&pi, cexp, 1, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, s);
      bzla_bv_free(d_mm, t);
    }
    /* s > t and s - t <= t -> s > 2 * t */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      two  = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      tmp2 = bzla_bv_udiv(d_mm, bvmax, two);
      tmp  = bzla_bv_uint64_to_bv(d_mm, 1, bw);
      t    = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      tmp  = bzla_bv_inc(d_mm, t);
      tmp2 = bzla_bv_mul(d_mm, t, two);
      s    = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      init_prop_info(&pi, exp, 1, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      init_prop_info(&pi, cexp, 1, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, two);
      bzla_bv_free(d_mm, t);
      bzla_bv_free(d_mm, s);
    }

    /* e[0] % s = t */
    /* t = 1...1 and s > 0 */
    t = bzla_bv_copy(d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp = bzla_bv_inc(d_mm, zero);
      s   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, bvmax);
      init_prop_info(&pi, exp, 0, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_EQ(bzla_bv_compare(res, t), 0);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_urem(d_bzla, e[0], ce);
      init_prop_info(&pi, cexp, 0, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_EQ(bzla_bv_compare(res, t), 0);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, s);
    }
    bzla_bv_free(d_mm, t);
    /* s > 0 and s <= t */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp = bzla_bv_inc(d_mm, zero);
      t   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, bvmax);
      s   = bzla_bv_new_random_range(d_mm, d_bzla->rng, bw, tmp, t);
      init_prop_info(&pi, exp, 0, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_urem(d_bzla, e[0], ce);
      init_prop_info(&pi, cexp, 0, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, t);
      bzla_bv_free(d_mm, s);
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_COMPLETE_CONF_UREM_TESTS;

  DONE:
    assert(slv);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    clear_domains();

    bzla_bv_free(d_mm, zero);
    bzla_bv_free(d_mm, bvmax);
    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Given x o s = t and s o x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_concat(uint32_t bw, bool use_domains)
  {
    (void) bw;
    int32_t k, cnt;
    uint32_t i, j, bws[2];
    BzlaNode *exp, *e[2], *ce[2], *cexp[2];
    BzlaSortId sorts[2];
    BzlaBitVector *res, *t, *s[2], *tmp[2];
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    /* prop engine: all conflicts are treated as fixable */

    slv = 0;
  PROP_COMPLETE_CONF_CONCAT_TESTS:

    for (k = 0; bw > 1 && k < 10; k++)
    {
      bws[0]   = bzla_rng_pick_rand(d_bzla->rng, 1, bw - 1);
      bws[1]   = bw - bws[0];
      sorts[0] = bzla_sort_bv(d_bzla, bw);
      sorts[1] = bzla_sort_bv(d_bzla, bw);
      e[0]     = bzla_exp_var(d_bzla, sorts[0], 0);
      e[1]     = bzla_exp_var(d_bzla, sorts[1], 0);
      exp      = bzla_exp_bv_concat(d_bzla, e[0], e[1]);
      t        = bzla_bv_new_random(d_mm, d_bzla->rng, bw);

      if (use_domains)
      {
        assert(d_domains);
        is_inv_fun = bzla_is_inv_concat_const;
        cons_fun   = bzla_proputils_cons_concat_const;
        bzla_synthesize_exp(d_bzla, exp, 0);
        bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
        x0 = (BzlaBvDomain *) bzla_hashint_map_get(
                 d_domains, bzla_node_real_addr(exp->e[0])->id)
                 ->as_ptr;
        x1 = (BzlaBvDomain *) bzla_hashint_map_get(
                 d_domains, bzla_node_real_addr(exp->e[1])->id)
                 ->as_ptr;
      }
      else
      {
        is_inv_fun = bzla_is_inv_concat;
        cons_fun   = bzla_proputils_cons_concat;
      }

      for (j = 0; j < 2; j++)
      {
        s[j] = bzla_bv_slice(d_mm, t, j ? bws[1] - 1 : bw - 1, j ? 0 : bws[1]);
        ASSERT_EQ(bzla_bv_get_width(s[j]), bws[j]);
        tmp[j] = bzla_bv_copy(d_mm, s[j]);
        cnt    = 0;
        while (!cnt)
        {
          for (i = 0; i < bws[j]; i++)
          {
            if (bzla_rng_pick_rand(d_bzla->rng, 0, 5))
            {
              bzla_bv_set_bit(s[j], i, bzla_bv_get_bit(s[j], i) ? 0 : 1);
              cnt += 1;
            }
          }
        }
      }
      ce[0]   = bzla_exp_bv_const(d_bzla, s[0]);
      ce[1]   = bzla_exp_bv_const(d_bzla, s[1]);
      cexp[0] = bzla_exp_bv_concat(d_bzla, ce[0], e[1]);
      cexp[1] = bzla_exp_bv_concat(d_bzla, e[0], ce[1]);
      for (j = 0; j < 2; j++)
      {
        init_prop_info(
            &pi, exp, j, t, j ? s[0] : 0, j ? 0 : s[1], 0, x0, x1, 0);
        ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
        res = cons_fun(d_bzla, &pi);
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, tmp[j]), 0);
        bzla_bv_free(d_mm, res);
        if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

        init_prop_info(&pi,
                       cexp[j ? 0 : 1],
                       j,
                       t,
                       j ? s[0] : 0,
                       j ? 0 : s[1],
                       0,
                       x0,
                       x1,
                       0);
        ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
        res = cons_fun(d_bzla, &pi);
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, tmp[j]), 0);
        bzla_bv_free(d_mm, res);
        if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      }
      for (j = 0; j < 2; j++)
      {
        bzla_sort_release(d_bzla, sorts[j]);
        bzla_node_release(d_bzla, cexp[j]);
        bzla_node_release(d_bzla, ce[j]);
        bzla_node_release(d_bzla, e[j]);
        bzla_bv_free(d_mm, s[j]);
        bzla_bv_free(d_mm, tmp[j]);
      }

      clear_domains();

      bzla_node_release(d_bzla, exp);
      bzla_bv_free(d_mm, t);
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_COMPLETE_CONF_CONCAT_TESTS;

  DONE:
    assert(slv);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;
  }

  BzlaMemMgr *d_mm            = nullptr;
  BzlaRNG *d_rng              = nullptr;
  BzlaIntHashTable *d_domains = nullptr;

 private:
  /**
   * Given x * s = t and s * x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * exp           : The node representing the multiplication.
   * t             : The assignment of 'mul'.
   * s             : The assignment of one of the operands of 'mul'.
   * use_domains   : True if this check should be performed w.r.t. const bits.
   */
  void check_conf_mul_result(BzlaNode *exp,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             bool use_domains)
  {
    BzlaNode *cexp[2], *ce[2];
    BzlaBitVector *res;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_mul_const;
      cons_fun   = bzla_proputils_cons_mul_const;
      bzla_synthesize_exp(d_bzla, exp, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }
    else
    {
      is_inv_fun = bzla_is_inv_mul;
      cons_fun   = bzla_proputils_cons_mul;
    }

    ce[0]   = bzla_exp_bv_const(d_bzla, s);
    ce[1]   = bzla_exp_bv_const(d_bzla, s);
    cexp[0] = bzla_exp_bv_mul(d_bzla, ce[0], exp->e[1]);
    cexp[1] = bzla_exp_bv_mul(d_bzla, exp->e[0], ce[1]);

    /* idx_x = 0 */
    init_prop_info(&pi, exp, 0, t, 0, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    init_prop_info(&pi, cexp[1], 0, t, 0, s, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    if (bzla_bv_get_bit(t, 0))
    {
      ASSERT_EQ(bzla_bv_get_bit(res, 0), 1u);
    }
    bzla_bv_free(d_mm, res);

    /* idx_x = 1 */
    init_prop_info(&pi, exp, 1, t, s, 0, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    init_prop_info(&pi, cexp[0], 1, t, s, 0, 0, x0, x1, 0);
    ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
    res = cons_fun(d_bzla, &pi);
    ASSERT_NE(res, nullptr);
    if (bzla_bv_get_bit(t, 0))
    {
      ASSERT_EQ(bzla_bv_get_bit(res, 0), 1u);
    }
    bzla_bv_free(d_mm, res);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    clear_domains();

    bzla_node_release(d_bzla, ce[0]);
    bzla_node_release(d_bzla, ce[1]);
    bzla_node_release(d_bzla, cexp[0]);
    bzla_node_release(d_bzla, cexp[1]);
  }

  /**
   * Given x / s = t and s / x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * exp        : The node representing the unsigned division.
   * t          : The assignment of 'udiv'.
   * s          : The assignment of one of the operands of udiv.
   * use_domains: True if this check should be performed w.r.t. const bits.
   */
  void check_conf_udiv_result(uint32_t idx_x,
                              BzlaNode *exp,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              bool use_domains)
  {
    BzlaNode *cexp, *ce;
    BzlaBitVector *res;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaPropIsInvFun is_inv_fun      = 0;
    BzlaPropComputeValueFun cons_fun = 0;
    BzlaPropInfo pi;

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_udiv_const;
      cons_fun   = bzla_proputils_cons_udiv_const;
      bzla_synthesize_exp(d_bzla, exp, 0);
      bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }
    else
    {
      is_inv_fun = bzla_is_inv_udiv;
      cons_fun   = bzla_proputils_cons_udiv;
    }

    if (idx_x)
    {
      init_prop_info(&pi, exp, idx_x, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_FALSE(bzla_bv_is_umulo(d_mm, res, t));
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_udiv(d_bzla, ce, exp->e[1]);
      init_prop_info(&pi, cexp, idx_x, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_FALSE(bzla_bv_is_umulo(d_mm, res, t));
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
    }
    else
    {
      init_prop_info(&pi, exp, idx_x, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      ce   = bzla_exp_bv_const(d_bzla, s);
      cexp = bzla_exp_bv_udiv(d_bzla, exp->e[0], ce);
      init_prop_info(&pi, cexp, idx_x, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
      bzla_node_release(d_bzla, cexp);
      bzla_node_release(d_bzla, ce);
    }

    clear_domains();
  }

  /**
   * Given x <> s = t and s <> x = t where <> is a shift operator, test if the
   * consistent value and inverse value computation always produces a 'legal'
   * value t when solved for x.
   *
   * shift  : The node representing the shift operation.
   * s_val  : A char* array representing the values for all operands of <>.
   * t_val  : A char* representation of the target value of <>.
   * rvalmax: The maximum value of the inverse/consistent value.
   */
  void check_conf_shift(uint32_t idx_x,
                        BzlaNode *exp,
                        std::string op,
                        const char *s_val,
                        const char *t_val,
                        uint64_t rvalmax,
                        bool use_domains)
  {
    assert(d_domains);

    BzlaNode *cexp, *ce;
    BzlaBitVector *res, *t, *s;
    BzlaBvDomain *x0 = 0, *x1 = 0;

    /* The function to create a node representing the exp operation. */
    BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *);
    /* The function to test if given operator is invertible w.r.t. s and t. */
    BzlaPropIsInvFun is_inv_fun;
    /* The function to compute the consistent value for x. */
    BzlaPropComputeValueFun cons_fun;
    BzlaPropInfo pi;

    if (op == "sll")
    {
      exp_fun    = bzla_exp_bv_sll;
      is_inv_fun = use_domains ? bzla_is_inv_sll_const : bzla_is_inv_sll;
      cons_fun =
          use_domains ? bzla_proputils_cons_sll : bzla_proputils_cons_sll_const;
      cons_fun = bzla_proputils_cons_sll;
    }
    else
    {
      assert(op == "srl");
      exp_fun    = bzla_exp_bv_srl;
      is_inv_fun = use_domains ? bzla_is_inv_srl_const : bzla_is_inv_srl;
      cons_fun =
          use_domains ? bzla_proputils_cons_srl : bzla_proputils_cons_srl_const;
      cons_fun = bzla_proputils_cons_srl;
    }

    if (use_domains)
    {
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[0])->id)
               ->as_ptr;
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[1])->id)
               ->as_ptr;
    }

    s  = bzla_bv_char_to_bv(d_mm, s_val);
    t  = bzla_bv_char_to_bv(d_mm, t_val);
    ce = bzla_exp_bv_const(d_bzla, s);
    if (idx_x)
    {
      init_prop_info(&pi, exp, idx_x, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_LE(bzla_bv_to_uint64(res), rvalmax);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      cexp = exp_fun(d_bzla, ce, exp->e[1]);
      init_prop_info(&pi, cexp, idx_x, t, s, 0, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      ASSERT_LE(bzla_bv_to_uint64(res), rvalmax);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
    }
    else
    {
      init_prop_info(&pi, exp, idx_x, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

      cexp = exp_fun(d_bzla, exp->e[0], ce);
      init_prop_info(&pi, cexp, idx_x, t, 0, s, 0, x0, x1, 0);
      ASSERT_FALSE(is_inv_fun(d_bzla, &pi));
      res = cons_fun(d_bzla, &pi);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
    }
    bzla_bv_free(d_mm, t);
    bzla_bv_free(d_mm, s);
    bzla_node_release(d_bzla, ce);
    bzla_node_release(d_bzla, cexp);
  }
};

/*------------------------------------------------------------------------*/

class TestPropCompleteConst : public TestPropComplete
{
 protected:
  void SetUp() override
  {
    TestPropComplete::SetUp();

    bzla_opt_set(d_bzla, BZLA_OPT_PROP_CONST_BITS, 1);
  }

  /** Helper for check_result_aux. */
  void check_result_n_tests(BzlaPropIsInvFun is_inv_fun,
                            BzlaPropComputeValueFun val_fun,
                            BzlaPropInfo *pi)
  {
    uint32_t idx_x;
    uint64_t k;
    bool is_inv;
    BzlaBitVector *res;
    const BzlaBitVector *s, *t, *x_bv;
    const BzlaBvDomain *x;

    idx_x = pi->pos_x;
    x     = pi->bvd[idx_x];
    x_bv  = pi->bv[idx_x];
    s     = pi->bv[idx_x ? 0 : 1];
    t     = pi->target_value;

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      pi->res_x = 0;
      if (is_inv_fun)
      {
        is_inv = is_inv_fun(d_bzla, pi);
        if (!is_inv)
        {
          std::cout << "x: ";
          bzla_bvdomain_print(d_mm, x, true);
          std::cout << "t: ";
          bzla_bv_print(t);
          std::cout << "s: ";
          bzla_bv_print(s);
          std::cout << "idx_x: " << idx_x << std::endl;
        }
        assert(is_inv);
      }
      res = val_fun(d_bzla, pi);
      if (pi->res_x) bzla_bvdomain_free(d_mm, pi->res_x);
      ASSERT_NE(res, nullptr);
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    if (!res)
    {
      std::cout << "domain x: ";
      bzla_bvdomain_print(d_mm, x, true);
      std::cout << "x: ";
      bzla_bv_print(x_bv);
      std::cout << "t: ";
      bzla_bv_print(t);
      std::cout << "s: ";
      bzla_bv_print(s);
      std::cout << "idx_x: " << idx_x << std::endl;
    }
    ASSERT_NE(res, nullptr);
    ASSERT_EQ(bzla_bv_compare(res, x_bv), 0);
    bzla_bv_free(d_mm, res);
  }

  /** Helper for check_result_cond_aux. */
  void check_result_cond_n_tests(BzlaPropIsInvFun is_inv_fun,
                                 BzlaPropComputeValueFun val_fun,
                                 BzlaPropInfo *pi)
  {
    uint32_t idx_x;
    uint64_t k;
    BzlaBitVector *res, *tmp;
    const BzlaBitVector *s0, *s1, *t, *x_bv;
    const BzlaBvDomain *x;

    idx_x = pi->pos_x;
    x     = pi->bvd[idx_x];
    x_bv  = pi->bv[idx_x];
    s0    = pi->bv[idx_x == 0 ? 1 : 0];
    s1    = pi->bv[idx_x == 2 ? 1 : 2];
    t     = pi->target_value;

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      pi->res_x = 0;
      if (is_inv_fun)
      {
        ASSERT_TRUE(is_inv_fun(d_bzla, pi));
      }
      res = val_fun(d_bzla, pi);
      if (pi->res_x) bzla_bvdomain_free(d_mm, pi->res_x);
      ASSERT_NE(res, nullptr);
      if ((idx_x == 1 && bzla_bv_is_zero(s0))
          || (idx_x == 2 && bzla_bv_is_one(s0)))
      {
        /* In case of cond, the implementation is not complete on purpose:
         * We don't care about disabled branches, and will never produce all
         * possible values for them. */
        break;
      }
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    if (!res)
    {
      std::cout << "x: ";
      bzla_bv_print(x_bv);
      std::cout << "domain x: ";
      bzla_bvdomain_print(d_mm, x, true);
      std::cout << "t: ";
      bzla_bv_print(t);
      std::cout << "s0: ";
      bzla_bv_print(s0);
      std::cout << "s1: ";
      bzla_bv_print(s1);
      std::cout << "idx_x: " << idx_x << std::endl;
    }
    ASSERT_NE(res, nullptr);
    tmp = bzla_bv_ite(d_mm,
                      idx_x == 0 ? res : pi->bv[0],
                      idx_x == 1 ? res : pi->bv[1],
                      idx_x == 2 ? res : pi->bv[2]);
    ASSERT_EQ(bzla_bv_compare(tmp, t), 0);
    bzla_bv_free(d_mm, tmp);
    bzla_bv_free(d_mm, res);
  }

  /** Helper for check_result_slice_aux. */
  void check_result_slice_n_tests(BzlaPropIsInvFun is_inv_fun,
                                  BzlaPropComputeValueFun val_fun,
                                  BzlaPropInfo *pi)
  {
    uint64_t k;
    BzlaBitVector *res;
    const BzlaBitVector *x_bv;

    x_bv = pi->bv[0];

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      pi->res_x = 0;
      if (is_inv_fun)
      {
        ASSERT_TRUE(is_inv_fun(d_bzla, pi));
      }
      res = val_fun(d_bzla, pi);
      ASSERT_NE(res, nullptr);
      if (pi->res_x) bzla_bvdomain_free(d_mm, pi->res_x);
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    ASSERT_NE(res, nullptr);
    ASSERT_EQ(bzla_bv_compare(res, x_bv), 0);
    bzla_bv_free(d_mm, res);
  }

  /** Helper for check_result. */
  void check_result_aux(BzlaPropIsInvFun is_inv_fun,
                        BzlaPropComputeValueFun val_fun,
                        BzlaPropInfo *pi,
                        std::vector<uint32_t> &fixed_idx)
  {
    BzlaNode *children[2];

    bzla_synthesize_exp(d_bzla, (BzlaNode *) pi->exp, 0);
    bzla_prop_solver_init_domains(d_bzla, d_domains, (BzlaNode *) pi->exp);
    if (bzla_is_bv_sra(d_bzla, pi->exp, &children[0], &children[1]))
    {
      assert(bzla_hashint_map_contains(d_domains,
                                       bzla_node_real_addr(children[0])->id));
      assert(bzla_hashint_map_contains(d_domains,
                                       bzla_node_real_addr(children[1])->id));

      pi->bvd[0] = (BzlaBvDomain *) bzla_hashint_map_get(
                       d_domains, bzla_node_real_addr(children[0])->id)
                       ->as_ptr;
      pi->bvd[1] = (BzlaBvDomain *) bzla_hashint_map_get(
                       d_domains, bzla_node_real_addr(children[1])->id)
                       ->as_ptr;
    }
    else
    {
      assert(bzla_hashint_map_contains(d_domains,
                                       bzla_node_real_addr(pi->exp->e[0])->id));
      assert(bzla_hashint_map_contains(d_domains,
                                       bzla_node_real_addr(pi->exp->e[1])->id));

      pi->bvd[0] = (BzlaBvDomain *) bzla_hashint_map_get(
                       d_domains, bzla_node_real_addr(pi->exp->e[0])->id)
                       ->as_ptr;
      pi->bvd[1] = (BzlaBvDomain *) bzla_hashint_map_get(
                       d_domains, bzla_node_real_addr(pi->exp->e[1])->id)
                       ->as_ptr;
    }
    BzlaBvDomain *x = (BzlaBvDomain *) pi->bvd[pi->pos_x];
    ASSERT_FALSE(bzla_bvdomain_has_fixed_bits(d_mm, x));
    const BzlaBitVector *x_bv = pi->bv[pi->pos_x];

    for (uint32_t i : fixed_idx)
    {
      bzla_bvdomain_fix_bit(x, i, bzla_bv_get_bit(x_bv, i));
    }

    check_result_n_tests(is_inv_fun, val_fun, pi);
    clear_domains();
  }

  /** Helper for check_result_cond. */
  void check_result_cond_aux(BzlaPropIsInvFun is_inv_fun,
                             BzlaPropComputeValueFun val_fun,
                             BzlaPropInfo *pi,
                             std::vector<uint32_t> &fixed_idx)
  {
    bzla_synthesize_exp(d_bzla, (BzlaNode *) pi->exp, 0);
    bzla_prop_solver_init_domains(d_bzla, d_domains, (BzlaNode *) pi->exp);
    assert(bzla_hashint_map_contains(d_domains,
                                     bzla_node_real_addr(pi->exp->e[0])->id));
    assert(bzla_hashint_map_contains(d_domains,
                                     bzla_node_real_addr(pi->exp->e[1])->id));
    assert(bzla_hashint_map_contains(d_domains,
                                     bzla_node_real_addr(pi->exp->e[2])->id));
    pi->bvd[0] = (BzlaBvDomain *) bzla_hashint_map_get(
                     d_domains, bzla_node_real_addr(pi->exp->e[0])->id)
                     ->as_ptr;
    pi->bvd[1] = (BzlaBvDomain *) bzla_hashint_map_get(
                     d_domains, bzla_node_real_addr(pi->exp->e[1])->id)
                     ->as_ptr;
    pi->bvd[2] = (BzlaBvDomain *) bzla_hashint_map_get(
                     d_domains, bzla_node_real_addr(pi->exp->e[2])->id)
                     ->as_ptr;
    BzlaBvDomain *x = (BzlaBvDomain *) pi->bvd[pi->pos_x];
    ASSERT_FALSE(bzla_bvdomain_has_fixed_bits(d_mm, x));
    const BzlaBitVector *x_bv = pi->bv[pi->pos_x];

    for (uint32_t i : fixed_idx)
    {
      bzla_bvdomain_fix_bit(x, i, bzla_bv_get_bit(x_bv, i));
    }

    check_result_cond_n_tests(is_inv_fun, val_fun, pi);
    clear_domains();
  }

  /** Helper for check_result_slice. */
  void check_result_slice_aux(BzlaPropIsInvFun is_inv_fun,
                              BzlaPropComputeValueFun val_fun,
                              BzlaPropInfo *pi,
                              std::vector<uint32_t> &fixed_idx)
  {
    bzla_synthesize_exp(d_bzla, (BzlaNode *) pi->exp, 0);
    bzla_prop_solver_init_domains(d_bzla, d_domains, (BzlaNode *) pi->exp);
    assert(bzla_hashint_map_contains(d_domains,
                                     bzla_node_real_addr(pi->exp->e[0])->id));
    pi->bvd[0] = (BzlaBvDomain *) bzla_hashint_map_get(
                     d_domains, bzla_node_real_addr(pi->exp->e[0])->id)
                     ->as_ptr;
    BzlaBvDomain *x = (BzlaBvDomain *) pi->bvd[pi->pos_x];
    ASSERT_FALSE(bzla_bvdomain_has_fixed_bits(d_mm, x));
    const BzlaBitVector *x_bv = pi->bv[pi->pos_x];

    for (uint32_t i : fixed_idx)
    {
      bzla_bvdomain_fix_bit(x, i, bzla_bv_get_bit(x_bv, i));
    }

    check_result_slice_n_tests(is_inv_fun, val_fun, pi);
    clear_domains();
  }

  /**
   * Check the result of a previous inverse value computation. Given 's'
   * (the assignment of the other operand) and 't' (the target value of the
   * operation) we expect that we determine an inverse value 'x_bv' for the
   * operand at index 'idx_x' while considering const bits in 'x' (which are
   * set to bits in 'x_bv').
   *
   * We use this to check that a value 's' that was previously determined as
   * the inverse value for an operation given 't' and 'x_bv', produces 'x_bv'
   * as inverse value, i.e., we essentially reverse the inverse value
   * computation with respect to the operands.
   *
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to s and t.
   * val_fun   : The function to compute the value for x given s and t.
   * pi        : The struct containing all information needed for is_inv checks
   *             and invers/consistent value computation.
   */
  void check_result(BzlaPropIsInvFun is_inv_fun,
                    BzlaPropComputeValueFun val_fun,
                    BzlaPropInfo *pi)
  {
    assert(val_fun);
    assert(pi);

    std::vector<uint32_t> fixed_idx;
    const BzlaBitVector *x_bv = pi->bv[pi->pos_x];

    /* set one bit */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      fixed_idx.push_back(i);
      check_result_aux(is_inv_fun, val_fun, pi, fixed_idx);
      fixed_idx.clear();
    }

    /* set two bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        fixed_idx.push_back(i);
        fixed_idx.push_back(j);
        check_result_aux(is_inv_fun, val_fun, pi, fixed_idx);
        fixed_idx.clear();
      }
    }

    /* set three bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        for (uint32_t k = j + 1, bw = bzla_bv_get_width(x_bv); k < bw; ++k)
        {
          fixed_idx.push_back(i);
          fixed_idx.push_back(j);
          fixed_idx.push_back(k);
          check_result_aux(is_inv_fun, val_fun, pi, fixed_idx);
          fixed_idx.clear();
        }
      }
    }
  }

  /**
   * Same as check_result but for cond.
   *
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to s0, s1 and t.
   * val_fun   : The function to compute the value for x given s0, s1 and t.
   * pi        : The struct containing all information needed for is_inv checks
   *             and invers/consistent value computation.
   */
  void check_result_cond(BzlaPropIsInvFun is_inv_fun,
                         BzlaPropComputeValueFun val_fun,
                         BzlaPropInfo *pi)
  {
    assert(pi);

    const BzlaBitVector *x_bv = pi->bv[pi->pos_x];
    std::vector<uint32_t> fixed_idx;

    /* set one bit */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      fixed_idx.push_back(i);
      check_result_cond_aux(is_inv_fun, val_fun, pi, fixed_idx);
      fixed_idx.clear();
    }

    /* set two bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        fixed_idx.push_back(i);
        fixed_idx.push_back(j);
        check_result_cond_aux(is_inv_fun, val_fun, pi, fixed_idx);
        fixed_idx.clear();
      }
    }

    /* set three bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        for (uint32_t k = j + 1, bw = bzla_bv_get_width(x_bv); k < bw; ++k)
        {
          fixed_idx.push_back(i);
          fixed_idx.push_back(j);
          fixed_idx.push_back(k);
          check_result_cond_aux(is_inv_fun, val_fun, pi, fixed_idx);
          fixed_idx.clear();
        }
      }
    }
  }

  /**
   * Check the result of a previous inverse value computation for slice.
   * Given 't' (the target value of the slice peration) and 'upper' and 'lower'
   * (the indices that define the slice range) we expect that we determine an
   * inverse value 'x_bv' while considering const bits in 'x' (which are
   * set to bits in 'x_bv').
   *
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to upper, lower and t.
   * val_fun   : The function to compute the value for x given upper, lower
   *             and t.
   * pi        : The struct containing all information needed for is_inv checks
   *             and invers/consistent value computation.
   */
  void check_result_slice(BzlaPropIsInvFun is_inv_fun,
                          BzlaPropComputeValueFun val_fun,
                          BzlaPropInfo *pi)
  {
    std::vector<uint32_t> fixed_idx;
    const BzlaBitVector *x_bv = pi->bv[pi->pos_x];

    /* set one bit */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      fixed_idx.push_back(i);
      check_result_slice_aux(is_inv_fun, val_fun, pi, fixed_idx);
      fixed_idx.clear();
    }

    /* set two bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        fixed_idx.push_back(i);
        fixed_idx.push_back(j);
        check_result_slice_aux(is_inv_fun, val_fun, pi, fixed_idx);
        fixed_idx.clear();
      }
    }

    /* set three bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        for (uint32_t k = j + 1, bw = bzla_bv_get_width(x_bv); k < bw; ++k)
        {
          fixed_idx.push_back(i);
          fixed_idx.push_back(j);
          fixed_idx.push_back(k);
          check_result_slice_aux(is_inv_fun, val_fun, pi, fixed_idx);
          fixed_idx.clear();
        }
      }
    }
  }

  /**
   * Test if for a binary operation s0 <> s1 = t, the inverse value computation
   * for the first operand produces value s0, and the inverse value computation
   * for the second operand produces value s1.
   *
   * exp_fun    : The function to create a node representing operation <>.
   * bv_fun     : The function to create the bit-vector result of
   *              operation s0 <> s1.
   * is_inv_fun : The function to test if given operator is invertible
   *              with respect to s and t.
   * val_fun    : The function to compute the value for x given s and t
   *              considering const bits in x.
   */
  void check_binary(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                    BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                             const BzlaBitVector *,
                                             const BzlaBitVector *),
                    BzlaPropIsInvFun is_inv_fun,
                    BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *t;
    BzlaPropInfo pi;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = exp_fun(d_bzla, e[0], e[1]);

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        t    = bv_fun(d_mm, s[0], s[1]);
        /* domains are initialized later */
        init_prop_info(&pi, exp, 1, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        init_prop_info(&pi, exp, 0, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }

  /** Same as check_binary but for cond.  */
  void check_cond(BzlaPropIsInvFun is_inv_fun, BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j, k;
    BzlaNode *exp, *e[3];
    BzlaSortId sort, sort1;
    BzlaBitVector *s[3], *t;
    BzlaPropInfo pi;

    bw    = TEST_PROP_INV_COMPLETE_BW;
    sort  = bzla_sort_bv(d_bzla, bw);
    sort1 = bzla_sort_bv(d_bzla, 1);
    e[0]  = bzla_exp_var(d_bzla, sort1, 0);
    e[1]  = bzla_exp_var(d_bzla, sort, 0);
    e[2]  = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    bzla_sort_release(d_bzla, sort1);
    exp = bzla_exp_cond(d_bzla, e[0], e[1], e[2]);

    for (i = 0; i < (uint32_t)(1 << 1); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, 1);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        for (k = 0; k < (uint32_t)(1 << bw); k++)
        {
          s[2] = bzla_bv_uint64_to_bv(d_mm, k, bw);
          t    = bzla_bv_ite(d_mm, s[0], s[1], s[2]);
          /* domains are initialized later */
          init_prop_info(&pi, exp, 2, t, s[0], s[1], s[2], 0, 0, 0);
          check_result_cond(is_inv_fun, val_fun, &pi);
          init_prop_info(&pi, exp, 1, t, s[0], s[1], s[2], 0, 0, 0);
          check_result_cond(is_inv_fun, val_fun, &pi);
          init_prop_info(&pi, exp, 2, t, s[0], s[1], s[2], 0, 0, 0);
          check_result_cond(is_inv_fun, val_fun, &pi);
          bzla_bv_free(d_mm, s[2]);
          bzla_bv_free(d_mm, t);
        }
        bzla_bv_free(d_mm, s[1]);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, e[2]);
    bzla_node_release(d_bzla, exp);
  }

  /** Same as check_binary but for cond.  */
  void check_slice(BzlaPropIsInvFun is_inv_fun, BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t up, lo, i;
    BzlaNode *exp, *e;
    BzlaBitVector *t, *x;
    BzlaSortId sort;
    BzlaPropInfo pi;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e    = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);

    for (lo = 0; lo < bw; lo++)
    {
      for (up = lo; up < bw; up++)
      {
        exp = bzla_exp_bv_slice(d_bzla, e, up, lo);
        for (i = 0; i < (uint32_t)(1 << bw); i++)
        {
          x = bzla_bv_uint64_to_bv(d_mm, i, bw);
          t = bzla_bv_slice(d_mm, x, up, lo);
          /* domains are initialized later */
          init_prop_info(&pi, exp, 0, t, x, 0, 0, 0, 0, 0);
          check_result_slice(is_inv_fun, val_fun, &pi);
          bzla_bv_free(d_mm, x);
          bzla_bv_free(d_mm, t);
        }
        bzla_node_release(d_bzla, exp);
      }
    }
    bzla_node_release(d_bzla, e);
  }

  /**
   * Test if for a shift operation s0 <> s1 = t, the inverse value computation
   * for the first operand produces value s0, and the inverse value computation
   * for the second operand produces value s1.
   *
   * exp_fun   : The function to create a node representing operation <>.
   * bv_fun    : The function to create the bit-vector result of
   *             operation s0 <> s1.
   * is_inv_fun: The function to test if given operator is invertible
   *             with respect to s and t.
   * val_fun   : The function to compute the value for x given s and t.
   */
  void check_shift(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                   BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                            const BzlaBitVector *,
                                            const BzlaBitVector *),
                   BzlaPropIsInvFun is_inv_fun,
                   BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *t;
    BzlaPropInfo pi;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = exp_fun(d_bzla, e[0], e[1]);

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        t    = bv_fun(d_mm, s[0], s[1]);
        /* domains are initialized later */
        init_prop_info(&pi, exp, 0, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        init_prop_info(&pi, exp, 1, t, s[0], s[1], 0, 0, 0, 0);
        check_result(is_inv_fun, val_fun, &pi);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }
};

/* ========================================================================== */
/* complete:                                                                  */
/* Test if given                                                              */
/* x <op> s = t or                                                            */
/* s <op> x = t or                                                            */
/* x <op> t                                                                   */
/* we can find solution x as result of the inverse value computation within   */
/* TEST_PROP_INV_COMPLETE_N_TESTS tries.                                      */
/* ========================================================================== */

/* -------------------------------------------------------------------------- */
/* Regular inverse value computation, no const bits.                          */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropComplete, complete_add_inv)
{
  check_binary(
      bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, bzla_proputils_inv_add);
}

TEST_F(TestPropComplete, complete_and_inv)
{
  check_binary(
      bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, bzla_proputils_inv_and);
}

TEST_F(TestPropComplete, complete_xor_inv)
{
  check_binary(
      bzla_exp_bv_xor, bzla_bv_xor, bzla_is_inv_xor, bzla_proputils_inv_xor);
}

TEST_F(TestPropComplete, complete_eq_inv)
{
  check_binary(bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq);
}

TEST_F(TestPropComplete, complete_ult_inv)
{
  check_binary(
      bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, bzla_proputils_inv_ult);
}

TEST_F(TestPropComplete, complete_ult_sext_inv)
{
  check_inv_lt_sext(2);
  check_inv_lt_sext(3);
  check_inv_lt_sext(5);
  check_inv_lt_sext(6);
}

TEST_F(TestPropComplete, complete_ult_concat_inv)
{
  check_inv_lt_concat(2);
  check_inv_lt_concat(3);
  check_inv_lt_concat(5);
  check_inv_lt_concat(6);
}

TEST_F(TestPropComplete, complete_slt_sext_inv)
{
  check_inv_lt_sext(2, true);
  check_inv_lt_sext(3, true);
  check_inv_lt_sext(5, true);
  check_inv_lt_sext(6, true);
}

TEST_F(TestPropComplete, complete_slt_concat_inv)
{
  check_inv_lt_concat(2, true);
  check_inv_lt_concat(3, true);
  check_inv_lt_concat(5, true);
  check_inv_lt_concat(6, true);
}

TEST_F(TestPropComplete, complete_slt_inv)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  check_binary(
      bzla_exp_bv_slt, bzla_bv_slt, bzla_is_inv_slt, bzla_proputils_inv_slt);
}

TEST_F(TestPropComplete, complete_sll_inv)
{
  check_shift(
      bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, bzla_proputils_inv_sll);
}

TEST_F(TestPropComplete, complete_srl_inv)
{
  check_shift(
      bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, bzla_proputils_inv_srl);
}

TEST_F(TestPropComplete, complete_sra_inv)
{
  check_shift(
      bzla_exp_bv_sra, bzla_bv_sra, bzla_is_inv_sra, bzla_proputils_inv_sra);
}

TEST_F(TestPropComplete, complete_mul_inv)
{
  check_binary(
      bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, bzla_proputils_inv_mul);
}

TEST_F(TestPropComplete, complete_udiv_inv)
{
  check_binary(bzla_exp_bv_udiv,
               bzla_bv_udiv,
               bzla_is_inv_udiv,
               bzla_proputils_inv_udiv);
}

TEST_F(TestPropComplete, complete_urem_inv)
{
  check_binary(bzla_exp_bv_urem,
               bzla_bv_urem,
               bzla_is_inv_urem,
               bzla_proputils_inv_urem);
}

TEST_F(TestPropComplete, complete_concat_inv)
{
  check_binary(bzla_exp_bv_concat,
               bzla_bv_concat,
               bzla_is_inv_concat,
               bzla_proputils_inv_concat);
}

TEST_F(TestPropComplete, complete_slice_inv)
{
  check_slice(bzla_is_inv_slice, bzla_proputils_inv_slice);
}

TEST_F(TestPropComplete, complete_cond_inv)
{
  check_cond(bzla_is_inv_cond, bzla_proputils_inv_cond);
}

/* -------------------------------------------------------------------------- */
/* Regular consistent value computation, no const bits.                       */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropComplete, complete_add_cons)
{
  check_binary(bzla_exp_bv_add, bzla_bv_add, 0, bzla_proputils_cons_add);
}

TEST_F(TestPropComplete, complete_and_cons)
{
  check_binary(bzla_exp_bv_and, bzla_bv_and, 0, bzla_proputils_cons_and);
}

TEST_F(TestPropComplete, complete_xor_cons)
{
  check_binary(bzla_exp_bv_xor, bzla_bv_xor, 0, bzla_proputils_cons_xor);
}

TEST_F(TestPropComplete, complete_eq_cons)
{
  check_binary(bzla_exp_eq, bzla_bv_eq, 0, bzla_proputils_cons_eq);
}

TEST_F(TestPropComplete, complete_ult_cons)
{
  check_binary(bzla_exp_bv_ult, bzla_bv_ult, 0, bzla_proputils_cons_ult);
}

TEST_F(TestPropComplete, complete_slt_cons)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  check_binary(bzla_exp_bv_slt, bzla_bv_slt, 0, bzla_proputils_cons_slt);
}

TEST_F(TestPropComplete, complete_sll_cons)
{
  check_shift(bzla_exp_bv_sll, bzla_bv_sll, 0, bzla_proputils_cons_sll);
}

TEST_F(TestPropComplete, complete_srl_cons)
{
  check_shift(bzla_exp_bv_srl, bzla_bv_srl, 0, bzla_proputils_cons_srl);
}

TEST_F(TestPropComplete, complete_sra_cons)
{
  check_shift(bzla_exp_bv_sra, bzla_bv_sra, 0, bzla_proputils_cons_sra);
}

TEST_F(TestPropComplete, complete_mul_cons)
{
  check_binary(bzla_exp_bv_mul, bzla_bv_mul, 0, bzla_proputils_cons_mul);
}

TEST_F(TestPropComplete, complete_udiv_cons)
{
  check_binary(bzla_exp_bv_udiv, bzla_bv_udiv, 0, bzla_proputils_cons_udiv);
}

TEST_F(TestPropComplete, complete_urem_cons)
{
  check_binary(bzla_exp_bv_urem, bzla_bv_urem, 0, bzla_proputils_cons_urem);
}

TEST_F(TestPropComplete, complete_concat_cons)
{
  check_binary(
      bzla_exp_bv_concat, bzla_bv_concat, 0, bzla_proputils_cons_concat);
}

TEST_F(TestPropComplete, complete_slice_cons)
{
  check_slice(0, bzla_proputils_cons_slice);
}

TEST_F(TestPropComplete, complete_cond_cons)
{
  check_cond(0, bzla_proputils_cons_cond);
}

/* -------------------------------------------------------------------------- */
/* Inverse value computation with propagator domains, const bits.             */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropCompleteConst, complete_add_inv_const)
{
  check_binary(bzla_exp_bv_add,
               bzla_bv_add,
               bzla_is_inv_add_const,
               bzla_proputils_inv_add_const);
}

TEST_F(TestPropCompleteConst, complete_and_inv_const)
{
  check_binary(bzla_exp_bv_and,
               bzla_bv_and,
               bzla_is_inv_and_const,
               bzla_proputils_inv_and_const);
}

TEST_F(TestPropCompleteConst, complete_xor_inv_const)
{
  check_binary(bzla_exp_bv_xor,
               bzla_bv_xor,
               bzla_is_inv_xor_const,
               bzla_proputils_inv_xor_const);
}

TEST_F(TestPropCompleteConst, complete_eq_inv_const)
{
  check_binary(bzla_exp_eq,
               bzla_bv_eq,
               bzla_is_inv_eq_const,
               bzla_proputils_inv_eq_const);
}

TEST_F(TestPropCompleteConst, complete_ult_inv_const)
{
  check_binary(bzla_exp_bv_ult,
               bzla_bv_ult,
               bzla_is_inv_ult_const,
               bzla_proputils_inv_ult_const);
}

TEST_F(TestPropCompleteConst, complete_slt_inv_const)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  check_binary(bzla_exp_bv_slt,
               bzla_bv_slt,
               bzla_is_inv_slt_const,
               bzla_proputils_inv_slt_const);
}

TEST_F(TestPropCompleteConst, complete_mul_inv_const)
{
  check_binary(bzla_exp_bv_mul,
               bzla_bv_mul,
               bzla_is_inv_mul_const,
               bzla_proputils_inv_mul_const);
}

TEST_F(TestPropCompleteConst, complete_sll_inv_const)
{
  check_shift(bzla_exp_bv_sll,
              bzla_bv_sll,
              bzla_is_inv_sll_const,
              bzla_proputils_inv_sll_const);
}

TEST_F(TestPropCompleteConst, complete_srl_inv_const)
{
  check_shift(bzla_exp_bv_srl,
              bzla_bv_srl,
              bzla_is_inv_srl_const,
              bzla_proputils_inv_srl_const);
}

TEST_F(TestPropCompleteConst, complete_sra_inv_const)
{
  check_shift(bzla_exp_bv_sra,
              bzla_bv_sra,
              bzla_is_inv_sra_const,
              bzla_proputils_inv_sra_const);
}

TEST_F(TestPropCompleteConst, complete_urem_inv_const)
{
  check_binary(bzla_exp_bv_urem,
               bzla_bv_urem,
               bzla_is_inv_urem_const,
               bzla_proputils_inv_urem_const);
}

TEST_F(TestPropCompleteConst, complete_udiv_inv_const)
{
  check_binary(bzla_exp_bv_udiv,
               bzla_bv_udiv,
               bzla_is_inv_udiv_const,
               bzla_proputils_inv_udiv_const);
}

TEST_F(TestPropCompleteConst, complete_concat_inv_const)
{
  check_binary(bzla_exp_bv_concat,
               bzla_bv_concat,
               bzla_is_inv_concat_const,
               bzla_proputils_inv_concat_const);
}

TEST_F(TestPropCompleteConst, complete_cond_inv_const)
{
  check_cond(bzla_is_inv_cond_const, bzla_proputils_inv_cond_const);
}

TEST_F(TestPropCompleteConst, complete_slice_inv_const)
{
  check_slice(bzla_is_inv_slice_const, bzla_proputils_inv_slice_const);
}

/* -------------------------------------------------------------------------- */
/* Consistent value computation with propagator domains, const bits.          */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropCompleteConst, complete_add_cons_const)
{
  check_binary(bzla_exp_bv_add, bzla_bv_add, 0, bzla_proputils_cons_add_const);
}

TEST_F(TestPropCompleteConst, complete_and_cons_const)
{
  check_binary(bzla_exp_bv_and, bzla_bv_and, 0, bzla_proputils_cons_and_const);
}

TEST_F(TestPropCompleteConst, complete_xor_cons_const)
{
  check_binary(bzla_exp_bv_xor, bzla_bv_xor, 0, bzla_proputils_cons_xor_const);
}

TEST_F(TestPropCompleteConst, complete_eq_cons_const)
{
  check_binary(bzla_exp_eq, bzla_bv_eq, 0, bzla_proputils_cons_eq_const);
}

TEST_F(TestPropCompleteConst, complete_ult_cons_const)
{
  check_binary(bzla_exp_bv_ult, bzla_bv_ult, 0, bzla_proputils_cons_ult_const);
}

TEST_F(TestPropCompleteConst, complete_slt_cons_const)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  check_binary(bzla_exp_bv_slt, bzla_bv_slt, 0, bzla_proputils_cons_slt_const);
}

TEST_F(TestPropCompleteConst, complete_mul_cons_const)
{
  check_binary(bzla_exp_bv_mul, bzla_bv_mul, 0, bzla_proputils_cons_mul_const);
}

TEST_F(TestPropCompleteConst, complete_sll_cons_const)
{
  check_shift(bzla_exp_bv_sll, bzla_bv_sll, 0, bzla_proputils_cons_sll_const);
}

TEST_F(TestPropCompleteConst, complete_srl_cons_const)
{
  check_shift(bzla_exp_bv_srl, bzla_bv_srl, 0, bzla_proputils_cons_srl_const);
}

TEST_F(TestPropCompleteConst, complete_sra_cons_const)
{
  check_shift(bzla_exp_bv_sra, bzla_bv_sra, 0, bzla_proputils_cons_sra_const);
}

TEST_F(TestPropCompleteConst, complete_urem_cons_const)
{
  check_binary(
      bzla_exp_bv_urem, bzla_bv_urem, 0, bzla_proputils_cons_urem_const);
}

TEST_F(TestPropCompleteConst, complete_udiv_cons_const)
{
  check_binary(
      bzla_exp_bv_udiv, bzla_bv_udiv, 0, bzla_proputils_cons_udiv_const);
}

TEST_F(TestPropCompleteConst, complete_concat_cons_const)
{
  check_binary(
      bzla_exp_bv_concat, bzla_bv_concat, 0, bzla_proputils_cons_concat_const);
}

TEST_F(TestPropCompleteConst, complete_cond_cons_const)
{
  check_cond(0, bzla_proputils_cons_cond_const);
}

TEST_F(TestPropCompleteConst, complete_slice_cons_const)
{
  check_slice(0, bzla_proputils_cons_slice_const);
}

/* ========================================================================== */
/* complete:                                                                  */
/* Test if given                                                              */
/* x <op> s = t or                                                            */
/* s <op> x = t or                                                            */
/* x <op> t                                                                   */
/* we can find solution x as result of the inverse value computation within   */
/* TEST_PROP_INV_COMPLETE_N_TESTS tries.                                      */
/* ========================================================================== */

/* -------------------------------------------------------------------------- */
/* Regular inverse value computation, no const bits, no propagator domains.   */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropComplete, conf_and)
{
  check_conf_and(1, false);
  check_conf_and(4, false);
  check_conf_and(8, false);
  check_conf_and(1, true);
  check_conf_and(4, true);
  check_conf_and(8, true);
}

TEST_F(TestPropComplete, conf_ult)
{
  check_conf_ult(1, false);
  check_conf_ult(4, false);
  check_conf_ult(8, false);
  check_conf_ult(1, true);
  check_conf_ult(4, true);
  check_conf_ult(8, true);
}

TEST_F(TestPropComplete, conf_slt)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  check_conf_slt(1, false);
  check_conf_slt(4, false);
  check_conf_slt(8, false);
  check_conf_slt(1, true);
  check_conf_slt(4, true);
  check_conf_slt(8, true);
}

TEST_F(TestPropComplete, conf_sll)
{
  check_conf_sll(2, false);
  check_conf_sll(4, false);
  check_conf_sll(8, false);
  check_conf_sll(2, true);
  check_conf_sll(4, true);
  check_conf_sll(8, true);
}

TEST_F(TestPropComplete, conf_srl)
{
  check_conf_srl(2, false);
  check_conf_srl(4, false);
  check_conf_srl(8, false);
  check_conf_srl(2, true);
  check_conf_srl(4, true);
  check_conf_srl(8, true);
}

TEST_F(TestPropComplete, conf_mul)
{
  check_conf_mul(1, false);
  check_conf_mul(4, false);
  check_conf_mul(8, false);
  check_conf_mul(1, true);
  check_conf_mul(4, true);
  check_conf_mul(8, true);
}

TEST_F(TestPropComplete, conf_udiv)
{
  check_conf_udiv(1, false);
  check_conf_udiv(4, false);
  check_conf_udiv(8, false);
  check_conf_udiv(1, true);
  check_conf_udiv(4, true);
  check_conf_udiv(8, true);
}

TEST_F(TestPropComplete, conf_urem)
{
  check_conf_urem(1, false);
  check_conf_urem(4, false);
  check_conf_urem(8, false);
}

TEST_F(TestPropComplete, conf_concat)
{
  check_conf_concat(2, false);
  check_conf_concat(4, false);
  check_conf_concat(8, false);
}
