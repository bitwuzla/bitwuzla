/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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

class TestPropInv : public TestBzla
{
 protected:
  static constexpr uint32_t TEST_PROP_INV_COMPLETE_BW      = 4u;
  static constexpr uint64_t TEST_PROP_INV_COMPLETE_N_TESTS = 10000u;

  void SetUp() override
  {
    TestBzla::SetUp();

    d_bzla->slv       = bzla_new_prop_solver(d_bzla);
    d_bzla->slv->bzla = d_bzla;
    d_mm              = d_bzla->mm;
    d_rng             = &d_bzla->rng;
    d_domains         = BZLA_PROP_SOLVER(d_bzla)->domains;

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    bzla_opt_set(d_bzla, BZLA_OPT_REWRITE_LEVEL, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_SORT_EXP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_CONC_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_EQ_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_AND_FLIP, 0);

    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_generate(d_bzla, d_bzla->bv_model, d_bzla->fun_model, 0);
  }

  void check_result(BzlaPropIsInv is_inv,
                    BzlaPropComputeValue inv_fun_bv,
                    BzlaPropComputeValue inv_fun_bvprop,
                    BzlaNode *exp,
                    BzlaBitVector *bve,
                    BzlaBitVector *bvn,
                    BzlaBitVector *bvres,
                    uint32_t idx_x,
                    bool use_domains)
  {
    uint64_t k;
    BzlaBitVector *res;
    BzlaIntHashTableIterator iit;

    if (use_domains)
    {
      assert(!d_domains);
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, exp);
    }

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      assert(is_inv(d_mm, bvn, bve, idx_x));
      if (use_domains)
      {
        res = inv_fun_bvprop(d_bzla, exp, bvn, bve, idx_x, d_domains);
      }
      else
      {
        res = inv_fun_bv(d_bzla, exp, bvn, bve, idx_x, d_domains);
      }
      ASSERT_NE(res, nullptr);
      if (!bzla_bv_compare(res, bvres)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    ASSERT_NE(res, nullptr);
    ASSERT_EQ(bzla_bv_compare(res, bvres), 0);
    bzla_bv_free(d_mm, res);

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }
  }

  void check_binary(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                    BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                             const BzlaBitVector *,
                                             const BzlaBitVector *),
                    BzlaPropIsInv is_inv,
                    BzlaPropComputeValue inv_fun_bv,
                    BzlaPropComputeValue inv_fun_bvprop,
                    bool use_domains)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *bve[2], *bvexp;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = exp_fun(d_bzla, e[0], e[1]);

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      bve[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        bve[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        bvexp  = bv_fun(d_mm, bve[0], bve[1]);
        check_result(is_inv,
                     inv_fun_bv,
                     inv_fun_bvprop,
                     exp,
                     bve[0],
                     bvexp,
                     bve[1],
                     1,
                     use_domains);
        check_result(is_inv,
                     inv_fun_bv,
                     inv_fun_bvprop,
                     exp,
                     bve[1],
                     bvexp,
                     bve[0],
                     0,
                     use_domains);
        bzla_bv_free(d_mm, bve[1]);
        bzla_bv_free(d_mm, bvexp);
      }
      bzla_bv_free(d_mm, bve[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }

  void check_shift(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                   BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                            const BzlaBitVector *,
                                            const BzlaBitVector *),
                   BzlaPropIsInv is_inv,
                   BzlaPropComputeValue inv_fun_bv,
                   BzlaPropComputeValue inv_fun_bvprop,
                   bool use_domains)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *bve[2], *bvexp;

    bw   = TEST_PROP_INV_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    exp = exp_fun(d_bzla, e[0], e[1]);

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      bve[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        bve[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        bvexp  = bv_fun(d_mm, bve[0], bve[1]);
        check_result(is_inv,
                     inv_fun_bv,
                     inv_fun_bvprop,
                     exp,
                     bve[0],
                     bvexp,
                     bve[1],
                     1,
                     use_domains);
        check_result(is_inv,
                     inv_fun_bv,
                     inv_fun_bvprop,
                     exp,
                     bve[1],
                     bvexp,
                     bve[0],
                     0,
                     use_domains);
        bzla_bv_free(d_mm, bve[1]);
        bzla_bv_free(d_mm, bvexp);
      }
      bzla_bv_free(d_mm, bve[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }

  void check_conf_and(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    bool inv;
    uint64_t i, j;
    BzlaNode *_and, *cand[2], *e[2], *ce[2];
    BzlaSortId sort;
    BzlaBitVector *bvand, *bve[2], *res, *tmp, *tmp2;
    BzlaSolver *slv = 0;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_and_bv;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    _and = bzla_exp_bv_and(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_and_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, _and);
    }

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      bve[0]  = bzla_bv_uint64_to_bv(d_mm, i, bw);
      bve[1]  = bzla_bv_uint64_to_bv(d_mm, i, bw);
      ce[0]   = bzla_exp_bv_const(d_bzla, bve[0]);
      ce[1]   = bzla_exp_bv_const(d_bzla, bve[1]);
      cand[0] = bzla_exp_bv_and(d_bzla, ce[0], e[1]);
      cand[1] = bzla_exp_bv_and(d_bzla, e[0], ce[1]);

      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        bvand = bzla_bv_uint64_to_bv(d_mm, j, bw);
        tmp   = bzla_bv_and(d_mm, bve[0], bvand);
        if (bzla_bv_compare(tmp, bvand))
        {
        PROP_INV_CONF_AND_TESTS:
          /* prop engine: all conflicts are treated as fixable */
          inv = bzla_is_inv_and(d_mm, bvand, bve[1], 0);
          res = inv ? inv_fun(d_bzla, _and, bvand, bve[1], 0, d_domains)
                    : cons_and_bv(d_bzla, _and, bvand, bve[1], 0, d_domains);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          inv = bzla_is_inv_and(d_mm, bvand, bve[0], 1);
          res = inv ? inv_fun(d_bzla, _and, bvand, bve[0], 1, d_domains)
                    : cons_and_bv(d_bzla, _and, bvand, bve[0], 1, d_domains);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          inv = bzla_is_inv_and(d_mm, bvand, bve[0], 1);
          res = inv ? inv_fun(d_bzla, cand[0], bvand, bve[0], 1, d_domains)
                    : cons_and_bv(d_bzla, cand[0], bvand, bve[0], 1, d_domains);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          inv = bzla_is_inv_and(d_mm, bvand, bve[1], 0);
          res = inv ? inv_fun(d_bzla, cand[1], bvand, bve[1], 0, d_domains)
                    : cons_and_bv(d_bzla, cand[1], bvand, bve[1], 0, d_domains);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS)
            goto DONE;

          /* sls engine: only fixable if non-const inputs */
          slv         = d_bzla->slv;
          d_bzla->slv = bzla_new_sls_solver(d_bzla);
          bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

          goto PROP_INV_CONF_AND_TESTS;
        DONE:
          bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
          d_bzla->slv->api.delet(d_bzla->slv);
          d_bzla->slv = slv;
        }
        bzla_bv_free(d_mm, bvand);
        bzla_bv_free(d_mm, tmp);
      }
      bzla_node_release(d_bzla, cand[0]);
      bzla_node_release(d_bzla, cand[1]);
      bzla_node_release(d_bzla, ce[0]);
      bzla_node_release(d_bzla, ce[1]);
      bzla_bv_free(d_mm, bve[0]);
      bzla_bv_free(d_mm, bve[1]);
    }

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }

    bzla_node_release(d_bzla, _and);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_ult(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    bool inv;
    BzlaNode *ult, *e[2], *cult, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *bvult, *bve, *zero, *bvmax;
    BzlaSolver *slv = 0;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_ult_bv;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    ult = bzla_exp_bv_ult(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_ult_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, ult);
    }

    zero  = bzla_bv_new(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);
    bvult = bzla_bv_one(d_mm, 1);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_ULT_TESTS:
    /* 1...1 < e[1] */
    bve = bzla_bv_ones(d_mm, bw);
    inv = bzla_is_inv_ult(d_mm, bvult, bve, 1);
    res = inv ? inv_fun(d_bzla, ult, bvult, bve, 1, d_domains)
              : cons_ult_bv(d_bzla, ult, bvult, bve, 1, d_domains);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_compare(res, zero), 0);
    bzla_bv_free(d_mm, res);
    ce   = bzla_exp_bv_const(d_bzla, bve);
    cult = bzla_exp_bv_ult(d_bzla, ce, e[1]);
    inv  = bzla_is_inv_ult(d_mm, bvult, bve, 1);
    res  = inv ? inv_fun(d_bzla, cult, bvult, bve, 1, d_domains)
              : cons_ult_bv(d_bzla, cult, bvult, bve, 1, d_domains);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_compare(res, zero), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cult);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, bve);
    /* e[0] < 0 */
    bve = bzla_bv_new(d_mm, bw);
    inv = bzla_is_inv_ult(d_mm, bvult, bve, 0);
    res = inv ? inv_fun(d_bzla, ult, bvult, bve, 0, d_domains)
              : cons_ult_bv(d_bzla, ult, bvult, bve, 0, d_domains);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_compare(res, bvmax), 0);
    bzla_bv_free(d_mm, res);
    ce   = bzla_exp_bv_const(d_bzla, bve);
    cult = bzla_exp_bv_ult(d_bzla, e[0], ce);
    inv  = bzla_is_inv_ult(d_mm, bvult, bve, 0);
    res  = inv ? inv_fun(d_bzla, cult, bvult, bve, 0, d_domains)
              : cons_ult_bv(d_bzla, cult, bvult, bve, 0, d_domains);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_compare(res, bvmax), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cult);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, bve);

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_INV_CONF_ULT_TESTS;

  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }

    bzla_bv_free(d_mm, bvult);
    bzla_bv_free(d_mm, zero);
    bzla_bv_free(d_mm, bvmax);

    bzla_node_release(d_bzla, ult);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_sll(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    BzlaNode *sll, *e[2];
    BzlaSortId sort;
    BzlaSolver *slv = 0;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_sll_bv;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    sll = bzla_exp_bv_sll(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_sll_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, sll);
    }

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_SLL_TESTS:
    /* bve << e[1] = bvsll */

    /* -> shifted bits must match */
    switch (bw)
    {
      case 2:
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00",
                         "01",
                         0);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00",
                         "10",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00",
                         "11",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01",
                         "11",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "10",
                         "01",
                         0);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "10",
                         "11",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "11",
                         "01",
                         0);
        break;

      case 4:
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0000",
                         "0010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0000",
                         "1000",
                         3);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0000",
                         "0110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0000",
                         "1110",
                         1);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0001",
                         "0110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0001",
                         "1100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0001",
                         "1010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0001",
                         "1110",
                         1);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1000",
                         "0110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1000",
                         "1100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1000",
                         "1010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1000",
                         "1110",
                         1);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1010",
                         "0110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1010",
                         "1100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1010",
                         "1110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1010",
                         "1111",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0110",
                         "0111",
                         0);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0110",
                         "0010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0110",
                         "1010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0110",
                         "1111",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1111",
                         "1010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1111",
                         "0110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1111",
                         "0010",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "1111",
                         "0011",
                         0);
        break;

      case 8:
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000000",
                         "11111110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000000",
                         "10101010",
                         1);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000100",
                         "00111100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000100",
                         "11110000",
                         4);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00100000",
                         "11001100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00100000",
                         "01000010",
                         1);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01010101",
                         "10101110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01010101",
                         "10100100",
                         2);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "11111110",
                         "10111100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "11111110",
                         "11111101",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01111111",
                         "10111100",
                         2);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01111111",
                         "11111101",
                         0);
        ///
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "11111111",
                         "10111110",
                         1);
        check_conf_shift(1,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "11111111",
                         "11111101",
                         0);
        break;

      default: break;
    }

    /* e[0] << bve = bvsll
     * -> LSBs shifted must be zero */
    switch (bw)
    {
      case 2:
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01",
                         "01",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "01",
                         "11",
                         0);
        break;
      case 4:
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0001",
                         "0001",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0010",
                         "0110",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "0011",
                         "1100",
                         0);
        break;
      case 8:
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000001",
                         "00000011",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000010",
                         "00001110",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000011",
                         "00001100",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000100",
                         "11111100",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000101",
                         "00011000",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000110",
                         "11001100",
                         0);
        check_conf_shift(0,
                         sll,
                         e,
                         bzla_exp_bv_sll,
                         bzla_is_inv_sll,
                         inv_fun,
                         cons_sll_bv,
                         "00000111",
                         "11000000",
                         0);
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

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }

    bzla_node_release(d_bzla, sll);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_srl(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    BzlaNode *srl, *e[2];
    BzlaSortId sort;
    BzlaSolver *slv = 0;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_srl_bv;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    srl = bzla_exp_bv_srl(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_srl_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, srl);
    }

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_SRL_TESTS:
    /* bve >> e[1] = bvsrl */

    /* -> shifted bits must match */
    switch (bw)
    {
      case 2:
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00",
                         "01",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00",
                         "10",
                         0);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00",
                         "11",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01",
                         "10",
                         0);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01",
                         "11",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "10",
                         "11",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "11",
                         "10",
                         0);
        break;

      case 4:
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0000",
                         "0010",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0000",
                         "1000",
                         0);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0000",
                         "0110",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0000",
                         "1110",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0001",
                         "0110",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0001",
                         "0011",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0001",
                         "0101",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0001",
                         "0111",
                         1);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1000",
                         "0110",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1000",
                         "0011",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1000",
                         "0101",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1000",
                         "0111",
                         1);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1010",
                         "0110",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1010",
                         "0011",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1010",
                         "0111",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1010",
                         "1111",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0110",
                         "0111",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0110",
                         "0010",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0110",
                         "1010",
                         0);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0110",
                         "1111",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1111",
                         "0101",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1111",
                         "0110",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1111",
                         "0010",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "1111",
                         "0100",
                         1);
        break;

      case 8:
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000000",
                         "01111111",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000000",
                         "01010101",
                         1);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000100",
                         "00111100",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000100",
                         "00001111",
                         4);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00100000",
                         "11001100",
                         0);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00100000",
                         "01000010",
                         1);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01010101",
                         "01010111",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01010101",
                         "00101001",
                         2);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "11111110",
                         "10111100",
                         0);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "11111110",
                         "11111101",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01111111",
                         "00101111",
                         2);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01111111",
                         "11111101",
                         0);
        ///
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "11111111",
                         "01011111",
                         1);
        check_conf_shift(1,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "11111111",
                         "11111101",
                         0);
        break;

      default: break;
    }

    /* e[0] << bve = bvsrl
     * -> LSBs shifted must be zero */
    switch (bw)
    {
      case 2:
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01",
                         "10",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "01",
                         "11",
                         0);
        break;
      case 4:
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0001",
                         "1000",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0010",
                         "0110",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "0011",
                         "0011",
                         0);
        break;
      case 8:
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000001",
                         "11000000",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000010",
                         "01110000",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000011",
                         "00110000",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000100",
                         "00111111",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000101",
                         "00011000",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000110",
                         "00110011",
                         0);
        check_conf_shift(0,
                         srl,
                         e,
                         bzla_exp_bv_srl,
                         bzla_is_inv_srl,
                         inv_fun,
                         cons_srl_bv,
                         "00000111",
                         "00000011",
                         0);
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

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;
#else
    (void) bw;
#endif
  }

  void check_conf_mul(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    uint32_t i, j, k, r;
    BzlaNode *mul, *e[2];
    BzlaSortId sort;
    BzlaBitVector *bvmul, *bve;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    mul = bzla_exp_bv_mul(d_bzla, e[0], e[1]);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_MUL_TESTS:
    /* bve = 0 but bvmul > 0 */
    bve = bzla_bv_new(d_mm, bw);
    for (k = 0; k < 10; k++)
    {
      bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      while (bzla_bv_is_zero(bvmul))
      {
        bzla_bv_free(d_mm, bvmul);
        bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      }
      check_conf_mul_result(mul, e, bvmul, bve, use_domains);
      bzla_bv_free(d_mm, bvmul);
    }
    bzla_bv_free(d_mm, bve);

    /* bvmul is odd but bve is even */
    for (k = 0; k < 10; k++)
    {
      bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      if (!bzla_bv_get_bit(bvmul, 0)) bzla_bv_set_bit(bvmul, 0, 1);
      bve = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      if (bzla_bv_get_bit(bve, 0)) bzla_bv_set_bit(bve, 0, 0);
      check_conf_mul_result(mul, e, bvmul, bve, use_domains);
      bzla_bv_free(d_mm, bvmul);
      bzla_bv_free(d_mm, bve);
    }

    /* bve = 2^i and number of 0-LSBs in bvmul < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 1; bw > 1 && i < bw; i++)
      {
        bve = bzla_bv_new(d_mm, bw);
        bzla_bv_set_bit(bve, i, 1);
        bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        r     = bzla_rng_pick_rand(&d_bzla->rng, 0, i - 1);
        for (j = 0; j < r; j++) bzla_bv_set_bit(bvmul, j, 0);
        if (!bzla_bv_get_bit(bvmul, r)) bzla_bv_set_bit(bvmul, r, 1);
        check_conf_mul_result(mul, e, bvmul, bve, use_domains);
        bzla_bv_free(d_mm, bvmul);
        bzla_bv_free(d_mm, bve);
      }
    }

    /* bve = 2^i * m and number of 0-LSBs in bvmul < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 0; bw > 1 && i < 10; i++)
      {
        bve = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        while (bzla_bv_power_of_two(bve) >= 0)
        {
          bzla_bv_free(d_mm, bve);
          bve = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        }
        if (bzla_bv_get_bit(bve, 0))
        {
          r = bzla_rng_pick_rand(&d_bzla->rng, 1, bw - 1);
          for (j = 0; j < r; j++) bzla_bv_set_bit(bve, j, 0);
        }
        else
        {
          for (j = 0; j < bw; j++)
            if (bzla_bv_get_bit(bve, j)) break;
        }
        bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        r     = bzla_rng_pick_rand(&d_bzla->rng, 0, j - 1);
        for (j = 0; j < r; j++) bzla_bv_set_bit(bvmul, j, 0);
        if (!bzla_bv_get_bit(bvmul, r)) bzla_bv_set_bit(bvmul, r, 1);
        check_conf_mul_result(mul, e, bvmul, bve, use_domains);
        bzla_bv_free(d_mm, bvmul);
        bzla_bv_free(d_mm, bve);
      }
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);
    goto PROP_INV_CONF_MUL_TESTS;

  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    bzla_node_release(d_bzla, mul);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_udiv(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    int32_t k;
    BzlaNode *udiv, *e[2];
    BzlaSortId sort;
    BzlaBitVector *bve, *bvudiv, *bvmax, *zero, *tmp, *tmp2;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    udiv = bzla_exp_bv_udiv(d_bzla, e[0], e[1]);

    zero  = bzla_bv_new(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_UDIV_TESTS:
    /* bve / e[1] = bvudiv */
    /* bve = 1...1 and bvudiv = 0 */
    bve    = bzla_bv_copy(d_mm, bvmax);
    bvudiv = bzla_bv_new(d_mm, bw);
    check_conf_udiv_result(1, udiv, e, bvudiv, bve, use_domains);
    bzla_bv_free(d_mm, bvudiv);
    bzla_bv_free(d_mm, bve);
    /* bve < bvudiv */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      bve = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      tmp    = bzla_bv_inc(d_mm, bve);
      tmp2   = bzla_bv_dec(d_mm, bvmax);
      bvudiv = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      check_conf_udiv_result(1, udiv, e, bvudiv, bve, use_domains);
      bzla_bv_free(d_mm, bvudiv);
      bzla_bv_free(d_mm, bve);
    }
    /* e[0] / bve = bvudiv */
    /* bve = 0 and bvudiv < 1...1 */
    for (k = 0; k < 10; k++)
    {
      bve    = bzla_bv_new(d_mm, bw);
      tmp    = bzla_bv_dec(d_mm, bvmax);
      bvudiv = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      check_conf_udiv_result(0, udiv, e, bvudiv, bve, use_domains);
      bzla_bv_free(d_mm, bvudiv);
      bzla_bv_free(d_mm, bve);
    }
    /* bvudiv = 1...1 and bve > 1 */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      bvudiv = bzla_bv_copy(d_mm, bvmax);
      tmp    = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      bve    = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(d_mm, tmp);
      check_conf_udiv_result(0, udiv, e, bvudiv, bve, use_domains);
      bzla_bv_free(d_mm, bvudiv);
      bzla_bv_free(d_mm, bve);
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_INV_CONF_UDIV_TESTS;
  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    bzla_bv_free(d_mm, bvmax);
    bzla_bv_free(d_mm, zero);

    bzla_node_release(d_bzla, udiv);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_urem(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    bool inv;
    int32_t k;
    BzlaNode *urem, *e[2], *curem, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *bve, *bvurem, *bvmax, *zero, *two, *tmp, *tmp2;
    BzlaSolver *slv = 0;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_urem_bv;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    urem = bzla_exp_bv_urem(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_urem_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, urem);
    }

    zero  = bzla_bv_new(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_UREM_TESTS:
    /* bve % e[1] = bvurem */
    /* bvurem = 1...1 and bve < 1...1 */
    bvurem = bzla_bv_copy(d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp   = bzla_bv_dec(d_mm, bvmax);
      bve   = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      ce    = bzla_exp_bv_const(d_bzla, bve);
      curem = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_urem(d_mm, bvurem, bve, 1);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, bve, 1, d_domains)
                : cons_urem_bv(d_bzla, urem, bvurem, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_TRUE(bzla_bv_is_zero(res));
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_mm, bvurem, bve, 1);
      res = inv ? inv_fun(d_bzla, curem, bvurem, bve, 1, d_domains)
                : cons_urem_bv(d_bzla, curem, bvurem, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_TRUE(bzla_bv_is_zero(res));
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, bve);
    }
    bzla_bv_free(d_mm, bvurem);
    /* bve < bvurem */
    for (k = 0; k < 10; k++)
    {
      tmp    = bzla_bv_inc(d_mm, zero);
      bvurem = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(d_mm, tmp);
      tmp = bzla_bv_dec(d_mm, bvurem);
      bve = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      ce    = bzla_exp_bv_const(d_bzla, bve);
      curem = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_urem(d_mm, bvurem, bve, 1);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, bve, 1, d_domains)
                : cons_urem_bv(d_bzla, urem, bvurem, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_mm, bvurem, bve, 1);
      res = inv ? inv_fun(d_bzla, curem, bvurem, bve, 1, d_domains)
                : cons_urem_bv(d_bzla, curem, bvurem, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, bve);
      bzla_bv_free(d_mm, bvurem);
    }
    /* bve > bvurem and bve - bvurem <= bvurem -> bve > 2 * bvurem */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      two    = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      tmp2   = bzla_bv_udiv(d_mm, bvmax, two);
      tmp    = bzla_bv_uint64_to_bv(d_mm, 1, bw);
      bvurem = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      tmp  = bzla_bv_inc(d_mm, bvurem);
      tmp2 = bzla_bv_mul(d_mm, bvurem, two);
      bve  = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      ce    = bzla_exp_bv_const(d_bzla, bve);
      curem = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_urem(d_mm, bvurem, bve, 1);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, bve, 1, d_domains)
                : cons_urem_bv(d_bzla, urem, bvurem, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_mm, bvurem, bve, 1);
      res = inv ? inv_fun(d_bzla, curem, bvurem, bve, 1, d_domains)
                : cons_urem_bv(d_bzla, curem, bvurem, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, two);
      bzla_bv_free(d_mm, bvurem);
      bzla_bv_free(d_mm, bve);
    }

    /* e[0] % bve = bvurem */
    /* bvurem = 1...1 and bve > 0 */
    bvurem = bzla_bv_copy(d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp   = bzla_bv_inc(d_mm, zero);
      bve   = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      ce    = bzla_exp_bv_const(d_bzla, bve);
      curem = bzla_exp_bv_urem(d_bzla, e[0], ce);
      inv   = bzla_is_inv_urem(d_mm, bvurem, bve, 0);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, bve, 0, d_domains)
                : cons_urem_bv(d_bzla, urem, bvurem, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_EQ(bzla_bv_compare(res, bvurem), 0);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_mm, bvurem, bve, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, bve, 0, d_domains)
                : cons_urem_bv(d_bzla, curem, bvurem, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_EQ(bzla_bv_compare(res, bvurem), 0);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, bve);
    }
    bzla_bv_free(d_mm, bvurem);
    /* bve > 0 and bve <= bvurem */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp    = bzla_bv_inc(d_mm, zero);
      bvurem = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      bve    = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvurem);
      ce     = bzla_exp_bv_const(d_bzla, bve);
      curem  = bzla_exp_bv_urem(d_bzla, e[0], ce);
      inv    = bzla_is_inv_urem(d_mm, bvurem, bve, 0);
      res    = inv ? inv_fun(d_bzla, urem, bvurem, bve, 0, d_domains)
                : cons_urem_bv(d_bzla, urem, bvurem, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_mm, bvurem, bve, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, bve, 0, d_domains)
                : cons_urem_bv(d_bzla, curem, bvurem, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, bvurem);
      bzla_bv_free(d_mm, bve);
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_INV_CONF_UREM_TESTS;

  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }

    bzla_bv_free(d_mm, zero);
    bzla_bv_free(d_mm, bvmax);
    bzla_node_release(d_bzla, urem);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
#else
    (void) bw;
#endif
  }

  void check_conf_concat(uint32_t bw, bool use_domains)
  {
#ifndef NDEBUG
    (void) bw;
    bool inv;
    int32_t k, cnt;
    uint32_t i, j, bws[2];
    BzlaNode *concat, *e[2], *ce[2], *cconcat[2];
    BzlaSortId sorts[2];
    BzlaBitVector *res, *bvconcat, *bve[2], *tmp[2];
    BzlaSolver *slv = 0;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_concat_bv;

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_CONCAT_TESTS:

    for (k = 0; bw > 1 && k < 10; k++)
    {
      bws[0]   = bzla_rng_pick_rand(&d_bzla->rng, 1, bw - 1);
      bws[1]   = bw - bws[0];
      sorts[0] = bzla_sort_bv(d_bzla, bw);
      sorts[1] = bzla_sort_bv(d_bzla, bw);
      e[0]     = bzla_exp_var(d_bzla, sorts[0], 0);
      e[1]     = bzla_exp_var(d_bzla, sorts[1], 0);
      concat   = bzla_exp_bv_concat(d_bzla, e[0], e[1]);
      bvconcat = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);

      if (use_domains)
      {
        assert(!d_domains);
        inv_fun   = inv_concat_bvprop;
        d_domains = bzla_hashint_map_new(d_bzla->mm);
        init_prop_domains(d_bzla, d_domains, concat);
      }

      for (j = 0; j < 2; j++)
      {
        bve[j] = bzla_bv_slice(
            d_mm, bvconcat, j ? bws[1] - 1 : bw - 1, j ? 0 : bws[1]);
        ASSERT_EQ(bzla_bv_get_width(bve[j]), bws[j]);
        tmp[j] = bzla_bv_copy(d_mm, bve[j]);
        cnt    = 0;
        while (!cnt)
        {
          for (i = 0; i < bws[j]; i++)
          {
            if (bzla_rng_pick_rand(&d_bzla->rng, 0, 5))
            {
              bzla_bv_set_bit(bve[j], i, bzla_bv_get_bit(bve[j], i) ? 0 : 1);
              cnt += 1;
            }
          }
        }
      }
      ce[0]      = bzla_exp_bv_const(d_bzla, bve[0]);
      ce[1]      = bzla_exp_bv_const(d_bzla, bve[1]);
      cconcat[0] = bzla_exp_bv_concat(d_bzla, ce[0], e[1]);
      cconcat[1] = bzla_exp_bv_concat(d_bzla, e[0], ce[1]);
      for (j = 0; j < 2; j++)
      {
        inv = bzla_is_inv_concat(d_mm, bvconcat, bve[j ? 0 : 1], j);
        res = inv ? inv_fun(
                  d_bzla, concat, bvconcat, bve[j ? 0 : 1], j, d_domains)
                  : cons_concat_bv(
                      d_bzla, concat, bvconcat, bve[j ? 0 : 1], j, d_domains);
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, tmp[j]), 0);
        bzla_bv_free(d_mm, res);
        inv = bzla_is_inv_concat(d_mm, bvconcat, bve[j ? 0 : 1], j);
        res = inv ? inv_fun(d_bzla,
                            cconcat[j ? 0 : 1],
                            bvconcat,
                            bve[j ? 0 : 1],
                            j,
                            d_domains)
                  : cons_concat_bv(d_bzla,
                                   cconcat[j ? 0 : 1],
                                   bvconcat,
                                   bve[j ? 0 : 1],
                                   j,
                                   d_domains);
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, tmp[j]), 0);
        bzla_bv_free(d_mm, res);
      }
      for (j = 0; j < 2; j++)
      {
        bzla_sort_release(d_bzla, sorts[j]);
        bzla_node_release(d_bzla, cconcat[j]);
        bzla_node_release(d_bzla, ce[j]);
        bzla_node_release(d_bzla, e[j]);
        bzla_bv_free(d_mm, bve[j]);
        bzla_bv_free(d_mm, tmp[j]);
      }

      if (use_domains)
      {
        bzla_iter_hashint_init(&iit, d_domains);
        while (bzla_iter_hashint_has_next(&iit))
        {
          bzla_bvprop_free(d_mm,
                           static_cast<BzlaBvDomain *>(
                               bzla_iter_hashint_next_data(&iit)->as_ptr));
        }
        bzla_hashint_map_delete(d_domains);
        d_domains = nullptr;
      }
      bzla_node_release(d_bzla, concat);
      bzla_bv_free(d_mm, bvconcat);
    }

    if (bzla_opt_get(d_bzla, BZLA_OPT_ENGINE) == BZLA_ENGINE_SLS) goto DONE;

    /* sls engine: only fixable if non-const inputs */
    slv         = d_bzla->slv;
    d_bzla->slv = bzla_new_sls_solver(d_bzla);
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_SLS);

    goto PROP_INV_CONF_CONCAT_TESTS;

  DONE:
    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    d_bzla->slv->api.delet(d_bzla->slv);
    d_bzla->slv = slv;
#else
    (void) bw;
#endif
  }

  BzlaMemMgr *d_mm            = nullptr;
  BzlaRNG *d_rng              = nullptr;
  BzlaIntHashTable *d_domains = nullptr;

 private:
  void check_conf_mul_result(BzlaNode *mul,
                             BzlaNode **e,
                             BzlaBitVector *bvmul,
                             BzlaBitVector *bve,
                             bool use_domains)
  {
#ifndef NDEBUG
    bool inv;
    BzlaNode *cmul[2], *ce[2];
    BzlaBitVector *res;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_mul_bv;

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_mul_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, mul);
    }

    ce[0]   = bzla_exp_bv_const(d_bzla, bve);
    ce[1]   = bzla_exp_bv_const(d_bzla, bve);
    cmul[0] = bzla_exp_bv_mul(d_bzla, ce[0], e[1]);
    cmul[1] = bzla_exp_bv_mul(d_bzla, e[0], ce[1]);

    inv = bzla_is_inv_mul(d_mm, bvmul, bve, 0);
    res = inv ? inv_fun(d_bzla, mul, bvmul, bve, 0, d_domains)
              : cons_mul_bv(d_bzla, mul, bvmul, bve, 0, d_domains);
    ASSERT_NE(res, nullptr);
    bzla_bv_free(d_mm, res);
    inv = bzla_is_inv_mul(d_mm, bvmul, bve, 0);
    res = inv ? inv_fun(d_bzla, cmul[1], bvmul, bve, 0, d_domains)
              : cons_mul_bv(d_bzla, cmul[1], bvmul, bve, 0, d_domains);
    ASSERT_NE(res, nullptr);
    if (bzla_bv_get_bit(bvmul, 0))
    {
      ASSERT_EQ(bzla_bv_get_bit(res, 0), 1u);
    }
    bzla_bv_free(d_mm, res);

    inv = bzla_is_inv_mul(d_mm, bvmul, bve, 1);
    res = inv ? inv_fun(d_bzla, mul, bvmul, bve, 1, d_domains)
              : cons_mul_bv(d_bzla, mul, bvmul, bve, 1, d_domains);
    ASSERT_NE(res, nullptr);
    bzla_bv_free(d_mm, res);
    inv = bzla_is_inv_mul(d_mm, bvmul, bve, 1);
    res = inv ? inv_fun(d_bzla, cmul[0], bvmul, bve, 1, d_domains)
              : cons_mul_bv(d_bzla, cmul[0], bvmul, bve, 1, d_domains);
    ASSERT_NE(res, nullptr);
    if (bzla_bv_get_bit(bvmul, 0))
    {
      ASSERT_EQ(bzla_bv_get_bit(res, 0), 1u);
    }
    bzla_bv_free(d_mm, res);

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }

    bzla_node_release(d_bzla, ce[0]);
    bzla_node_release(d_bzla, ce[1]);
    bzla_node_release(d_bzla, cmul[0]);
    bzla_node_release(d_bzla, cmul[1]);
#else
    (void) mul;
    (void) e;
    (void) bvmul;
    (void) bve;
#endif
  }

  void check_conf_udiv_result(uint32_t idx_x,
                              BzlaNode *udiv,
                              BzlaNode **e,
                              BzlaBitVector *bvudiv,
                              BzlaBitVector *bve,
                              bool use_domains)
  {
#ifndef NDEBUG
    bool inv;
    BzlaNode *cudiv, *ce;
    BzlaBitVector *res;
    BzlaIntHashTableIterator iit;
    BzlaPropComputeValue inv_fun = inv_udiv_bv;

    if (use_domains)
    {
      assert(!d_domains);
      inv_fun   = inv_udiv_bvprop;
      d_domains = bzla_hashint_map_new(d_bzla->mm);
      init_prop_domains(d_bzla, d_domains, udiv);
    }

    if (idx_x)
    {
      ce    = bzla_exp_bv_const(d_bzla, bve);
      cudiv = bzla_exp_bv_udiv(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_udiv(d_mm, bvudiv, bve, 1);
      res   = inv ? inv_fun(d_bzla, udiv, bvudiv, bve, 1, d_domains)
                : cons_udiv_bv(d_bzla, udiv, bvudiv, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_FALSE(bzla_bv_is_umulo(d_mm, res, bvudiv));
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_udiv(d_mm, bvudiv, bve, 1);
      res = inv ? inv_fun(d_bzla, cudiv, bvudiv, bve, 1, d_domains)
                : cons_udiv_bv(d_bzla, cudiv, bvudiv, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_FALSE(bzla_bv_is_umulo(d_mm, res, bvudiv));
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, cudiv);
      bzla_node_release(d_bzla, ce);
    }
    else
    {
      ce    = bzla_exp_bv_const(d_bzla, bve);
      cudiv = bzla_exp_bv_udiv(d_bzla, e[0], ce);
      inv   = bzla_is_inv_udiv(d_mm, bvudiv, bve, 0);
      res   = inv ? inv_fun(d_bzla, udiv, bvudiv, bve, 0, d_domains)
                : cons_udiv_bv(d_bzla, udiv, bvudiv, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_udiv(d_mm, bvudiv, bve, 0);
      res = inv ? inv_fun(d_bzla, cudiv, bvudiv, bve, 0, d_domains)
                : cons_udiv_bv(d_bzla, cudiv, bvudiv, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, cudiv);
      bzla_node_release(d_bzla, ce);
    }

    if (use_domains)
    {
      bzla_iter_hashint_init(&iit, d_domains);
      while (bzla_iter_hashint_has_next(&iit))
      {
        bzla_bvprop_free(d_mm,
                         static_cast<BzlaBvDomain *>(
                             bzla_iter_hashint_next_data(&iit)->as_ptr));
      }
      bzla_hashint_map_delete(d_domains);
      d_domains = nullptr;
    }
#else
    (void) idx_x;
    (void) udiv;
    (void) e;
    (void) bvudiv;
    (void) bve;
#endif
  }

  void check_conf_shift(uint32_t idx_x,
                        BzlaNode *shift,
                        BzlaNode **e,
                        BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                        bool (*is_inv_fun)(BzlaMemMgr *,
                                           const BzlaBitVector *,
                                           const BzlaBitVector *,
                                           uint32_t),
                        BzlaBitVector *(*inv_fun)(Bzla *,
                                                  BzlaNode *,
                                                  BzlaBitVector *,
                                                  BzlaBitVector *,
                                                  int32_t idx_x,
                                                  BzlaIntHashTable *),
                        BzlaBitVector *(*cons_fun)(Bzla *,
                                                   BzlaNode *,
                                                   BzlaBitVector *,
                                                   BzlaBitVector *,
                                                   int32_t idx_x,
                                                   BzlaIntHashTable *),
                        const char *ve,
                        const char *vshift,
                        uint64_t rvalmax)
  {
#ifndef NDEBUG
    bool inv;
    BzlaNode *cshift, *ce;
    BzlaBitVector *res, *bvshift, *bve;

    bve     = bzla_bv_char_to_bv(d_mm, ve);
    bvshift = bzla_bv_char_to_bv(d_mm, vshift);
    ce      = bzla_exp_bv_const(d_bzla, bve);
    if (idx_x)
    {
      cshift = exp_fun(d_bzla, ce, e[1]);
      inv    = is_inv_fun(d_mm, bvshift, bve, 1);
      res    = inv ? inv_fun(d_bzla, shift, bvshift, bve, 1, d_domains)
                : cons_fun(d_bzla, shift, bvshift, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_LE(bzla_bv_to_uint64(res), rvalmax);
      bzla_bv_free(d_mm, res);
      inv = is_inv_fun(d_mm, bvshift, bve, 1);
      res = inv ? inv_fun(d_bzla, cshift, bvshift, bve, 1, d_domains)
                : cons_fun(d_bzla, cshift, bvshift, bve, 1, d_domains);
      ASSERT_NE(res, nullptr);
      ASSERT_LE(bzla_bv_to_uint64(res), rvalmax);
      bzla_bv_free(d_mm, res);
    }
    else
    {
      cshift = exp_fun(d_bzla, e[0], ce);
      inv    = is_inv_fun(d_mm, bvshift, bve, 0);
      res    = inv ? inv_fun(d_bzla, shift, bvshift, bve, 0, d_domains)
                : cons_fun(d_bzla, shift, bvshift, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = is_inv_fun(d_mm, bvshift, bve, 0);
      res = inv ? inv_fun(d_bzla, shift, bvshift, bve, 0, d_domains)
                : cons_fun(d_bzla, shift, bvshift, bve, 0, d_domains);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
    }
    bzla_bv_free(d_mm, bvshift);
    bzla_bv_free(d_mm, bve);
    bzla_node_release(d_bzla, ce);
    bzla_node_release(d_bzla, cshift);
#else
    (void) idx_x;
    (void) shift;
    (void) e;
    (void) exp_fun;
    (void) inv_fun;
    (void) ve;
    (void) vshift;
    (void) rvalmax;
#endif
  }
};

/* Test if given
 * bv_x <op> bv_s = bv_t or
 * bv_s <op> bv_x = bv_t or
 * bv_x <op> bv_t
 * we can find value bv_x as result of the inverse value computation within
 * TEST_PROP_INV_COMPLETE_N_TESTS tries. */

TEST_F(TestPropInv, complete_add)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_add,
               bzla_bv_add,
               bzla_is_inv_add,
               inv_add_bv,
               inv_add_bvprop,
               false);
  check_binary(bzla_exp_bv_add,
               bzla_bv_add,
               bzla_is_inv_add,
               inv_add_bv,
               inv_add_bvprop,
               true);
#endif
}

TEST_F(TestPropInv, complete_and)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_and,
               bzla_bv_and,
               bzla_is_inv_and,
               inv_and_bv,
               inv_and_bvprop,
               false);
  check_binary(bzla_exp_bv_and,
               bzla_bv_and,
               bzla_is_inv_and,
               inv_and_bv,
               inv_and_bvprop,
               true);
#endif
}

TEST_F(TestPropInv, complete_eq)
{
#ifndef NDEBUG
  check_binary(
      bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, inv_eq_bv, inv_eq_bvprop, false);
  check_binary(
      bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, inv_eq_bv, inv_eq_bvprop, true);
#endif
}

TEST_F(TestPropInv, complete_ult)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_ult,
               bzla_bv_ult,
               bzla_is_inv_ult,
               inv_ult_bv,
               inv_ult_bvprop,
               false);
  check_binary(bzla_exp_bv_ult,
               bzla_bv_ult,
               bzla_is_inv_ult,
               inv_ult_bv,
               inv_ult_bvprop,
               true);
#endif
}

TEST_F(TestPropInv, complete_sll)
{
#ifndef NDEBUG
  check_shift(bzla_exp_bv_sll,
              bzla_bv_sll,
              bzla_is_inv_sll,
              inv_sll_bv,
              inv_sll_bvprop,
              false);
  check_shift(bzla_exp_bv_sll,
              bzla_bv_sll,
              bzla_is_inv_sll,
              inv_sll_bv,
              inv_sll_bvprop,
              true);
#endif
}

TEST_F(TestPropInv, complete_srl)
{
#ifndef NDEBUG
  check_shift(bzla_exp_bv_srl,
              bzla_bv_srl,
              bzla_is_inv_srl,
              inv_srl_bv,
              inv_srl_bvprop,
              false);
  check_shift(bzla_exp_bv_srl,
              bzla_bv_srl,
              bzla_is_inv_srl,
              inv_srl_bv,
              inv_srl_bvprop,
              true);
#endif
}

TEST_F(TestPropInv, complete_mul)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_mul,
               bzla_bv_mul,
               bzla_is_inv_mul,
               inv_mul_bv,
               inv_mul_bvprop,
               false);
  check_binary(bzla_exp_bv_mul,
               bzla_bv_mul,
               bzla_is_inv_mul,
               inv_mul_bv,
               inv_mul_bvprop,
               true);
#endif
}

TEST_F(TestPropInv, complete_udiv)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_udiv,
               bzla_bv_udiv,
               bzla_is_inv_udiv,
               inv_udiv_bv,
               inv_udiv_bvprop,
               false);
  check_binary(bzla_exp_bv_udiv,
               bzla_bv_udiv,
               bzla_is_inv_udiv,
               inv_udiv_bv,
               inv_udiv_bvprop,
               true);
#endif
}

TEST_F(TestPropInv, complete_urem)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_urem,
               bzla_bv_urem,
               bzla_is_inv_urem,
               inv_urem_bv,
               inv_urem_bvprop,
               false);
#endif
}

TEST_F(TestPropInv, complete_concat)
{
#ifndef NDEBUG
  check_binary(bzla_exp_bv_concat,
               bzla_bv_concat,
               bzla_is_inv_concat,
               inv_concat_bv,
               inv_concat_bvprop,
               false);
#endif
}

TEST_F(TestPropInv, complete_slice)
{
#ifndef NDEBUG
  uint32_t bw;
  uint64_t up, lo, i, k;
  BzlaNode *exp, *e;
  BzlaBitVector *bve, *bvexp, *res;
  BzlaSortId sort;

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
        bve   = bzla_bv_uint64_to_bv(d_mm, i, bw);
        bvexp = bzla_bv_slice(d_mm, bve, up, lo);
        for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
        {
          res = inv_slice_bv(d_bzla, exp, bvexp, bve, 0, d_domains);
          ASSERT_NE(res, nullptr);
          if (!bzla_bv_compare(res, bve)) break;
          bzla_bv_free(d_mm, res);
          res = 0;
        }
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, bve), 0);
        bzla_bv_free(d_mm, res);
        bzla_bv_free(d_mm, bvexp);
        bzla_bv_free(d_mm, bve);
      }
      bzla_node_release(d_bzla, exp);
    }
  }
  bzla_node_release(d_bzla, e);
#endif
}

TEST_F(TestPropInv, conf_and)
{
  check_conf_and(1, false);
  check_conf_and(4, false);
  check_conf_and(8, false);
  check_conf_and(1, true);
  check_conf_and(4, true);
  check_conf_and(8, true);
}

TEST_F(TestPropInv, conf_ult)
{
  check_conf_ult(1, false);
  check_conf_ult(4, false);
  check_conf_ult(8, false);
  check_conf_ult(1, true);
  check_conf_ult(4, true);
  check_conf_ult(8, true);
}

TEST_F(TestPropInv, conf_sll)
{
  check_conf_sll(2, false);
  check_conf_sll(4, false);
  check_conf_sll(8, false);
  check_conf_sll(2, true);
  check_conf_sll(4, true);
  check_conf_sll(8, true);
}

TEST_F(TestPropInv, conf_srl)
{
  check_conf_srl(2, false);
  check_conf_srl(4, false);
  check_conf_srl(8, false);
  check_conf_srl(2, true);
  check_conf_srl(4, true);
  check_conf_srl(8, true);
}

TEST_F(TestPropInv, conf_mul)
{
  check_conf_mul(1, false);
  check_conf_mul(4, false);
  check_conf_mul(8, false);
  check_conf_mul(1, true);
  check_conf_mul(4, true);
  check_conf_mul(8, true);
}

TEST_F(TestPropInv, conf_udiv)
{
  check_conf_udiv(1, false);
  check_conf_udiv(4, false);
  check_conf_udiv(8, false);
  check_conf_udiv(1, true);
  check_conf_udiv(4, true);
  check_conf_udiv(8, true);
}

TEST_F(TestPropInv, conf_urem)
{
  check_conf_urem(1, false);
  check_conf_urem(4, false);
  check_conf_urem(8, false);
}

TEST_F(TestPropInv, conf_concat)
{
  check_conf_concat(2, false);
  check_conf_concat(4, false);
  check_conf_concat(8, false);
}
