/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2020 Aina Niemetz.
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

  void clear_domains()
  {
    BzlaIntHashTableIterator iit;
    bzla_iter_hashint_init(&iit, d_domains);
    while (bzla_iter_hashint_has_next(&iit))
    {
      int32_t key = bzla_iter_hashint_next(&iit);
      bzla_bvprop_free(d_mm,
                       static_cast<BzlaBvDomain *>(
                           bzla_hashint_map_get(d_domains, key)->as_ptr));
      bzla_hashint_map_remove(d_domains, key, 0);
    }
    assert(d_domains->count == 0);
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
   * inv_fun   : The function to compute the inverse value for x given s and t.
   * exp       : The node representing the operation.
   * s         : The assignment of the other operand.
   * t         : The assignment of the output (the target value of the
   *             operation).
   * x_bv      : The expected assignment of the operand we solve for.
   * idx_x     : The index of operand 'x'.
   */
  void check_result(BzlaPropIsInv is_inv_fun,
                    BzlaPropComputeValue inv_fun,
                    BzlaNode *exp,
                    BzlaBitVector *s,
                    BzlaBitVector *t,
                    BzlaBitVector *x_bv,
                    uint32_t idx_x)
  {
    assert(is_inv_fun);
    assert(inv_fun);
    assert(exp);
    assert(bzla_node_is_regular(exp));
    assert(s);
    assert(t);
    assert(x_bv);
    assert(d_domains);

    uint64_t k;
    bool is_inv;
    BzlaBitVector *res;
    BzlaBvDomain *x = 0, *d_res_x;

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      d_res_x = 0;
      is_inv  = is_inv_fun(d_bzla, x, t, s, idx_x, &d_res_x);
      assert(is_inv);
      res = inv_fun(d_bzla, exp, t, s, idx_x, d_domains, d_res_x);
      ASSERT_NE(res, nullptr);
      if (d_res_x) bzla_bvprop_free(d_mm, d_res_x);
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    ASSERT_NE(res, nullptr);
    ASSERT_EQ(bzla_bv_compare(res, x_bv), 0);
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
   * inv_fun   : The function to compute the inverse value for x given s
   *                and t.
   */
  void check_binary(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                    BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                             const BzlaBitVector *,
                                             const BzlaBitVector *),
                    BzlaPropIsInv is_inv_fun,
                    BzlaPropComputeValue inv_fun)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *t;

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
        check_result(is_inv_fun, inv_fun, exp, s[0], t, s[1], 1);
        check_result(is_inv_fun, inv_fun, exp, s[1], t, s[0], 0);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
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
   * inv_fun      : The function to compute the inverse value for x given s
   *                and t.
   * inv_fun_const: The function to compute the inverse value for x given s
   *                and t using propagator domains.
   */
  void check_shift(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                   BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                            const BzlaBitVector *,
                                            const BzlaBitVector *),
                   BzlaPropIsInv is_inv_fun,
                   BzlaPropComputeValue inv_fun_bv)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *x;

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
        x    = bv_fun(d_mm, s[0], s[1]);
        check_result(is_inv_fun, inv_fun_bv, exp, s[0], x, s[1], 1);
        check_result(is_inv_fun, inv_fun_bv, exp, s[1], x, s[0], 0);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, x);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
  }

  /**
   * Test if for x & s = t and s & x = t, the consistent value and inverse value
   * computation always produces t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_and(uint32_t bw, bool use_domains)
  {
    (void) bw;
    bool inv;
    uint64_t i, j;
    BzlaNode *_and, *cand[2], *e[2], *ce[2];
    BzlaSortId sort;
    BzlaBitVector *bvand, *s[2], *res, *tmp, *tmp2;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv              = 0;
    BzlaPropComputeValue inv_fun = bzla_proputils_inv_and;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    _and = bzla_exp_bv_and(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      inv_fun = bzla_proputils_inv_and_const;
      bzla_prop_solver_init_domains(d_bzla, d_domains, _and);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(_and->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(_and->e[1])->id)
               ->as_ptr;
    }

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0]    = bzla_bv_uint64_to_bv(d_mm, i, bw);
      s[1]    = bzla_bv_uint64_to_bv(d_mm, i, bw);
      ce[0]   = bzla_exp_bv_const(d_bzla, s[0]);
      ce[1]   = bzla_exp_bv_const(d_bzla, s[1]);
      cand[0] = bzla_exp_bv_and(d_bzla, ce[0], e[1]);
      cand[1] = bzla_exp_bv_and(d_bzla, e[0], ce[1]);

      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        bvand = bzla_bv_uint64_to_bv(d_mm, j, bw);
        tmp   = bzla_bv_and(d_mm, s[0], bvand);
        if (bzla_bv_compare(tmp, bvand))
        {
        PROP_INV_CONF_AND_TESTS:
          /* prop engine: all conflicts are treated as fixable */
          inv = bzla_is_inv_and(d_bzla, x0, bvand, s[1], 0, 0);
          res = inv ? inv_fun(d_bzla, _and, bvand, s[1], 0, d_domains, 0)
                    : bzla_proputils_cons_and(
                        d_bzla, _and, bvand, s[1], 0, d_domains, 0);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          inv = bzla_is_inv_and(d_bzla, x0, bvand, s[1], 0, 0);
          res = inv ? inv_fun(d_bzla, cand[1], bvand, s[1], 0, d_domains, 0)
                    : bzla_proputils_cons_and(
                        d_bzla, cand[1], bvand, s[1], 0, d_domains, 0);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          /* idx_x = 0 */
          inv = bzla_is_inv_and(d_bzla, x1, bvand, s[0], 1, 0);
          res = inv ? inv_fun(d_bzla, _and, bvand, s[0], 1, d_domains, 0)
                    : bzla_proputils_cons_and(
                        d_bzla, _and, bvand, s[0], 1, d_domains, 0);
          ASSERT_NE(res, nullptr);
          tmp2 = bzla_bv_and(d_mm, bvand, res);
          ASSERT_EQ(bzla_bv_compare(tmp2, bvand), 0);
          bzla_bv_free(d_mm, res);
          bzla_bv_free(d_mm, tmp2);

          inv = bzla_is_inv_and(d_bzla, x1, bvand, s[0], 1, 0);
          res = inv ? inv_fun(d_bzla, cand[0], bvand, s[0], 1, d_domains, 0)
                    : bzla_proputils_cons_and(
                        d_bzla, cand[0], bvand, s[0], 1, d_domains, 0);
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
      bzla_bv_free(d_mm, s[0]);
      bzla_bv_free(d_mm, s[1]);
    }

    clear_domains();

    bzla_node_release(d_bzla, _and);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Test if for x < s = t and s < x = t, the consistent value and inverse value
   * computation always produces t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_ult(uint32_t bw, bool use_domains)
  {
    (void) bw;
    bool inv;
    BzlaNode *ult, *e[2], *cult, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *bvult, *s, *zero, *bvmax;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv              = 0;
    BzlaPropComputeValue inv_fun = bzla_proputils_inv_ult;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    ult = bzla_exp_bv_ult(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      inv_fun = bzla_proputils_inv_ult_const;
      bzla_prop_solver_init_domains(d_bzla, d_domains, ult);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(ult->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(ult->e[1])->id)
               ->as_ptr;
    }

    zero  = bzla_bv_new(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);
    bvult = bzla_bv_one(d_mm, 1);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_ULT_TESTS:
    /* 1...1 < e[1] */
    s   = bzla_bv_ones(d_mm, bw);
    inv = bzla_is_inv_ult(d_bzla, x1, bvult, s, 1, 0);
    res = inv ? inv_fun(d_bzla, ult, bvult, s, 1, d_domains, 0)
              : bzla_proputils_cons_ult(d_bzla, ult, bvult, s, 1, d_domains, 0);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_compare(res, zero), 0);
    bzla_bv_free(d_mm, res);
    ce   = bzla_exp_bv_const(d_bzla, s);
    cult = bzla_exp_bv_ult(d_bzla, ce, e[1]);
    inv  = bzla_is_inv_ult(d_bzla, x1, bvult, s, 1, 0);
    res =
        inv ? inv_fun(d_bzla, cult, bvult, s, 1, d_domains, 0)
            : bzla_proputils_cons_ult(d_bzla, cult, bvult, s, 1, d_domains, 0);
    ASSERT_NE(res, nullptr);
    ASSERT_GT(bzla_bv_compare(res, zero), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cult);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, s);
    /* e[0] < 0 */
    s   = bzla_bv_new(d_mm, bw);
    inv = bzla_is_inv_ult(d_bzla, x0, bvult, s, 0, 0);
    res = inv ? inv_fun(d_bzla, ult, bvult, s, 0, d_domains, 0)
              : bzla_proputils_cons_ult(d_bzla, ult, bvult, s, 0, d_domains, 0);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_compare(res, bvmax), 0);
    bzla_bv_free(d_mm, res);
    ce   = bzla_exp_bv_const(d_bzla, s);
    cult = bzla_exp_bv_ult(d_bzla, e[0], ce);
    inv  = bzla_is_inv_ult(d_bzla, x0, bvult, s, 0, 0);
    res =
        inv ? inv_fun(d_bzla, cult, bvult, s, 0, d_domains, 0)
            : bzla_proputils_cons_ult(d_bzla, cult, bvult, s, 0, d_domains, 0);
    ASSERT_NE(res, nullptr);
    ASSERT_LT(bzla_bv_compare(res, bvmax), 0);
    bzla_bv_free(d_mm, res);
    bzla_node_release(d_bzla, cult);
    bzla_node_release(d_bzla, ce);
    bzla_bv_free(d_mm, s);

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

    clear_domains();

    bzla_bv_free(d_mm, bvult);
    bzla_bv_free(d_mm, zero);
    bzla_bv_free(d_mm, bvmax);

    bzla_node_release(d_bzla, ult);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Test if for x << s = t and s << x = t, the consistent value and inverse
   * value computation always produces a value t when solved for x where the
   * shifted bits match the corresponding bits in the shifted operand.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
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
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
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
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_mul(uint32_t bw, bool use_domains)
  {
    (void) bw;
    uint32_t i, j, k, r;
    BzlaNode *mul, *e[2];
    BzlaSortId sort;
    BzlaBitVector *bvmul, *s;
    BzlaSolver *slv = 0;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    mul = bzla_exp_bv_mul(d_bzla, e[0], e[1]);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_MUL_TESTS:
    /* s = 0 but bvmul > 0 */
    s = bzla_bv_new(d_mm, bw);
    for (k = 0; k < 10; k++)
    {
      bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      while (bzla_bv_is_zero(bvmul))
      {
        bzla_bv_free(d_mm, bvmul);
        bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      }
      check_conf_mul_result(mul, bvmul, s, use_domains);
      bzla_bv_free(d_mm, bvmul);
    }
    bzla_bv_free(d_mm, s);

    /* bvmul is odd but s is even */
    for (k = 0; k < 10; k++)
    {
      bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      if (!bzla_bv_get_bit(bvmul, 0)) bzla_bv_set_bit(bvmul, 0, 1);
      s = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
      if (bzla_bv_get_bit(s, 0)) bzla_bv_set_bit(s, 0, 0);
      check_conf_mul_result(mul, bvmul, s, use_domains);
      bzla_bv_free(d_mm, bvmul);
      bzla_bv_free(d_mm, s);
    }

    /* s = 2^i and number of 0-LSBs in bvmul < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 1; bw > 1 && i < bw; i++)
      {
        s = bzla_bv_new(d_mm, bw);
        bzla_bv_set_bit(s, i, 1);
        bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        r     = bzla_rng_pick_rand(&d_bzla->rng, 0, i - 1);
        for (j = 0; j < r; j++) bzla_bv_set_bit(bvmul, j, 0);
        if (!bzla_bv_get_bit(bvmul, r)) bzla_bv_set_bit(bvmul, r, 1);
        check_conf_mul_result(mul, bvmul, s, use_domains);
        bzla_bv_free(d_mm, bvmul);
        bzla_bv_free(d_mm, s);
      }
    }

    /* s = 2^i * m and number of 0-LSBs in bvmul < i */
    for (k = 0; k < 10; k++)
    {
      for (i = 0; bw > 1 && i < 10; i++)
      {
        s = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        while (bzla_bv_power_of_two(s) >= 0)
        {
          bzla_bv_free(d_mm, s);
          s = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        }
        if (bzla_bv_get_bit(s, 0))
        {
          r = bzla_rng_pick_rand(&d_bzla->rng, 1, bw - 1);
          for (j = 0; j < r; j++) bzla_bv_set_bit(s, j, 0);
        }
        else
        {
          for (j = 0; j < bw; j++)
            if (bzla_bv_get_bit(s, j)) break;
        }
        bvmul = bzla_bv_new_random(d_mm, &d_bzla->rng, bw);
        r     = bzla_rng_pick_rand(&d_bzla->rng, 0, j - 1);
        for (j = 0; j < r; j++) bzla_bv_set_bit(bvmul, j, 0);
        if (!bzla_bv_get_bit(bvmul, r)) bzla_bv_set_bit(bvmul, r, 1);
        check_conf_mul_result(mul, bvmul, s, use_domains);
        bzla_bv_free(d_mm, bvmul);
        bzla_bv_free(d_mm, s);
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
  }

  /**
   * Given x / s = t and s / x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
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

    zero  = bzla_bv_new(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_UDIV_TESTS:
    /* s / e[1] = bvudiv */
    /* s = 1...1 and bvudiv = 0 */
    s      = bzla_bv_copy(d_mm, bvmax);
    bvudiv = bzla_bv_new(d_mm, bw);
    check_conf_udiv_result(1, udiv, bvudiv, s, use_domains);
    bzla_bv_free(d_mm, bvudiv);
    bzla_bv_free(d_mm, s);
    /* s < bvudiv */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp = bzla_bv_uint64_to_bv(d_mm, 2, bw);
      s   = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      tmp    = bzla_bv_inc(d_mm, s);
      tmp2   = bzla_bv_dec(d_mm, bvmax);
      bvudiv = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, tmp2);
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
      s      = bzla_bv_new(d_mm, bw);
      tmp    = bzla_bv_dec(d_mm, bvmax);
      bvudiv = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
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
      s      = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
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
  }

  /**
   * Given x % s = t and s % x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_urem(uint32_t bw, bool use_domains)
  {
    (void) bw;
    bool inv;
    int32_t k;
    BzlaNode *urem, *e[2], *curem, *ce;
    BzlaSortId sort;
    BzlaBitVector *res, *s, *bvurem, *bvmax, *zero, *two, *tmp, *tmp2;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv              = 0;
    BzlaPropComputeValue inv_fun = bzla_proputils_inv_urem;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    bzla_sort_release(d_bzla, sort);
    urem = bzla_exp_bv_urem(d_bzla, e[0], e[1]);

    if (use_domains)
    {
      assert(d_domains);
      inv_fun = bzla_proputils_inv_urem_const;
      bzla_prop_solver_init_domains(d_bzla, d_domains, urem);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(urem->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(urem->e[1])->id)
               ->as_ptr;
    }

    zero  = bzla_bv_new(d_mm, bw);
    bvmax = bzla_bv_ones(d_mm, bw);

    /* prop engine: all conflicts are treated as fixable */

  PROP_INV_CONF_UREM_TESTS:
    /* s % e[1] = bvurem */
    /* bvurem = 1...1 and s < 1...1 */
    bvurem = bzla_bv_copy(d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp   = bzla_bv_dec(d_mm, bvmax);
      s     = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      ce    = bzla_exp_bv_const(d_bzla, s);
      curem = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_urem(d_bzla, x1, bvurem, s, 1, 0);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, s, 1, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, urem, bvurem, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_TRUE(bzla_bv_is_zero(res));
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_bzla, x1, bvurem, s, 1, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, s, 1, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, curem, bvurem, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_TRUE(bzla_bv_is_zero(res));
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, s);
    }
    bzla_bv_free(d_mm, bvurem);
    /* s < bvurem */
    for (k = 0; k < 10; k++)
    {
      tmp    = bzla_bv_inc(d_mm, zero);
      bvurem = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      bzla_bv_free(d_mm, tmp);
      tmp = bzla_bv_dec(d_mm, bvurem);
      s   = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, zero, tmp);
      bzla_bv_free(d_mm, tmp);
      ce    = bzla_exp_bv_const(d_bzla, s);
      curem = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_urem(d_bzla, x1, bvurem, s, 1, 0);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, s, 1, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, urem, bvurem, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_bzla, x1, bvurem, s, 1, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, s, 1, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, curem, bvurem, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, s);
      bzla_bv_free(d_mm, bvurem);
    }
    /* s > bvurem and s - bvurem <= bvurem -> s > 2 * bvurem */
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
      s    = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, tmp2);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, tmp2);
      ce    = bzla_exp_bv_const(d_bzla, s);
      curem = bzla_exp_bv_urem(d_bzla, ce, e[1]);
      inv   = bzla_is_inv_urem(d_bzla, x1, bvurem, s, 1, 0);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, s, 1, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, urem, bvurem, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_bzla, x1, bvurem, s, 1, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, s, 1, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, curem, bvurem, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, two);
      bzla_bv_free(d_mm, bvurem);
      bzla_bv_free(d_mm, s);
    }

    /* e[0] % s = bvurem */
    /* bvurem = 1...1 and s > 0 */
    bvurem = bzla_bv_copy(d_mm, bvmax);
    for (k = 0; k < 10; k++)
    {
      tmp   = bzla_bv_inc(d_mm, zero);
      s     = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      ce    = bzla_exp_bv_const(d_bzla, s);
      curem = bzla_exp_bv_urem(d_bzla, e[0], ce);
      inv   = bzla_is_inv_urem(d_bzla, x0, bvurem, s, 0, 0);
      res   = inv ? inv_fun(d_bzla, urem, bvurem, s, 0, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, urem, bvurem, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_EQ(bzla_bv_compare(res, bvurem), 0);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_bzla, x0, bvurem, s, 0, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, s, 0, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, curem, bvurem, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_EQ(bzla_bv_compare(res, bvurem), 0);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, s);
    }
    bzla_bv_free(d_mm, bvurem);
    /* s > 0 and s <= bvurem */
    for (k = 0; bw > 1 && k < 10; k++)
    {
      tmp    = bzla_bv_inc(d_mm, zero);
      bvurem = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvmax);
      s      = bzla_bv_new_random_range(d_mm, &d_bzla->rng, bw, tmp, bvurem);
      ce     = bzla_exp_bv_const(d_bzla, s);
      curem  = bzla_exp_bv_urem(d_bzla, e[0], ce);
      inv    = bzla_is_inv_urem(d_bzla, x0, bvurem, s, 0, 0);
      res    = inv ? inv_fun(d_bzla, urem, bvurem, s, 0, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, urem, bvurem, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_urem(d_bzla, x0, bvurem, s, 0, 0);
      res = inv ? inv_fun(d_bzla, curem, bvurem, s, 0, d_domains, 0)
                : bzla_proputils_cons_urem(
                    d_bzla, curem, bvurem, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, curem);
      bzla_node_release(d_bzla, ce);
      bzla_bv_free(d_mm, tmp);
      bzla_bv_free(d_mm, bvurem);
      bzla_bv_free(d_mm, s);
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

    clear_domains();

    bzla_bv_free(d_mm, zero);
    bzla_bv_free(d_mm, bvmax);
    bzla_node_release(d_bzla, urem);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
  }

  /**
   * Given x o s = t and s o x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * bw            : The bit-width to use.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_concat(uint32_t bw, bool use_domains)
  {
    (void) bw;
    bool inv;
    int32_t k, cnt;
    uint32_t i, j, bws[2];
    BzlaNode *concat, *e[2], *ce[2], *cconcat[2];
    BzlaSortId sorts[2];
    BzlaBitVector *res, *bvconcat, *s[2], *tmp[2];
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaSolver *slv              = 0;
    BzlaPropComputeValue inv_fun = bzla_proputils_inv_concat;

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
        assert(d_domains);
        inv_fun = bzla_proputils_inv_concat_const;
        bzla_prop_solver_init_domains(d_bzla, d_domains, concat);
        x0 = (BzlaBvDomain *) bzla_hashint_map_get(
                 d_domains, bzla_node_real_addr(concat->e[0])->id)
                 ->as_ptr;
        x1 = (BzlaBvDomain *) bzla_hashint_map_get(
                 d_domains, bzla_node_real_addr(concat->e[1])->id)
                 ->as_ptr;
      }

      for (j = 0; j < 2; j++)
      {
        s[j] = bzla_bv_slice(
            d_mm, bvconcat, j ? bws[1] - 1 : bw - 1, j ? 0 : bws[1]);
        ASSERT_EQ(bzla_bv_get_width(s[j]), bws[j]);
        tmp[j] = bzla_bv_copy(d_mm, s[j]);
        cnt    = 0;
        while (!cnt)
        {
          for (i = 0; i < bws[j]; i++)
          {
            if (bzla_rng_pick_rand(&d_bzla->rng, 0, 5))
            {
              bzla_bv_set_bit(s[j], i, bzla_bv_get_bit(s[j], i) ? 0 : 1);
              cnt += 1;
            }
          }
        }
      }
      ce[0]      = bzla_exp_bv_const(d_bzla, s[0]);
      ce[1]      = bzla_exp_bv_const(d_bzla, s[1]);
      cconcat[0] = bzla_exp_bv_concat(d_bzla, ce[0], e[1]);
      cconcat[1] = bzla_exp_bv_concat(d_bzla, e[0], ce[1]);
      for (j = 0; j < 2; j++)
      {
        inv = bzla_is_inv_concat(
            d_bzla, j ? x1 : x0, bvconcat, s[j ? 0 : 1], j, 0);
        res = inv ? inv_fun(
                  d_bzla, concat, bvconcat, s[j ? 0 : 1], j, d_domains, 0)
                  : bzla_proputils_cons_concat(
                      d_bzla, concat, bvconcat, s[j ? 0 : 1], j, d_domains, 0);
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, tmp[j]), 0);
        bzla_bv_free(d_mm, res);
        inv = bzla_is_inv_concat(
            d_bzla, j ? x1 : x0, bvconcat, s[j ? 0 : 1], j, 0);
        res = inv ? inv_fun(d_bzla,
                            cconcat[j ? 0 : 1],
                            bvconcat,
                            s[j ? 0 : 1],
                            j,
                            d_domains,
                            0)
                  : bzla_proputils_cons_concat(d_bzla,
                                               cconcat[j ? 0 : 1],
                                               bvconcat,
                                               s[j ? 0 : 1],
                                               j,
                                               d_domains,
                                               0);
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
        bzla_bv_free(d_mm, s[j]);
        bzla_bv_free(d_mm, tmp[j]);
      }

      clear_domains();

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
  }

  BzlaMemMgr *d_mm            = nullptr;
  BzlaRNG *d_rng              = nullptr;
  BzlaIntHashTable *d_domains = nullptr;

 private:
  /**
   * Given x * s = t and s * x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * mul           : The node representing the multiplication.
   * t             : The assignment of 'mul'.
   * s             : The assignment of one of the operands of 'mul'.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_mul_result(BzlaNode *mul,
                             BzlaBitVector *t,
                             BzlaBitVector *s,
                             bool use_domains)
  {
    bool inv;
    BzlaNode *cmul[2], *ce[2];
    BzlaBitVector *res;
    BzlaBvDomain *x0 = 0, *x1 = 0, *d_res_x;
    BzlaPropIsInv is_inv_fun     = bzla_is_inv_mul;
    BzlaPropComputeValue inv_fun = bzla_proputils_inv_mul;

    if (use_domains)
    {
      assert(d_domains);
      is_inv_fun = bzla_is_inv_mul_const;
      inv_fun    = bzla_proputils_inv_mul_const;
      bzla_prop_solver_init_domains(d_bzla, d_domains, mul);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(mul->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(mul->e[1])->id)
               ->as_ptr;
    }

    ce[0]   = bzla_exp_bv_const(d_bzla, s);
    ce[1]   = bzla_exp_bv_const(d_bzla, s);
    cmul[0] = bzla_exp_bv_mul(d_bzla, ce[0], mul->e[1]);
    cmul[1] = bzla_exp_bv_mul(d_bzla, mul->e[0], ce[1]);

    d_res_x = 0;
    inv     = is_inv_fun(d_bzla, x0, t, s, 0, &d_res_x);
    res =
        inv ? inv_fun(d_bzla, mul, t, s, 0, d_domains, d_res_x)
            : bzla_proputils_cons_mul(d_bzla, mul, t, s, 0, d_domains, d_res_x);
    ASSERT_NE(res, nullptr);
    bzla_bv_free(d_mm, res);
    if (d_res_x) bzla_bvprop_free(d_mm, d_res_x);
    d_res_x = 0;
    inv     = is_inv_fun(d_bzla, x0, t, s, 0, &d_res_x);
    res     = inv ? inv_fun(d_bzla, cmul[1], t, s, 0, d_domains, d_res_x)
              : bzla_proputils_cons_mul(
                  d_bzla, cmul[1], t, s, 0, d_domains, d_res_x);
    ASSERT_NE(res, nullptr);
    if (d_res_x) bzla_bvprop_free(d_mm, d_res_x);
    if (bzla_bv_get_bit(t, 0))
    {
      ASSERT_EQ(bzla_bv_get_bit(res, 0), 1u);
    }
    bzla_bv_free(d_mm, res);

    d_res_x = 0;
    inv     = is_inv_fun(d_bzla, x1, t, s, 1, &d_res_x);
    res =
        inv ? inv_fun(d_bzla, mul, t, s, 1, d_domains, d_res_x)
            : bzla_proputils_cons_mul(d_bzla, mul, t, s, 1, d_domains, d_res_x);
    ASSERT_NE(res, nullptr);
    bzla_bv_free(d_mm, res);
    if (d_res_x) bzla_bvprop_free(d_mm, d_res_x);
    d_res_x = 0;
    inv     = is_inv_fun(d_bzla, x1, t, s, 1, &d_res_x);
    res     = inv ? inv_fun(d_bzla, cmul[0], t, s, 1, d_domains, d_res_x)
              : bzla_proputils_cons_mul(
                  d_bzla, cmul[0], t, s, 1, d_domains, d_res_x);
    ASSERT_NE(res, nullptr);
    if (bzla_bv_get_bit(t, 0))
    {
      ASSERT_EQ(bzla_bv_get_bit(res, 0), 1u);
    }
    bzla_bv_free(d_mm, res);
    if (d_res_x) bzla_bvprop_free(d_mm, d_res_x);

    clear_domains();

    bzla_node_release(d_bzla, ce[0]);
    bzla_node_release(d_bzla, ce[1]);
    bzla_node_release(d_bzla, cmul[0]);
    bzla_node_release(d_bzla, cmul[1]);
  }

  /**
   * Given x / s = t and s / x = t, test if the consistent value and inverse
   * value computation always produces a 'legal' value t when solved for x.
   *
   * udiv          : The node representing the unsigned division.
   * t             : The assignment of 'udiv'.
   * s             : The assignment of one of the operands of udiv.
   * use_domains   : True if this check should be performed using propagator
   *                 domains (inv_fun_const).
   */
  void check_conf_udiv_result(uint32_t idx_x,
                              BzlaNode *udiv,
                              BzlaBitVector *t,
                              BzlaBitVector *s,
                              bool use_domains)
  {
    bool inv;
    BzlaNode *cudiv, *ce;
    BzlaBitVector *res;
    BzlaBvDomain *x0 = 0, *x1 = 0;
    BzlaPropComputeValue inv_fun = bzla_proputils_inv_udiv;

    if (use_domains)
    {
      assert(d_domains);
      inv_fun = bzla_proputils_inv_udiv_const;
      bzla_prop_solver_init_domains(d_bzla, d_domains, udiv);
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(udiv->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(udiv->e[1])->id)
               ->as_ptr;
    }

    if (idx_x)
    {
      ce    = bzla_exp_bv_const(d_bzla, s);
      cudiv = bzla_exp_bv_udiv(d_bzla, ce, udiv->e[1]);
      inv   = bzla_is_inv_udiv(d_bzla, x1, t, s, 1, 0);
      res   = inv ? inv_fun(d_bzla, udiv, t, s, 1, d_domains, 0)
                : bzla_proputils_cons_udiv(d_bzla, udiv, t, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_FALSE(bzla_bv_is_umulo(d_mm, res, t));
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_udiv(d_bzla, x1, t, s, 1, 0);
      res =
          inv ? inv_fun(d_bzla, cudiv, t, s, 1, d_domains, 0)
              : bzla_proputils_cons_udiv(d_bzla, cudiv, t, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_FALSE(bzla_bv_is_umulo(d_mm, res, t));
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, cudiv);
      bzla_node_release(d_bzla, ce);
    }
    else
    {
      ce    = bzla_exp_bv_const(d_bzla, s);
      cudiv = bzla_exp_bv_udiv(d_bzla, udiv->e[0], ce);
      inv   = bzla_is_inv_udiv(d_bzla, x0, t, s, 0, 0);
      res   = inv ? inv_fun(d_bzla, udiv, t, s, 0, d_domains, 0)
                : bzla_proputils_cons_udiv(d_bzla, udiv, t, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = bzla_is_inv_udiv(d_bzla, x0, t, s, 0, 0);
      res =
          inv ? inv_fun(d_bzla, cudiv, t, s, 0, d_domains, 0)
              : bzla_proputils_cons_udiv(d_bzla, cudiv, t, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      bzla_node_release(d_bzla, cudiv);
      bzla_node_release(d_bzla, ce);
    }

    clear_domains();
  }

  /**
   * Given x <> s = t and s <> x = t where <> is a shift operator, test if the
   * consistent value and inverse value computation always produces a 'legal'
   * value t when solved for x.
   *
   * shift     : The node representing the shift operation.
   * s_vals    : A char* array representing the values for all operands of <>.
   * t_val     : A char* representation of the target value of <>.
   * rvalmax   : The maximum value of the inverse/consistent value.
   */
  void check_conf_shift(uint32_t idx_x,
                        BzlaNode *shift,
                        std::string op,
                        const char *s_vals,
                        const char *t_val,
                        uint64_t rvalmax,
                        bool use_domains)
  {
    assert(d_domains);

    bool inv;
    BzlaNode *cshift, *ce;
    BzlaBitVector *res, *t, *s;
    BzlaBvDomain *x0 = 0, *x1 = 0;

    /* The function to create a node representing the shift operation. */
    BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *);
    /* The function to test if given operator is invertible w.r.t.  s and t. */
    BzlaPropIsInv is_inv_fun;
    /* The function to compute the inverse value for x. */
    BzlaPropComputeValue inv_fun;
    /* The function to compute the consistent value for x. */
    BzlaPropComputeValue cons_fun;

    if (op == "sll")
    {
      exp_fun    = bzla_exp_bv_sll;
      is_inv_fun = use_domains ? bzla_is_inv_sll_const : bzla_is_inv_sll;
      inv_fun =
          use_domains ? bzla_proputils_inv_sll : bzla_proputils_inv_sll_const;
      cons_fun = bzla_proputils_cons_sll;
    }
    else
    {
      assert(op == "srl");
      exp_fun    = bzla_exp_bv_srl;
      is_inv_fun = use_domains ? bzla_is_inv_srl_const : bzla_is_inv_srl;
      inv_fun =
          use_domains ? bzla_proputils_inv_srl : bzla_proputils_inv_srl_const;
      cons_fun = bzla_proputils_cons_srl;
    }

    if (use_domains)
    {
      x0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(shift->e[0])->id)
               ->as_ptr;
      x1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(shift->e[1])->id)
               ->as_ptr;
    }

    s  = bzla_bv_char_to_bv(d_mm, s_vals);
    t  = bzla_bv_char_to_bv(d_mm, t_val);
    ce = bzla_exp_bv_const(d_bzla, s);
    if (idx_x)
    {
      cshift = exp_fun(d_bzla, ce, shift->e[1]);
      inv    = is_inv_fun(d_bzla, x1, t, s, 1, 0);
      res    = inv ? inv_fun(d_bzla, shift, t, s, 1, d_domains, 0)
                : cons_fun(d_bzla, shift, t, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_LE(bzla_bv_to_uint64(res), rvalmax);
      bzla_bv_free(d_mm, res);
      inv = is_inv_fun(d_bzla, x1, t, s, 1, 0);
      res = inv ? inv_fun(d_bzla, cshift, t, s, 1, d_domains, 0)
                : cons_fun(d_bzla, cshift, t, s, 1, d_domains, 0);
      ASSERT_NE(res, nullptr);
      ASSERT_LE(bzla_bv_to_uint64(res), rvalmax);
      bzla_bv_free(d_mm, res);
    }
    else
    {
      cshift = exp_fun(d_bzla, shift->e[0], ce);
      inv    = is_inv_fun(d_bzla, x0, t, s, 0, 0);
      res    = inv ? inv_fun(d_bzla, shift, t, s, 0, d_domains, 0)
                : cons_fun(d_bzla, shift, t, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
      inv = is_inv_fun(d_bzla, x0, t, s, 0, 0);
      res = inv ? inv_fun(d_bzla, shift, t, s, 0, d_domains, 0)
                : cons_fun(d_bzla, shift, t, s, 0, d_domains, 0);
      ASSERT_NE(res, nullptr);
      bzla_bv_free(d_mm, res);
    }
    bzla_bv_free(d_mm, t);
    bzla_bv_free(d_mm, s);
    bzla_node_release(d_bzla, ce);
    bzla_node_release(d_bzla, cshift);
  }
};

/*------------------------------------------------------------------------*/

class TestPropInvConst : public TestPropInv
{
 protected:
  void SetUp() override
  {
    TestPropInv::SetUp();

    bzla_opt_set(d_bzla, BZLA_OPT_PROP_CONST_BITS, 1);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_DOMAINS, 1);
  }

  /** Helper for check_result_aux. */
  void check_result_n_tests(BzlaPropIsInv is_inv_fun,
                            BzlaPropComputeValue inv_fun,
                            BzlaNode *exp,
                            BzlaBitVector *s,
                            BzlaBitVector *t,
                            BzlaBitVector *x_bv,
                            uint32_t idx_x)
  {
    uint64_t k;
    bool is_inv;
    BzlaBitVector *res;
    BzlaBvDomain *d_res_x;

    assert(bzla_hashint_map_contains(d_domains,
                                     bzla_node_real_addr(exp->e[idx_x])->id));
    BzlaBvDomain *x = (BzlaBvDomain *) bzla_hashint_map_get(
                          d_domains, bzla_node_real_addr(exp->e[idx_x])->id)
                          ->as_ptr;

    for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
    {
      d_res_x = 0;
      is_inv  = is_inv_fun(d_bzla, x, t, s, idx_x, &d_res_x);
      assert(is_inv);
      res = inv_fun(d_bzla, exp, t, s, idx_x, d_domains, d_res_x);
      if (d_res_x) bzla_bvprop_free(d_mm, d_res_x);
      ASSERT_NE(res, nullptr);
      if (!bzla_bv_compare(res, x_bv)) break;
      bzla_bv_free(d_mm, res);
      res = 0;
    }
    ASSERT_NE(res, nullptr);
    ASSERT_EQ(bzla_bv_compare(res, x_bv), 0);
    bzla_bv_free(d_mm, res);
  }

  /** Helper for check_result. */
  void check_result_aux(BzlaPropIsInv is_inv_fun,
                        BzlaPropComputeValue inv_fun,
                        BzlaNode *exp,
                        BzlaBitVector *s,
                        BzlaBitVector *t,
                        BzlaBitVector *x_bv,
                        uint32_t idx_x,
                        std::vector<uint32_t> &fixed_idx)
  {
    BzlaBvDomain *x = 0;

    bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
    assert(bzla_hashint_map_contains(d_domains,
                                     bzla_node_real_addr(exp->e[idx_x])->id));
    x = (BzlaBvDomain *) bzla_hashint_map_get(
            d_domains, bzla_node_real_addr(exp->e[idx_x])->id)
            ->as_ptr;
    assert(!bzla_bvprop_has_fixed_bits(d_mm, x));

    for (uint32_t i : fixed_idx)
    {
      bzla_bvprop_fix_bit(x, i, bzla_bv_get_bit(x_bv, i));
    }

    check_result_n_tests(is_inv_fun, inv_fun, exp, s, t, x_bv, idx_x);
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
   * is_inv_fun : The function to test if given operator is invertible with
   *              respect to s and t.
   * inv_fun    : The function to compute the inverse value for x given s and t.
   * exp        : The node representing the operation.
   * s          : The assignment of the other operand.
   * t          : The assignment of the output (the target value of the
   *              operation).
   * x_bv       : The expected assignment of the operand we solve for.
   * idx_x      : The index of operand 'x'.
   */
  void check_result(BzlaPropIsInv is_inv_fun,
                    BzlaPropComputeValue inv_fun,
                    BzlaNode *exp,
                    BzlaBitVector *s,
                    BzlaBitVector *t,
                    BzlaBitVector *x_bv,
                    uint32_t idx_x)
  {
    assert(is_inv_fun);
    assert(inv_fun);
    assert(exp);
    assert(bzla_node_is_regular(exp));
    assert(s);
    assert(t);
    assert(x_bv);
    assert(d_domains);

    std::vector<uint32_t> fixed_idx;

    /* set one bit */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      fixed_idx.push_back(i);
      check_result_aux(is_inv_fun, inv_fun, exp, s, t, x_bv, idx_x, fixed_idx);
      fixed_idx.clear();
    }

    /* set two bits */
    for (uint32_t i = 0, bw = bzla_bv_get_width(x_bv); i < bw; ++i)
    {
      for (uint32_t j = i + 1, bw = bzla_bv_get_width(x_bv); j < bw; ++j)
      {
        fixed_idx.push_back(i);
        fixed_idx.push_back(j);
        check_result_aux(
            is_inv_fun, inv_fun, exp, s, t, x_bv, idx_x, fixed_idx);
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
          check_result_aux(
              is_inv_fun, inv_fun, exp, s, t, x_bv, idx_x, fixed_idx);
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
   * exp_fun    : The function to create the node representing operation <>.
   * bv_fun     : The function to create the bit-vector result of operation
   *              s0 <> s1.
   * is_inv_fun : The function to test if given operator is invertible with
   *              respect to s and t.
   * inv_fun    : The function to compute the inverse value for x given s
   *              and t considering const bits in x.
   */
  void check_binary(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                    BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                             const BzlaBitVector *,
                                             const BzlaBitVector *),
                    BzlaPropIsInv is_inv_fun,
                    BzlaPropComputeValue inv_fun)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *t;

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
        check_result(is_inv_fun, inv_fun, exp, s[0], t, s[1], 1);
        check_result(is_inv_fun, inv_fun, exp, s[1], t, s[0], 0);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, exp);
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
   * inv_fun      : The function to compute the inverse value for x given s
   *                and t.
   * inv_fun_const: The function to compute the inverse value for x given s
   *                and t using propagator domains.
   */
  void check_shift(BzlaNode *(*exp_fun)(Bzla *, BzlaNode *, BzlaNode *),
                   BzlaBitVector *(*bv_fun)(BzlaMemMgr *,
                                            const BzlaBitVector *,
                                            const BzlaBitVector *),
                   BzlaPropIsInv is_inv_fun,
                   BzlaPropComputeValue inv_fun_bv)
  {
    uint32_t bw;
    uint64_t i, j;
    BzlaNode *exp, *e[2];
    BzlaSortId sort;
    BzlaBitVector *s[2], *x;

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
        x    = bv_fun(d_mm, s[0], s[1]);
        check_result(is_inv_fun, inv_fun_bv, exp, s[0], x, s[1], 1);
        check_result(is_inv_fun, inv_fun_bv, exp, s[1], x, s[0], 0);
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, x);
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
/* Regular inverse value computation, no const bits, no propagator domains.   */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropInv, complete_add)
{
  check_binary(
      bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, bzla_proputils_inv_add);
}

TEST_F(TestPropInv, complete_and)
{
  check_binary(
      bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, bzla_proputils_inv_and);
}

TEST_F(TestPropInv, complete_eq)
{
  check_binary(bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq);
}

TEST_F(TestPropInv, complete_ult)
{
  check_binary(
      bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, bzla_proputils_inv_ult);
}

TEST_F(TestPropInv, complete_sll)
{
  check_shift(
      bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, bzla_proputils_inv_sll);
}

TEST_F(TestPropInv, complete_srl)
{
  check_shift(
      bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, bzla_proputils_inv_srl);
}

TEST_F(TestPropInv, complete_mul)
{
  check_binary(
      bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, bzla_proputils_inv_mul);
}

TEST_F(TestPropInv, complete_udiv)
{
  check_binary(bzla_exp_bv_udiv,
               bzla_bv_udiv,
               bzla_is_inv_udiv,
               bzla_proputils_inv_udiv);
}

TEST_F(TestPropInv, complete_urem)
{
  check_binary(bzla_exp_bv_urem,
               bzla_bv_urem,
               bzla_is_inv_urem,
               bzla_proputils_inv_urem);
}

TEST_F(TestPropInv, complete_concat)
{
  check_binary(bzla_exp_bv_concat,
               bzla_bv_concat,
               bzla_is_inv_concat,
               bzla_proputils_inv_concat);
}

TEST_F(TestPropInv, complete_slice)
{
  uint32_t bw;
  uint64_t up, lo, i, k;
  BzlaNode *exp, *e;
  BzlaBitVector *s, *x, *res;
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
        s = bzla_bv_uint64_to_bv(d_mm, i, bw);
        x = bzla_bv_slice(d_mm, s, up, lo);
        for (k = 0, res = 0; k < TEST_PROP_INV_COMPLETE_N_TESTS; k++)
        {
          res = bzla_proputils_inv_slice(d_bzla, exp, x, s, 0, d_domains, 0);
          ASSERT_NE(res, nullptr);
          if (!bzla_bv_compare(res, s)) break;
          bzla_bv_free(d_mm, res);
          res = 0;
        }
        ASSERT_NE(res, nullptr);
        ASSERT_EQ(bzla_bv_compare(res, s), 0);
        bzla_bv_free(d_mm, res);
        bzla_bv_free(d_mm, x);
        bzla_bv_free(d_mm, s);
      }
      bzla_node_release(d_bzla, exp);
    }
  }
  bzla_node_release(d_bzla, e);
}

/* -------------------------------------------------------------------------- */
/* Inverse value computation with propagator domains, no const bits.          */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropInvConst, complete_add_const)
{
  check_binary(bzla_exp_bv_add,
               bzla_bv_add,
               bzla_is_inv_add_const,
               bzla_proputils_inv_add_const);
}

TEST_F(TestPropInvConst, complete_and_const)
{
  check_binary(bzla_exp_bv_and,
               bzla_bv_and,
               bzla_is_inv_and_const,
               bzla_proputils_inv_and_const);
}

TEST_F(TestPropInvConst, complete_eq_const)
{
  check_binary(bzla_exp_eq,
               bzla_bv_eq,
               bzla_is_inv_eq_const,
               bzla_proputils_inv_eq_const);
}

TEST_F(TestPropInvConst, complete_ult_const)
{
  check_binary(bzla_exp_bv_ult,
               bzla_bv_ult,
               bzla_is_inv_ult_const,
               bzla_proputils_inv_ult_const);
}

TEST_F(TestPropInvConst, complete_mul_const)
{
  check_binary(bzla_exp_bv_mul,
               bzla_bv_mul,
               bzla_is_inv_mul_const,
               bzla_proputils_inv_mul_const);
}

TEST_F(TestPropInvConst, complete_sll_const)
{
  check_shift(bzla_exp_bv_sll,
              bzla_bv_sll,
              bzla_is_inv_sll_const,
              bzla_proputils_inv_sll_const);
}

#if 0
TEST_F (TestPropInvConst, complete_srl_const)
{
  check_shift (bzla_exp_bv_srl,
               bzla_bv_srl,
               bzla_is_inv_srl_const,
               bzla_proputils_inv_srl_const);
}

TEST_F (TestPropInvConst, complete_udiv_const)
{
  check_binary (bzla_exp_bv_udiv,
                bzla_bv_udiv,
                bzla_is_inv_udiv_const,
                bzla_proputils_inv_udiv_const);
}

TEST_F (TestPropInvConst, complete_urem_const)
{
  check_binary (bzla_exp_bv_urem,
                bzla_bv_urem,
                bzla_is_inv_urem_const,
                bzla_proputils_inv_urem_const);
}

TEST_F (TestPropInvConst, complete_concat_const)
{
  check_binary (bzla_exp_bv_concat,
                bzla_bv_concat,
                bzla_is_inv_concat_const,
                bzla_proputils_inv_concat_const);
}

TEST_F (TestPropInvConst, complete_slice)
{
}
#endif

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
