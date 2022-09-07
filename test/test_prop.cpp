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
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlaproputils.h"
#include "bzlaslvprop.h"
#include "utils/bzlahashint.h"
#include "utils/bzlautil.h"
}

#define TEST_PROP_LOG_LEVEL 0
#define TEST_PROP_LOG(FMT, ...) \
  if (TEST_PROP_LOG_LEVEL > 0)  \
  {                             \
    printf(FMT, ##__VA_ARGS__); \
  }

class TestProp : public TestBzla
{
 protected:
  static constexpr int32_t TEST_PROP_COMPLETE_BW      = 4;
  static constexpr int32_t TEST_PROP_COMPLETE_N_TESTS = 1000;

  void SetUp() override
  {
    TestBzla::SetUp();

    d_bzla->slv       = bzla_new_prop_solver(d_bzla);
    d_bzla->slv->bzla = d_bzla;
    d_mm              = d_bzla->mm;
    d_rng             = d_bzla->rng;
    d_slv             = BZLA_PROP_SOLVER(d_bzla);
    d_domains         = BZLA_PROP_SOLVER(d_bzla)->domains;

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE, 1000);
    bzla_opt_set(d_bzla, BZLA_OPT_RW_LEVEL, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_RW_SORT_EXP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_INCREMENTAL, 1);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_EQ_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_AND_FLIP, 0);
    // bzla_opt_set (d_bzla, BZLA_OPT_LOGLEVEL, 2);
  }

  void clear_domains()
  {
    BzlaIntHashTableIterator it;
    bzla_iter_hashint_init(&it, d_domains);
    while (bzla_iter_hashint_has_next(&it))
    {
      BzlaHashTableData *data = bzla_iter_hashint_next_data(&it);
      BzlaBvDomain *d         = static_cast<BzlaBvDomain *>(data->as_ptr);
      bzla_bvdomain_free(d_mm, d);
    }
    bzla_hashint_map_clear(d_domains);
    assert(d_domains->count == 0);
  }

  /**
   * Given an operator and assignments 's' (for the other operand) and 't' (for
   * the target value of the operation) with a solution 'x' (for the operand to
   * solve for), test if a solution can be found within 'n' propagation steps /
   * moves. If n = 1, we test if it is found within one propagation step, and
   * else we test if it is found within moves.
   *
   * n         : The number of propagation steps expected to be required to
   *             find a solution.
   * idx_x     : The index of operand 'x'.
   * bw        : The bit-width to test for.
   * s         : The assignment of the other operand.
   * x         : The assignment of the operand we solve for.
   * t         : The assignment of the output (the target value of the
   *             operation).
   * create_exp: The function to create a node node(x) <> node(s) or
   *             node(s) <> node(t) for operator <>.
   * create_bv : The function to create a bit-vector t = x <> s or t = s <> t
   *             for operator <>.
   * is_inv_fun: The function to test if given operator is invertible with
   *             respect to s and t.
   * val_fun   : The function to compute the value for x given s and t.
   */
  void prop_complete_binary_idx(
      uint32_t n,
      int32_t pos_x,
      uint32_t bw,
      BzlaBitVector *s,
      BzlaBitVector *x,
      BzlaBitVector *t,
      BzlaNode *(*create_exp)(Bzla *, BzlaNode *, BzlaNode *),
      BzlaBitVector *(*create_bv)(BzlaMemMgr *,
                                  const BzlaBitVector *,
                                  const BzlaBitVector *),
      BzlaPropIsInvFun is_inv_fun,
      BzlaPropComputeValueFun val_fun)
  {
    bool is_inv;
    int32_t i, pos_s, sat_res;
    BzlaNode *e[2], *exp, *val, *eq, *children[2];
    BzlaBitVector *s_tmp[2], *t_tmp, *res[2], *tmp;
    BzlaBvDomain *d_x, *d_s;
    BzlaSortId sort;
    BzlaPropInfo pi;

    memset(&pi, 0, sizeof(BzlaPropInfo));

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    exp  = create_exp(d_bzla, e[0], e[1]);
    val  = bzla_exp_bv_const(d_bzla, t);
    eq   = bzla_exp_eq(d_bzla, exp, val);

    pos_s = pos_x ? 0 : 1;

    bzla_synthesize_exp(d_bzla, eq, 0);
    bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
    if (bzla_is_bv_sra(d_bzla, exp, &children[0], &children[1]))
    {
      assert(bzla_hashint_map_contains(d_domains,
                                       bzla_node_real_addr(children[0])->id));
      assert(bzla_hashint_map_contains(d_domains,
                                       bzla_node_real_addr(children[1])->id));

      d_x = (BzlaBvDomain *) bzla_hashint_map_get(
                d_domains, bzla_node_real_addr(children[pos_x])->id)
                ->as_ptr;
      d_s = (BzlaBvDomain *) bzla_hashint_map_get(
                d_domains, bzla_node_real_addr(children[pos_s])->id)
                ->as_ptr;
    }
    else
    {
      assert((BzlaBvDomain *) bzla_hashint_map_get(
          d_domains, bzla_node_real_addr(exp->e[pos_x])->id));
      assert((BzlaBvDomain *) bzla_hashint_map_get(
          d_domains, bzla_node_real_addr(exp->e[pos_s])->id));
      d_x = (BzlaBvDomain *) bzla_hashint_map_get(
                d_domains, bzla_node_real_addr(exp->e[pos_x])->id)
                ->as_ptr;
      d_s = (BzlaBvDomain *) bzla_hashint_map_get(
                d_domains, bzla_node_real_addr(exp->e[pos_s])->id)
                ->as_ptr;
    }
    assert(d_x);
    assert(d_s);

    s_tmp[pos_x] = bzla_bv_new_random(d_mm, d_rng, bw);
    s_tmp[pos_s] =
        n == 1 ? bzla_bv_copy(d_mm, s) : bzla_bv_new_random(d_mm, d_rng, bw);
    t_tmp = create_bv(d_mm, s_tmp[0], s_tmp[1]);

    /* init bv model */
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_s], s_tmp[pos_s]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_x], s_tmp[pos_x]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, t_tmp);

    TEST_PROP_LOG("pos_x %d s_tmp[0] %s s_tmp[1] %s target %s\n",
                  pos_x,
                  bzla_bv_to_char(d_mm, s_tmp[0]),
                  bzla_bv_to_char(d_mm, s_tmp[1]),
                  bzla_bv_to_char(d_mm, t));

    pi.exp          = exp;
    pi.bv[pos_x]    = s_tmp[pos_x];
    pi.bv[pos_s]    = s;
    pi.bvd[pos_x]   = d_x;
    pi.bvd[pos_s]   = d_s;
    pi.target_value = t;

    /* -> first test local completeness  */
    /* we must find a solution within n move(s) */
    pi.pos_x = pos_x;
    pi.res_x = nullptr;
    is_inv   = is_inv_fun(d_bzla, &pi);
    ASSERT_TRUE(is_inv);
    res[pos_x] = val_fun(d_bzla, &pi);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
    pi.res_x = nullptr;
    ASSERT_NE(res[pos_x], nullptr);

    pi.pos_x     = pos_s;
    pi.bv[pos_x] = res[pos_x];
    pi.res_x     = nullptr;
    is_inv       = is_inv_fun(d_bzla, &pi);
    ASSERT_TRUE(is_inv);
    res[pos_s] = n == 1 ? bzla_bv_copy(d_mm, s) : val_fun(d_bzla, &pi);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
    ASSERT_NE(res[pos_s], nullptr);
    /* Note: this is also tested within the inverse function(s) */
    tmp = create_bv(d_mm, res[0], res[1]);
    ASSERT_EQ(bzla_bv_compare(tmp, t), 0);
    bzla_bv_free(d_mm, tmp);
    bzla_bv_free(d_mm, res[0]);
    bzla_bv_free(d_mm, res[1]);
    /* try to find the exact given solution */
    if (n == 1)
    {
      for (i = 0, res[pos_x] = 0; i < TEST_PROP_COMPLETE_N_TESTS; i++)
      {
        pi.pos_x     = pos_x;
        pi.bv[pos_x] = s_tmp[pos_x];
        pi.res_x     = nullptr;
        is_inv       = is_inv_fun(d_bzla, &pi);
        assert(is_inv);
        res[pos_x] = val_fun(d_bzla, &pi);
        ASSERT_NE(res[pos_x], nullptr);
        if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
        if (!bzla_bv_compare(res[pos_x], x)) break;
        bzla_bv_free(d_mm, res[pos_x]);
        res[pos_x] = nullptr;
      }
      ASSERT_NE(res[pos_x], nullptr);
      ASSERT_EQ(bzla_bv_compare(res[pos_x], x), 0);
      bzla_bv_free(d_mm, res[pos_x]);
    }

    /* -> then test completeness of the whole propagation algorithm
     *    (we must find a solution within n move(s)) */
    ((BzlaPropSolver *) d_bzla->slv)->stats.moves = 0;
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_RANDOM_INPUT, 0);
    bzla_assume_exp(d_bzla, eq);
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_s], s_tmp[pos_s]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_x], s_tmp[pos_x]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, t_tmp);
    bzla_bv_free(d_mm, s_tmp[0]);
    bzla_bv_free(d_mm, s_tmp[1]);
    bzla_bv_free(d_mm, t_tmp);
    bzla_node_release(d_bzla, eq);
    bzla_node_release(d_bzla, val);
    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_sort_release(d_bzla, sort);
    clear_domains();
    sat_res = bzla_prop_solver_sat(d_bzla);
    ASSERT_EQ(sat_res, BZLA_RESULT_SAT);
    TEST_PROP_LOG(
        "moves %u n %u\n", ((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    assert(((BzlaPropSolver *) d_bzla->slv)->stats.moves <= n);
    ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    bzla_reset_incremental_usage(d_bzla);
  }

  /**
   * Same as prop_complete_binary_idx but for cond.
   *
   * n         : The number of propagation steps expected to be required to
   *             find a solution.
   * idx_x     : The index of operand 'x'.
   * bw        : The bit-width to test for.
   * s0, s1    : The assignment of other two operands:
   *               - for idx_x = 0, assignment s0 is for e[1] and s1 for e[2]
   *               - for idx_x = 1, assignment s0 is for e[0] and s1 for e[2]
   *               - for idx_x = 2, assignment s0 is for e[0] and s1 for e[1]
   * x         : The assignment of the operand we solve for.
   * t         : The assignment of the output (the target value of the
   *             operation).
   * const_bits: True to test with const bits.
   */
  void prop_complete_cond_idx(uint32_t n,
                              uint32_t pos_x,
                              uint32_t bw,
                              BzlaBitVector *s0,
                              BzlaBitVector *s1,
                              BzlaBitVector *x,
                              BzlaBitVector *t,
                              bool const_bits)
  {
    assert(const_bits);  // else not supported yet because of special handling
                         // for cond (TODO)

    bool is_inv;
    uint32_t i, pos_s0, pos_s1;
    int32_t sat_res;
    BzlaNode *e[3], *exp, *val, *eq;
    BzlaBitVector *s_tmp[3], *x_tmp, *res[3], *tmp;
    BzlaBvDomain *d_x, *d_s0, *d_s1;
    BzlaSortId sort, sort1;
    BzlaPropIsInvFun is_inv_fun;
    BzlaPropComputeValueFun val_fun;
    BzlaPropInfo pi;

    memset(&pi, 0, sizeof(BzlaPropInfo));

    if (const_bits)
    {
      is_inv_fun = bzla_is_inv_cond_const;
      val_fun    = bzla_proputils_inv_cond_const;
    }
    else
    {
      is_inv_fun = bzla_is_inv_cond;
      val_fun    = bzla_proputils_inv_cond;
    }

    sort  = bzla_sort_bv(d_bzla, bw);
    sort1 = bzla_sort_bv(d_bzla, 1);
    e[0]  = bzla_exp_var(d_bzla, sort1, 0);
    e[1]  = bzla_exp_var(d_bzla, sort, 0);
    e[2]  = bzla_exp_var(d_bzla, sort, 0);
    exp   = bzla_exp_cond(d_bzla, e[0], e[1], e[2]);
    val   = bzla_exp_bv_const(d_bzla, t);
    eq    = bzla_exp_eq(d_bzla, exp, val);

    if (pos_x == 0)
    {
      pos_s0 = 1;
      pos_s1 = 2;
    }
    else if (pos_x == 1)
    {
      pos_s0 = 0;
      pos_s1 = 2;
    }
    else
    {
      pos_s0 = 0;
      pos_s1 = 1;
    }

    bzla_synthesize_exp(d_bzla, eq, 0);
    bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
    assert((BzlaBvDomain *) bzla_hashint_map_get(
        d_domains, bzla_node_real_addr(exp->e[pos_x])->id));
    d_x = (BzlaBvDomain *) bzla_hashint_map_get(
              d_domains, bzla_node_real_addr(exp->e[pos_x])->id)
              ->as_ptr;
    assert(d_x);
    assert(bzla_bv_get_width(x) == bzla_bvdomain_get_width(d_x));

    assert((BzlaBvDomain *) bzla_hashint_map_get(
        d_domains, bzla_node_real_addr(exp->e[pos_s0])->id));
    d_s0 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[pos_s0])->id)
               ->as_ptr;
    assert(d_s0);

    assert((BzlaBvDomain *) bzla_hashint_map_get(
        d_domains, bzla_node_real_addr(exp->e[pos_s1])->id));
    d_s1 = (BzlaBvDomain *) bzla_hashint_map_get(
               d_domains, bzla_node_real_addr(exp->e[pos_s1])->id)
               ->as_ptr;
    assert(d_s1);

    s_tmp[pos_x] = bzla_bv_new_random(d_mm, d_rng, pos_x ? bw : 1);
    if (n == 2)
    {
      s_tmp[pos_s0] = bzla_bv_copy(d_mm, s0);
      s_tmp[pos_s1] = bzla_bv_copy(d_mm, s1);
    }
    else
    {
      s_tmp[pos_s0] = bzla_bv_new_random(d_mm, d_rng, pos_x ? 1 : bw);
      s_tmp[pos_s1] = bzla_bv_new_random(d_mm, d_rng, bw);
    }
    x_tmp = bzla_bv_ite(d_mm, s_tmp[0], s_tmp[1], s_tmp[2]);

    /* init bv model */
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_s0], s_tmp[pos_s0]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_s1], s_tmp[pos_s1]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_x], s_tmp[pos_x]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, x_tmp);

    TEST_PROP_LOG("pos_x %d s_tmp[0] %s s_tmp[1] %s s_tmp[2] %s target %s\n",
                  pos_x,
                  bzla_bv_to_char(d_mm, s_tmp[0]),
                  bzla_bv_to_char(d_mm, s_tmp[1]),
                  bzla_bv_to_char(d_mm, s_tmp[2]),
                  bzla_bv_to_char(d_mm, t));

    pi.exp          = exp;
    pi.bv[pos_x]    = s_tmp[pos_x];
    pi.bv[pos_s0]   = s0;
    pi.bv[pos_s1]   = s1;
    pi.bvd[pos_x]   = d_x;
    pi.bvd[pos_s0]  = d_s0;
    pi.bvd[pos_s1]  = d_s1;
    pi.target_value = t;

    /* -> first test local completeness  */
    /* we must find a solution within n move(s) */
    pi.pos_x = pos_x;
    pi.res_x = nullptr;
    is_inv   = is_inv_fun(d_bzla, &pi);
    ASSERT_TRUE(is_inv);
    res[pos_x] = val_fun(d_bzla, &pi);
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
    pi.res_x = nullptr;
    ASSERT_NE(res[pos_x], nullptr);
    if (pos_x == 0)
    {
      assert(bzla_bv_get_width(res[pos_x]) == 1);
    }
    else
    {
      assert(bzla_bv_get_width(res[pos_x]) == bzla_bv_get_width(s1));
    }

    if (n <= 2)
    {
      res[pos_s0] = bzla_bv_copy(d_mm, s0);
      res[pos_s1] = bzla_bv_copy(d_mm, s1);
    }

    pi.bv[pos_x] = res[pos_x];
    pi.res_x     = nullptr;
    if (pos_x == 0)
    {
      /**
       * s0: e[1], s1: e[2]
       *
       * test enabled branch:
       * res[pos_x] = 0: determine res[pos_s1] as res[pos_x] ? s0 : xs1 = t
       * res[pos_x] = 1: determine res[pos_s0] as res[pos_x] ? xs0 : s1 = t
       */
      if (bzla_bv_is_one(res[pos_x]))
      {
        pi.pos_x = pos_s0;
        is_inv   = is_inv_fun(d_bzla, &pi);
        assert(is_inv);
        if (n != 2)
        {
          res[pos_s0] = val_fun(d_bzla, &pi);
          ASSERT_NE(res[pos_s0], nullptr);
          res[pos_s1] = bzla_bv_copy(d_mm, s1);
        }
      }
      else
      {
        pi.pos_x = pos_s1;
        is_inv   = is_inv_fun(d_bzla, &pi);
        assert(is_inv);
        if (n != 2)
        {
          res[pos_s0] = bzla_bv_copy(d_mm, s0);
          res[pos_s1] = val_fun(d_bzla, &pi);
          ASSERT_NE(res[pos_s1], nullptr);
        }
      }
    }
    else
    {
      pi.pos_x = pos_s1;
      is_inv   = is_inv_fun(d_bzla, &pi);
      assert(is_inv);
      if (n != 2)
      {
        /**
         * test with condition fixed:
         * pos_x = 1: s0: e[0], s1: e[2]
         *            determine res[pos_s1] as c ? res[pos_x] : xs1 = t
         * pos_x = 2: s0: e[0], s1: e[1]
         *            determine res[pos_s1] as c ? xs1 : res[pos_x] = t
         */
        res[pos_s0] = bzla_bv_copy(d_mm, s0);
        res[pos_s1] = val_fun(d_bzla, &pi);
        ASSERT_NE(res[pos_s1], nullptr);
      }
    }
    if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);

    /* Note: this is also tested within the inverse function(s) */
    tmp = bzla_bv_ite(d_mm, res[0], res[1], res[2]);
    ASSERT_EQ(bzla_bv_compare(tmp, t), 0);
    bzla_bv_free(d_mm, tmp);
    bzla_bv_free(d_mm, res[0]);
    bzla_bv_free(d_mm, res[1]);
    bzla_bv_free(d_mm, res[2]);
    /* try to find the exact given solution */
    if (n == 1)
    {
      for (i = 0, res[pos_x] = 0; i < TEST_PROP_COMPLETE_N_TESTS; i++)
      {
        pi.bv[pos_x] = s_tmp[pos_x];
        pi.pos_x     = pos_x;
        pi.res_x     = nullptr;
        is_inv       = is_inv_fun(d_bzla, &pi);
        assert(is_inv);
        res[pos_x] = val_fun(d_bzla, &pi);
        ASSERT_NE(res[pos_x], nullptr);
        if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
        if (!bzla_bv_compare(res[pos_x], x)) break;
        bzla_bv_free(d_mm, res[pos_x]);
        res[pos_x] = nullptr;
      }
      ASSERT_NE(res[pos_x], nullptr);
      ASSERT_EQ(bzla_bv_compare(res[pos_x], x), 0);
      bzla_bv_free(d_mm, res[pos_x]);
    }

    /* -> then test completeness of the whole propagation algorithm
     *    (we must find a solution within n move(s)) */
    ((BzlaPropSolver *) d_bzla->slv)->stats.moves = 0;
    bzla_assume_exp(d_bzla, eq);
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_s0], s_tmp[pos_s0]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_s1], s_tmp[pos_s1]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[pos_x], s_tmp[pos_x]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, x_tmp);
    bzla_bv_free(d_mm, s_tmp[0]);
    bzla_bv_free(d_mm, s_tmp[1]);
    bzla_bv_free(d_mm, s_tmp[2]);
    bzla_bv_free(d_mm, x_tmp);
    bzla_node_release(d_bzla, eq);
    bzla_node_release(d_bzla, val);
    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_node_release(d_bzla, e[2]);
    bzla_sort_release(d_bzla, sort);
    bzla_sort_release(d_bzla, sort1);
    clear_domains();
    sat_res = bzla_prop_solver_sat(d_bzla);
    ASSERT_EQ(sat_res, BZLA_RESULT_SAT);
    TEST_PROP_LOG(
        "moves %u n %u\n", ((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    bzla_reset_incremental_usage(d_bzla);
  }

  /**
   * Given a binary operator and assignments 's' (for the other operand) and
   * 't' (for the target value of the operation) with a solution 'x' (for the
   * operand to solve for), test if a solution can be found within 'n'
   * propagation steps for bit-widths from 1 to TEST_PROP_COMPLETE_BW for both
   * operands of a binary operation.
   *
   * n         : The number of propagation steps expected to be required to
   *             find a solution.
   * create_bv : The function to create a bit-vector t = x <> s or t = s <> t
   *             for operator <>.
   * is_inv    : The function to test if given operator is invertible with
   *             respect to s and t.
   * val_fun   : The function to compute the value for x given s and t.
   */
  void prop_complete_binary(uint32_t n,
                            BzlaNode *(*create_exp)(Bzla *,
                                                    BzlaNode *,
                                                    BzlaNode *),
                            BzlaBitVector *(*create_bv)(BzlaMemMgr *,
                                                        const BzlaBitVector *,
                                                        const BzlaBitVector *),
                            BzlaPropIsInvFun is_inv,
                            BzlaPropComputeValueFun val_fun)
  {
    uint32_t bw;
    uint64_t i, j, k;
    BzlaBitVector *s[2], *t;

    bw = TEST_PROP_COMPLETE_BW;

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      s[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        s[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        t    = create_bv(d_mm, s[0], s[1]);
        TEST_PROP_LOG("s[0] %s s[1] %s t %s\n",
                      bzla_bv_to_char(d_mm, s[0]),
                      bzla_bv_to_char(d_mm, s[1]),
                      bzla_bv_to_char(d_mm, t));
        /* -> first test local completeness  */
        for (k = 0; k < bw; k++)
        {
          prop_complete_binary_idx(
              n, 1, bw, s[0], s[1], t, create_exp, create_bv, is_inv, val_fun);
          prop_complete_binary_idx(
              n, 0, bw, s[1], s[0], t, create_exp, create_bv, is_inv, val_fun);
        }
        bzla_bv_free(d_mm, s[1]);
        bzla_bv_free(d_mm, t);
      }
      bzla_bv_free(d_mm, s[0]);
    }
  }

  /**
   * Same as prop_complete_binary but for cond.
   *
   * n         : The number of propagation steps expected to be required to
   *             find a solution.
   * const_bits: True to test with const bits.
   */
  void prop_complete_cond(uint32_t n, bool const_bits)
  {
    uint32_t bw;
    uint64_t i, j, k, l;
    BzlaBitVector *s[3], *t;

    bw = TEST_PROP_COMPLETE_BW;

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
          TEST_PROP_LOG("s[0] %s s[1] %s s[2] %s t %s\n",
                        bzla_bv_to_char(d_mm, s[0]),
                        bzla_bv_to_char(d_mm, s[1]),
                        bzla_bv_to_char(d_mm, s[2]),
                        bzla_bv_to_char(d_mm, t));
          /* -> first test local completeness  */
          for (l = 0; l < bw; l++)
          {
            prop_complete_cond_idx(n, 0, bw, s[1], s[2], s[0], t, const_bits);
            prop_complete_cond_idx(n, 1, bw, s[0], s[2], s[1], t, const_bits);
            prop_complete_cond_idx(n, 2, bw, s[0], s[1], s[2], t, const_bits);
          }
          bzla_bv_free(d_mm, t);
          bzla_bv_free(d_mm, s[2]);
        }
        bzla_bv_free(d_mm, s[1]);
      }
      bzla_bv_free(d_mm, s[0]);
    }
  }

  /**
   * Test if a solution for the slice operator can be found within one
   * propagation step, and then if it can be found within one move.
   *
   * val_fun   : The function to compute the value for x given s and t.
   */
  void prop_complete_slice(BzlaPropComputeValueFun val_fun)
  {
    int32_t sat_res;
    uint32_t bw;
    uint64_t up, lo, i, j, k;
    BzlaNode *exp, *e, *val, *eq;
    BzlaBitVector *s, *t, *s_tmp, *t_tmp, *res, *tmp;
    BzlaSortId sort;
    BzlaBvDomain *d_x;
    BzlaPropInfo pi;

    memset(&pi, 0, sizeof(BzlaPropInfo));

    bw   = TEST_PROP_COMPLETE_BW;
    sort = bzla_sort_bv(d_bzla, bw);

    for (lo = 0; lo < bw; lo++)
    {
      for (up = lo; up < bw; up++)
      {
        for (i = 0; i < (uint32_t)(1 << bw); i++)
        {
          for (j = 0; j < bw; j++)
          {
            e     = bzla_exp_var(d_bzla, sort, 0);
            exp   = bzla_exp_bv_slice(d_bzla, e, up, lo);
            s     = bzla_bv_uint64_to_bv(d_mm, i, bw);
            t     = bzla_bv_slice(d_mm, s, up, lo);
            val   = bzla_exp_bv_const(d_bzla, t);
            eq    = bzla_exp_eq(d_bzla, exp, val);
            s_tmp = bzla_bv_new_random(d_mm, d_rng, bw);
            t_tmp = bzla_bv_slice(d_mm, s_tmp, up, lo);
            /* init bv model */
            bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
            bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
            bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e, s_tmp);
            bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, t_tmp);

            bzla_synthesize_exp(d_bzla, eq, 0);
            bzla_prop_solver_init_domains(d_bzla, d_domains, exp);
            assert((BzlaBvDomain *) bzla_hashint_map_get(
                d_domains, bzla_node_real_addr(exp->e[0])->id));
            d_x = (BzlaBvDomain *) bzla_hashint_map_get(
                      d_domains, bzla_node_real_addr(exp->e[0])->id)
                      ->as_ptr;
            assert(d_x);

            pi.exp          = exp;
            pi.bv[0]        = s_tmp;
            pi.bvd[0]       = d_x;
            pi.target_value = t;
            pi.pos_x        = 0;
            /* -> first test local completeness
             *    we must find a solution within one move */
            pi.res_x = 0;
            res      = val_fun(d_bzla, &pi);
            ASSERT_NE(res, nullptr);
            if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
            /* Note: this is also tested within inverse function */
            tmp = bzla_bv_slice(d_mm, res, up, lo);
            ASSERT_EQ(bzla_bv_compare(tmp, t), 0);
            bzla_bv_free(d_mm, tmp);
            bzla_bv_free(d_mm, res);
            /* try to find exact given solution */
            for (k = 0, res = 0; k < TEST_PROP_COMPLETE_N_TESTS; k++)
            {
              pi.res_x = 0;
              res      = val_fun(d_bzla, &pi);
              ASSERT_NE(res, nullptr);
              if (pi.res_x) bzla_bvdomain_free(d_mm, pi.res_x);
              if (!bzla_bv_compare(res, s)) break;
              bzla_bv_free(d_mm, res);
              res = 0;
            }
            ASSERT_NE(res, nullptr);
            ASSERT_EQ(bzla_bv_compare(res, s), 0);
            bzla_bv_free(d_mm, res);

            /* -> then test completeness of whole propagation algorithm
             *    (we must find a solution within one move) */
            ((BzlaPropSolver *) d_bzla->slv)->stats.moves = 0;
            bzla_assume_exp(d_bzla, eq);
            bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
            bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
            bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e, s_tmp);
            bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, t_tmp);
            bzla_bv_free(d_mm, s);
            bzla_bv_free(d_mm, t);
            bzla_bv_free(d_mm, s_tmp);
            bzla_bv_free(d_mm, t_tmp);
            bzla_node_release(d_bzla, eq);
            bzla_node_release(d_bzla, val);
            bzla_node_release(d_bzla, exp);
            bzla_node_release(d_bzla, e);
            clear_domains();
            sat_res = bzla_prop_solver_sat(d_bzla);
            ASSERT_EQ(sat_res, BZLA_RESULT_SAT);
            ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, 1u);
            bzla_reset_incremental_usage(d_bzla);
          }
        }
      }
    }
    bzla_sort_release(d_bzla, sort);
  }

  BzlaMemMgr *d_mm            = nullptr;
  BzlaRNG *d_rng              = nullptr;
  BzlaPropSolver *d_slv       = nullptr;
  BzlaIntHashTable *d_domains = nullptr;
};

/*------------------------------------------------------------------------*/

class TestPropConst : public TestProp
{
 protected:
  void SetUp() override
  {
    TestProp::SetUp();

    bzla_opt_set(d_bzla, BZLA_OPT_PROP_CONST_BITS, 1);
  }
};

/* ========================================================================== */
/* one_complete:                                                              */
/* Test if it is possible to find a solution with one propagation step.       */
/* ========================================================================== */

/* -------------------------------------------------------------------------- */
/* Regular inverse value computation, no const bits, no propagator domains.   */
/* -------------------------------------------------------------------------- */

TEST_F(TestProp, one_complete_add)
{
  prop_complete_binary(
      1, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, bzla_proputils_inv_add);
}

TEST_F(TestProp, one_complete_and)
{
  prop_complete_binary(
      1, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, bzla_proputils_inv_and);
}

TEST_F(TestProp, one_complete_eq)
{
  prop_complete_binary(
      1, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq);
}

TEST_F(TestProp, one_complete_ult)
{
  prop_complete_binary(
      1, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, bzla_proputils_inv_ult);
}

TEST_F(TestProp, one_complete_slt)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  prop_complete_binary(
      1, bzla_exp_bv_slt, bzla_bv_slt, bzla_is_inv_slt, bzla_proputils_inv_slt);
}

TEST_F(TestProp, one_complete_sll)
{
  prop_complete_binary(
      1, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, bzla_proputils_inv_sll);
}

TEST_F(TestProp, one_complete_srl)
{
  prop_complete_binary(
      1, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, bzla_proputils_inv_srl);
}

TEST_F(TestProp, one_complete_sra)
{
  bzla_opt_set(d_bzla, BZLA_OPT_PROP_ASHR, 1);
  prop_complete_binary(
      1, bzla_exp_bv_sra, bzla_bv_sra, bzla_is_inv_sra, bzla_proputils_inv_sra);
}

TEST_F(TestProp, one_complete_mul)
{
  prop_complete_binary(
      1, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, bzla_proputils_inv_mul);
}

TEST_F(TestProp, one_complete_udiv)
{
  prop_complete_binary(1,
                       bzla_exp_bv_udiv,
                       bzla_bv_udiv,
                       bzla_is_inv_udiv,
                       bzla_proputils_inv_udiv);
}

TEST_F(TestProp, one_complete_urem)
{
  prop_complete_binary(1,
                       bzla_exp_bv_urem,
                       bzla_bv_urem,
                       bzla_is_inv_urem,
                       bzla_proputils_inv_urem);
}

TEST_F(TestProp, one_complete_concat)
{
  prop_complete_binary(1,
                       bzla_exp_bv_concat,
                       bzla_bv_concat,
                       bzla_is_inv_concat,
                       bzla_proputils_inv_concat);
}

/* -------------------------------------------------------------------------- */
/* Regular inverse value computation with const bits, no propagator domains   */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropConst, one_complete_add_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_add,
                       bzla_bv_add,
                       bzla_is_inv_add_const,
                       bzla_proputils_inv_add_const);
}

TEST_F(TestPropConst, one_complete_and_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_and,
                       bzla_bv_and,
                       bzla_is_inv_and_const,
                       bzla_proputils_inv_and_const);
}

TEST_F(TestPropConst, one_complete_eq_const)
{
  prop_complete_binary(1,
                       bzla_exp_eq,
                       bzla_bv_eq,
                       bzla_is_inv_eq_const,
                       bzla_proputils_inv_eq_const);
}

TEST_F(TestPropConst, one_complete_ult_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_ult,
                       bzla_bv_ult,
                       bzla_is_inv_ult_const,
                       bzla_proputils_inv_ult_const);
}

TEST_F(TestPropConst, one_complete_slt_const)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  prop_complete_binary(1,
                       bzla_exp_bv_slt,
                       bzla_bv_slt,
                       bzla_is_inv_slt_const,
                       bzla_proputils_inv_slt_const);
}

TEST_F(TestPropConst, one_complete_mul_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_mul,
                       bzla_bv_mul,
                       bzla_is_inv_mul_const,
                       bzla_proputils_inv_mul_const);
}

TEST_F(TestPropConst, one_complete_sll_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_sll,
                       bzla_bv_sll,
                       bzla_is_inv_sll_const,
                       bzla_proputils_inv_sll_const);
}

TEST_F(TestPropConst, one_complete_srl_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_srl,
                       bzla_bv_srl,
                       bzla_is_inv_srl_const,
                       bzla_proputils_inv_srl_const);
}

TEST_F(TestPropConst, one_complete_sra_const)
{
  bzla_opt_set(d_bzla, BZLA_OPT_PROP_ASHR, 1);
  prop_complete_binary(1,
                       bzla_exp_bv_sra,
                       bzla_bv_sra,
                       bzla_is_inv_sra_const,
                       bzla_proputils_inv_sra_const);
}

TEST_F(TestPropConst, one_complete_udiv_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_udiv,
                       bzla_bv_udiv,
                       bzla_is_inv_udiv_const,
                       bzla_proputils_inv_udiv_const);
}

TEST_F(TestPropConst, one_complete_urem_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_urem,
                       bzla_bv_urem,
                       bzla_is_inv_urem_const,
                       bzla_proputils_inv_urem_const);
}

TEST_F(TestPropConst, one_complete_concat_const)
{
  prop_complete_binary(1,
                       bzla_exp_bv_concat,
                       bzla_bv_concat,
                       bzla_is_inv_concat_const,
                       bzla_proputils_inv_concat_const);
}

/* Note: We don't need to test completeness within one propagation step
 *       for slice -- we can always compute an inverse value for slice
 *       within one step if it is invertible. */

/* -------------------------------------------------------------------------- */
/* Inverse value computation with propagator domains, no const bits.          */
/* -------------------------------------------------------------------------- */

#if 0
TEST_F (TestProp, one_complete_add_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_add,
                        bzla_bv_add,
                        bzla_is_inv_add,
                        bzla_proputils_inv_add_bvprop);
}

TEST_F (TestProp, one_complete_and_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_and,
                        bzla_bv_and,
                        bzla_is_inv_and,
                        bzla_proputils_inv_and_bvprop);
}

TEST_F (TestProp, one_complete_eq_bvprop)
{
  prop_complete_binary (
      1, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq_bvprop);
}

TEST_F (TestProp, one_complete_ult_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_ult,
                        bzla_bv_ult,
                        bzla_is_inv_ult,
                        bzla_proputils_inv_ult_bvprop);
}

TEST_F (TestProp, one_complete_sll_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_sll,
                        bzla_bv_sll,
                        bzla_is_inv_sll,
                        bzla_proputils_inv_sll_bvprop);
}

TEST_F (TestProp, one_complete_srl_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_srl,
                        bzla_bv_srl,
                        bzla_is_inv_srl,
                        bzla_proputils_inv_srl_bvprop);
}

TEST_F (TestProp, one_complete_mul_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_mul,
                        bzla_bv_mul,
                        bzla_is_inv_mul,
                        bzla_proputils_inv_mul_bvprop);
}

TEST_F (TestProp, one_complete_udiv_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_udiv,
                        bzla_bv_udiv,
                        bzla_is_inv_udiv,
                        bzla_proputils_inv_udiv_bvprop);
}

TEST_F (TestProp, one_complete_urem_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_urem,
                        bzla_bv_urem,
                        bzla_is_inv_urem,
                        bzla_proputils_inv_udiv_urem);
}

TEST_F (TestProp, one_complete_concat_bvprop)
{
  prop_complete_binary (1,
                        bzla_exp_bv_concat,
                        bzla_bv_concat,
                        bzla_is_inv_concat,
                        bzla_proputils_inv_concat_bvprop);
}
#endif

/* ========================================================================== */
/* complete:                                                                  */
/* Test if it is possible to find a solution with two propagation step.       */
/* ========================================================================== */

/* -------------------------------------------------------------------------- */
/* Regular inverse value computation, no const bits, no propagator domains.   */
/* -------------------------------------------------------------------------- */

TEST_F(TestProp, complete_add)
{
  prop_complete_binary(
      2, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, bzla_proputils_inv_add);
}

TEST_F(TestProp, complete_and)
{
  prop_complete_binary(
      2, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, bzla_proputils_inv_and);
}

TEST_F(TestProp, complete_eq)
{
  prop_complete_binary(
      2, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq);
}

TEST_F(TestProp, complete_ult)
{
  prop_complete_binary(
      2, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, bzla_proputils_inv_ult);
}

TEST_F(TestProp, complete_slt)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  prop_complete_binary(
      2, bzla_exp_bv_slt, bzla_bv_slt, bzla_is_inv_slt, bzla_proputils_inv_slt);
}

TEST_F(TestProp, complete_sll)
{
  prop_complete_binary(
      2, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, bzla_proputils_inv_sll);
}

TEST_F(TestProp, complete_srl)
{
  prop_complete_binary(
      2, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, bzla_proputils_inv_srl);
}

TEST_F(TestProp, complete_sra)
{
  bzla_opt_set(d_bzla, BZLA_OPT_PROP_ASHR, 1);
  prop_complete_binary(
      2, bzla_exp_bv_sra, bzla_bv_sra, bzla_is_inv_sra, bzla_proputils_inv_sra);
}

TEST_F(TestProp, complete_mul)
{
  prop_complete_binary(
      2, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, bzla_proputils_inv_mul);
}

TEST_F(TestProp, complete_udiv)
{
  prop_complete_binary(2,
                       bzla_exp_bv_udiv,
                       bzla_bv_udiv,
                       bzla_is_inv_udiv,
                       bzla_proputils_inv_udiv);
}

TEST_F(TestProp, complete_urem)
{
  prop_complete_binary(2,
                       bzla_exp_bv_urem,
                       bzla_bv_urem,
                       bzla_is_inv_urem,
                       bzla_proputils_inv_urem);
}

TEST_F(TestProp, complete_concat)
{
  prop_complete_binary(2,
                       bzla_exp_bv_concat,
                       bzla_bv_concat,
                       bzla_is_inv_concat,
                       bzla_proputils_inv_concat);
}

TEST_F(TestProp, complete_slice)
{
  prop_complete_slice(bzla_proputils_inv_slice);
}

/* -------------------------------------------------------------------------- */
/* Regular inverse value computation with const bits, no propagator domains.  */
/* -------------------------------------------------------------------------- */

TEST_F(TestPropConst, complete_add_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_add,
                       bzla_bv_add,
                       bzla_is_inv_add_const,
                       bzla_proputils_inv_add_const);
}

TEST_F(TestPropConst, complete_and_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_and,
                       bzla_bv_and,
                       bzla_is_inv_and_const,
                       bzla_proputils_inv_and_const);
}

TEST_F(TestPropConst, complete_eq_const)
{
  prop_complete_binary(2,
                       bzla_exp_eq,
                       bzla_bv_eq,
                       bzla_is_inv_eq_const,
                       bzla_proputils_inv_eq_const);
}

TEST_F(TestPropConst, complete_ult_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_ult,
                       bzla_bv_ult,
                       bzla_is_inv_ult_const,
                       bzla_proputils_inv_ult_const);
}

TEST_F(TestPropConst, complete_slt_const)
{
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  prop_complete_binary(2,
                       bzla_exp_bv_slt,
                       bzla_bv_slt,
                       bzla_is_inv_slt_const,
                       bzla_proputils_inv_slt_const);
}

TEST_F(TestPropConst, complete_mul_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_mul,
                       bzla_bv_mul,
                       bzla_is_inv_mul_const,
                       bzla_proputils_inv_mul_const);
}

TEST_F(TestPropConst, complete_sll_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_sll,
                       bzla_bv_sll,
                       bzla_is_inv_sll_const,
                       bzla_proputils_inv_sll_const);
}

TEST_F(TestPropConst, complete_srl_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_srl,
                       bzla_bv_srl,
                       bzla_is_inv_srl_const,
                       bzla_proputils_inv_srl_const);
}

TEST_F(TestPropConst, complete_sra_const)
{
  bzla_opt_set(d_bzla, BZLA_OPT_PROP_ASHR, 1);
  prop_complete_binary(2,
                       bzla_exp_bv_sra,
                       bzla_bv_sra,
                       bzla_is_inv_sra_const,
                       bzla_proputils_inv_sra_const);
}

TEST_F(TestPropConst, complete_udiv_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_udiv,
                       bzla_bv_udiv,
                       bzla_is_inv_udiv_const,
                       bzla_proputils_inv_udiv_const);
}

TEST_F(TestPropConst, complete_urem_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_urem,
                       bzla_bv_urem,
                       bzla_is_inv_urem_const,
                       bzla_proputils_inv_urem_const);
}

TEST_F(TestPropConst, complete_concat_const)
{
  prop_complete_binary(2,
                       bzla_exp_bv_concat,
                       bzla_bv_concat,
                       bzla_is_inv_concat_const,
                       bzla_proputils_inv_concat_const);
}

TEST_F(TestPropConst, complete_cond_const) { prop_complete_cond(25, true); }

TEST_F(TestPropConst, complete_slice_const)
{
  prop_complete_slice(bzla_proputils_inv_slice_const);
}

/* -------------------------------------------------------------------------- */
/* Inverse value computation with propagator domains, no const bits.          */
/* -------------------------------------------------------------------------- */

#if 0
TEST_F (TestProp, complete_add_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_add,
                        bzla_bv_add,
                        bzla_is_inv_add,
                        bzla_proputils_inv_add_bvprop);
}

TEST_F (TestProp, complete_and_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_and,
                        bzla_bv_and,
                        bzla_is_inv_and,
                        bzla_proputils_inv_and_bvprop);
}

TEST_F (TestProp, complete_eq_bvprop)
{
  prop_complete_binary (
      2, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq_bvprop);
}

TEST_F (TestProp, complete_ult_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_ult,
                        bzla_bv_ult,
                        bzla_is_inv_ult,
                        bzla_proputils_inv_ult_bvprop);
}

TEST_F (TestProp, complete_sll_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_sll,
                        bzla_bv_sll,
                        bzla_is_inv_sll,
                        bzla_proputils_inv_sll_bvprop);
}

TEST_F (TestProp, complete_srl_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_srl,
                        bzla_bv_srl,
                        bzla_is_inv_srl,
                        bzla_proputils_inv_srl_bvprop);
}

TEST_F (TestProp, complete_mul_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_mul,
                        bzla_bv_mul,
                        bzla_is_inv_mul,
                        bzla_proputils_inv_mul_bvprop);
}

TEST_F (TestProp, complete_udiv_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_udiv,
                        bzla_bv_udiv,
                        bzla_is_inv_udiv,
                        bzla_proputils_inv_udiv_bvprop);
}

TEST_F (TestProp, complete_urem_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_urem,
                        bzla_bv_urem,
                        bzla_is_inv_urem,
                        bzla_proputils_inv_urem_bvprop);
}

TEST_F (TestProp, complete_concat_bvprop)
{
  prop_complete_binary (2,
                        bzla_exp_bv_concat,
                        bzla_bv_concat,
                        bzla_is_inv_concat,
                        bzla_proputils_inv_concat_bvprop);
}

TEST_F (TestProp, complete_slice_bvprop)
{
}
#endif
