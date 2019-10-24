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
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlaproputils.h"
#include "bzlaslvprop.h"
#include "utils/bzlahashint.h"
#include "utils/bzlautil.h"
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
    d_rng             = &d_bzla->rng;
    d_slv             = BZLA_PROP_SOLVER(d_bzla);

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE, 1000);
    bzla_opt_set(d_bzla, BZLA_OPT_REWRITE_LEVEL, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_SORT_EXP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_INCREMENTAL, 1);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_CONC_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_EQ_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_AND_FLIP, 0);
    // bzla_opt_set (d_bzla, BZLA_OPT_PROP_CONST_BITS, 1);
    // bzla_opt_set (d_bzla, BZLA_OPT_LOGLEVEL, 2);
  }

  void prop_complete_binary_idx(
      uint32_t n,
      int32_t idx_x,
      uint32_t bw,
      BzlaBitVector *bve,
      BzlaBitVector *bvres,
      BzlaBitVector *bvexp,
      BzlaNode *(*create_exp)(Bzla *, BzlaNode *, BzlaNode *),
      BzlaBitVector *(*create_bv)(BzlaMemMgr *,
                                  const BzlaBitVector *,
                                  const BzlaBitVector *),
      BzlaPropIsInv is_inv,
      BzlaPropComputeValue inv_fun)
  {
#ifndef NDEBUG
    int32_t i, idx_s, sat_res;
    BzlaNode *e[2], *exp, *val, *eq;
    BzlaBitVector *bvetmp[2], *bvexptmp, *res[2], *tmp;
    BzlaSortId sort;
    BzlaIntHashTable *domains;
    BzlaIntHashTableIterator iit;

    domains                           = bzla_hashint_map_new(d_bzla->mm);
    BZLA_PROP_SOLVER(d_bzla)->domains = domains;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    exp  = create_exp(d_bzla, e[0], e[1]);
    val  = bzla_exp_bv_const(d_bzla, bvexp);
    eq   = bzla_exp_eq(d_bzla, exp, val);

    init_prop_domains(d_bzla, domains, exp);

    idx_s = idx_x ? 0 : 1;

    bvetmp[idx_x] = bzla_bv_new_random(d_mm, d_rng, bw);
    bvetmp[idx_s] =
        n == 1 ? bzla_bv_copy(d_mm, bve) : bzla_bv_new_random(d_mm, d_rng, bw);
    bvexptmp = create_bv(d_mm, bvetmp[0], bvetmp[1]);

    /* init bv model */
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[idx_s], bvetmp[idx_s]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[idx_x], bvetmp[idx_x]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, bvexptmp);

    // printf ("idx_x %d bvetmp[0] %s bvetmp[1] %s target %s\n",
    //        idx_x,
    //        bzla_bv_to_char (d_mm, bvetmp[0]),
    //        bzla_bv_to_char (d_mm, bvetmp[1]),
    //        bzla_bv_to_char (d_mm, bvexp));
    /* -> first test local completeness  */
    /* we must find a solution within n move(s) */
    assert(is_inv(d_mm, bvexp, bve, idx_x));
    res[idx_x] = inv_fun(d_bzla, exp, bvexp, bve, idx_x, domains);
    ASSERT_NE(res[idx_x], nullptr);
    res[idx_s] = n == 1
                     ? bzla_bv_copy(d_mm, bve)
                     : inv_fun(d_bzla, exp, bvexp, res[idx_x], idx_s, domains);
    ASSERT_NE(res[idx_s], nullptr);
    /* Note: this is also tested within the inverse function(s) */
    tmp = create_bv(d_mm, res[0], res[1]);
    ASSERT_EQ(bzla_bv_compare(tmp, bvexp), 0);
    bzla_bv_free(d_mm, tmp);
    bzla_bv_free(d_mm, res[0]);
    bzla_bv_free(d_mm, res[1]);
    /* try to find the exact given solution */
    if (n == 1)
    {
      for (i = 0, res[idx_x] = 0; i < TEST_PROP_COMPLETE_N_TESTS; i++)
      {
        assert(is_inv(d_mm, bvexp, bve, idx_x));
        res[idx_x] = inv_fun(d_bzla, exp, bvexp, bve, idx_x, domains);
        ASSERT_NE(res[idx_x], nullptr);
        if (!bzla_bv_compare(res[idx_x], bvres)) break;
        bzla_bv_free(d_mm, res[idx_x]);
        res[idx_x] = nullptr;
      }
      ASSERT_NE(res[idx_x], nullptr);
      ASSERT_EQ(bzla_bv_compare(res[idx_x], bvres), 0);
      bzla_bv_free(d_mm, res[idx_x]);
    }

    /* reset for sat call */
    bzla_iter_hashint_init(&iit, domains);
    while (bzla_iter_hashint_has_next(&iit))
    {
      bzla_bvprop_free(d_mm,
                       static_cast<BzlaBvDomain *>(
                           bzla_iter_hashint_next_data(&iit)->as_ptr));
    }
    bzla_hashint_map_delete(domains);
    BZLA_PROP_SOLVER(d_bzla)->domains = 0;

    /* -> then test completeness of the whole propagation algorithm
     *    (we must find a solution within n move(s)) */
    ((BzlaPropSolver *) d_bzla->slv)->stats.moves = 0;
    bzla_assume_exp(d_bzla, eq);
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[idx_s], bvetmp[idx_s]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[idx_x], bvetmp[idx_x]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, bvexptmp);
    bzla_bv_free(d_mm, bvetmp[0]);
    bzla_bv_free(d_mm, bvetmp[1]);
    bzla_bv_free(d_mm, bvexptmp);
    bzla_node_release(d_bzla, eq);
    bzla_node_release(d_bzla, val);
    bzla_node_release(d_bzla, exp);
    bzla_node_release(d_bzla, e[0]);
    bzla_node_release(d_bzla, e[1]);
    bzla_sort_release(d_bzla, sort);
    sat_res = sat_prop_solver_aux(d_bzla);
    ASSERT_EQ(sat_res, BZLA_RESULT_SAT);
    // printf ("moves %u n %u\n", ((BzlaPropSolver *) d_bzla->slv)->stats.moves,
    // n);
    ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    bzla_reset_incremental_usage(d_bzla);
#else
    (void) n;
    (void) idx_x;
    (void) bw;
    (void) bve;
    (void) bvres;
    (void) bvexp;
    (void) create_exp;
    (void) create_bv;
    (void) inv_bv;
#endif
  }

  void prop_complete_binary(uint32_t n,
                            BzlaNode *(*create_exp)(Bzla *,
                                                    BzlaNode *,
                                                    BzlaNode *),
                            BzlaBitVector *(*create_bv)(BzlaMemMgr *,
                                                        const BzlaBitVector *,
                                                        const BzlaBitVector *),
                            BzlaPropIsInv is_inv,
                            BzlaPropComputeValue inv_fun)
  {
    uint32_t bw;
    uint64_t i, j, k;
    BzlaBitVector *bve[2], *bvexp;

    bw = TEST_PROP_COMPLETE_BW;

    for (i = 0; i < (uint32_t)(1 << bw); i++)
    {
      bve[0] = bzla_bv_uint64_to_bv(d_mm, i, bw);
      for (j = 0; j < (uint32_t)(1 << bw); j++)
      {
        bve[1] = bzla_bv_uint64_to_bv(d_mm, j, bw);
        bvexp  = create_bv(d_mm, bve[0], bve[1]);
        // printf ("bve[0] %s bve[1] %s bvexp %s\n", bzla_bv_to_char (d_mm,
        // bve[0]), bzla_bv_to_char (d_mm, bve[1]), bzla_bv_to_char (d_mm,
        // bvexp));
        /* -> first test local completeness  */
        for (k = 0; k < bw; k++)
        {
          prop_complete_binary_idx(n,
                                   1,
                                   bw,
                                   bve[0],
                                   bve[1],
                                   bvexp,
                                   create_exp,
                                   create_bv,
                                   is_inv,
                                   inv_fun);
          prop_complete_binary_idx(n,
                                   0,
                                   bw,
                                   bve[1],
                                   bve[0],
                                   bvexp,
                                   create_exp,
                                   create_bv,
                                   is_inv,
                                   inv_fun);
        }
        bzla_bv_free(d_mm, bve[1]);
        bzla_bv_free(d_mm, bvexp);
      }
      bzla_bv_free(d_mm, bve[0]);
    }
  }

  BzlaMemMgr *d_mm      = nullptr;
  BzlaRNG *d_rng        = nullptr;
  BzlaPropSolver *d_slv = nullptr;
};

/*------------------------------------------------------------------------*/

TEST_F(TestProp, one_complete_add)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, inv_add_bv);
  prop_complete_binary(
      1, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, inv_add_bvprop);
#endif
}

TEST_F(TestProp, one_complete_and)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, inv_and_bv);
  prop_complete_binary(
      1, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, inv_and_bvprop);
#endif
}

TEST_F(TestProp, one_complete_eq)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, inv_eq_bv);
  prop_complete_binary(
      1, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, inv_eq_bvprop);
#endif
}

TEST_F(TestProp, one_complete_ult)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, inv_ult_bv);
  prop_complete_binary(
      1, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, inv_ult_bvprop);
#endif
}

TEST_F(TestProp, one_complete_sll)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, inv_sll_bv);
  prop_complete_binary(
      1, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, inv_sll_bvprop);
#endif
}

TEST_F(TestProp, one_complete_srl)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, inv_srl_bv);
  prop_complete_binary(
      1, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, inv_srl_bvprop);
#endif
}

TEST_F(TestProp, one_complete_mul)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, inv_mul_bv);
  prop_complete_binary(
      1, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, inv_mul_bvprop);
#endif
}

TEST_F(TestProp, one_complete_udiv)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_udiv, bzla_bv_udiv, bzla_is_inv_udiv, inv_udiv_bv);
  prop_complete_binary(
      1, bzla_exp_bv_udiv, bzla_bv_udiv, bzla_is_inv_udiv, inv_udiv_bvprop);
#endif
}

TEST_F(TestProp, one_complete_urem)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_urem, bzla_bv_urem, bzla_is_inv_urem, inv_urem_bv);
#endif
}

TEST_F(TestProp, one_complete_concat)
{
#ifndef NDEBUG
  prop_complete_binary(
      1, bzla_exp_bv_concat, bzla_bv_concat, bzla_is_inv_concat, inv_concat_bv);
#endif
}

/*------------------------------------------------------------------------*/

TEST_F(TestProp, complete_add)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, inv_add_bv);
  prop_complete_binary(
      2, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, inv_add_bvprop);
#endif
}

TEST_F(TestProp, complete_and)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, inv_and_bv);
  prop_complete_binary(
      2, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, inv_and_bvprop);
#endif
}

TEST_F(TestProp, complete_eq)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, inv_eq_bv);
  prop_complete_binary(
      2, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, inv_eq_bvprop);
#endif
}

TEST_F(TestProp, complete_ult)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, inv_ult_bv);
  prop_complete_binary(
      2, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, inv_ult_bvprop);
#endif
}

TEST_F(TestProp, complete_sll)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, inv_sll_bv);
  prop_complete_binary(
      2, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, inv_sll_bvprop);
#endif
}

TEST_F(TestProp, complete_srl)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, inv_srl_bv);
  prop_complete_binary(
      2, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, inv_srl_bvprop);
#endif
}

TEST_F(TestProp, complete_mul)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, inv_mul_bv);
  prop_complete_binary(
      2, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, inv_mul_bvprop);
#endif
}

TEST_F(TestProp, complete_udiv)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_udiv, bzla_bv_udiv, bzla_is_inv_udiv, inv_udiv_bv);
  prop_complete_binary(
      2, bzla_exp_bv_udiv, bzla_bv_udiv, bzla_is_inv_udiv, inv_udiv_bvprop);
#endif
}

TEST_F(TestProp, complete_urem)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_urem, bzla_bv_urem, bzla_is_inv_urem, inv_urem_bv);
#endif
}

TEST_F(TestProp, complete_concat)
{
#ifndef NDEBUG
  prop_complete_binary(
      2, bzla_exp_bv_concat, bzla_bv_concat, bzla_is_inv_concat, inv_concat_bv);
#endif
}

TEST_F(TestProp, complete_slice)
{
#ifndef NDEBUG
  int32_t sat_res;
  uint32_t bw;
  uint64_t up, lo, i, j, k;
  BzlaNode *exp, *e, *val, *eq;
  BzlaBitVector *bve, *bvexp, *bvetmp, *bvexptmp, *res, *tmp;
  BzlaSortId sort;
  BzlaIntHashTable *domains;
  BzlaIntHashTableIterator iit;

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
          e        = bzla_exp_var(d_bzla, sort, 0);
          exp      = bzla_exp_bv_slice(d_bzla, e, up, lo);
          bve      = bzla_bv_uint64_to_bv(d_mm, i, bw);
          bvexp    = bzla_bv_slice(d_mm, bve, up, lo);
          val      = bzla_exp_bv_const(d_bzla, bvexp);
          eq       = bzla_exp_eq(d_bzla, exp, val);
          bvetmp   = bzla_bv_new_random(d_mm, d_rng, bw);
          bvexptmp = bzla_bv_slice(d_mm, bvetmp, up, lo);
          /* init bv model */
          bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
          bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
          bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e, bvetmp);
          bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, bvexptmp);

          domains = bzla_hashint_map_new(d_bzla->mm);
          init_prop_domains(d_bzla, domains, exp);
          BZLA_PROP_SOLVER(d_bzla)->domains = domains;

          /* -> first test local completeness
           *    we must find a solution within one move */
          res = inv_slice_bv(d_bzla, exp, bvexp, bve, 0, domains);
          ASSERT_NE(res, nullptr);
          /* Note: this is also tested within inverse function */
          tmp = bzla_bv_slice(d_mm, res, up, lo);
          ASSERT_EQ(bzla_bv_compare(tmp, bvexp), 0);
          bzla_bv_free(d_mm, tmp);
          bzla_bv_free(d_mm, res);
          /* try to find exact given solution */
          for (k = 0, res = 0; k < TEST_PROP_COMPLETE_N_TESTS; k++)
          {
            res = inv_slice_bv(d_bzla, exp, bvexp, bve, 0, domains);
            ASSERT_NE(res, nullptr);
            if (!bzla_bv_compare(res, bve)) break;
            bzla_bv_free(d_mm, res);
            res = 0;
          }
          ASSERT_NE(res, nullptr);
          ASSERT_EQ(bzla_bv_compare(res, bve), 0);
          bzla_bv_free(d_mm, res);

          /* reset for sat call */
          bzla_iter_hashint_init(&iit, domains);
          while (bzla_iter_hashint_has_next(&iit))
          {
            bzla_bvprop_free(d_mm,
                             static_cast<BzlaBvDomain *>(
                                 bzla_iter_hashint_next_data(&iit)->as_ptr));
          }
          bzla_hashint_map_delete(domains);
          BZLA_PROP_SOLVER(d_bzla)->domains = 0;

          /* -> then test completeness of whole propagation algorithm
           *    (we must find a solution within one move) */
          ((BzlaPropSolver *) d_bzla->slv)->stats.moves = 0;
          bzla_assume_exp(d_bzla, eq);
          bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
          bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
          bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e, bvetmp);
          bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, bvexptmp);
          bzla_bv_free(d_mm, bve);
          bzla_bv_free(d_mm, bvexp);
          bzla_bv_free(d_mm, bvetmp);
          bzla_bv_free(d_mm, bvexptmp);
          bzla_node_release(d_bzla, eq);
          bzla_node_release(d_bzla, val);
          bzla_node_release(d_bzla, exp);
          bzla_node_release(d_bzla, e);
          sat_res = sat_prop_solver_aux(d_bzla);
          ASSERT_EQ(sat_res, BZLA_RESULT_SAT);
          ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, 1u);
          bzla_reset_incremental_usage(d_bzla);
        }
      }
    }
  }
  bzla_sort_release(d_bzla, sort);
#endif
}
