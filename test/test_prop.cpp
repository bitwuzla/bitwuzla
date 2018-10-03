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
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlaproputils.h"
#include "bzlaslvprop.h"
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

    bzla_opt_set(d_bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE, 1000);
    bzla_opt_set(d_bzla, BZLA_OPT_REWRITE_LEVEL, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_SORT_EXP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_INCREMENTAL, 1);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_CONC_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_SLICE_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_EQ_FLIP, 0);
    bzla_opt_set(d_bzla, BZLA_OPT_PROP_PROB_AND_FLIP, 0);
    // bzla_opt_set (d_bzla, BZLA_OPT_LOGLEVEL, 2);
  }

  BzlaMemMgr *d_mm = nullptr;
  BzlaRNG *d_rng   = nullptr;

  void prop_complete_binary_eidx(
      uint32_t n,
      int32_t eidx,
      uint32_t bw,
      BzlaBitVector *bve,
      BzlaBitVector *bvres,
      BzlaBitVector *bvexp,
      BzlaNode *(*create_exp)(Bzla *, BzlaNode *, BzlaNode *),
      BzlaBitVector *(*create_bv)(BzlaMemMgr *,
                                  const BzlaBitVector *,
                                  const BzlaBitVector *),
      BzlaBitVector *(*inv_bv)(
          Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t))
  {
#ifndef NDEBUG
    int32_t i, idx, sat_res;
    BzlaNode *e[2], *exp, *val, *eq;
    BzlaBitVector *bvetmp[2], *bvexptmp, *res[2], *tmp;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    exp  = create_exp(d_bzla, e[0], e[1]);
    val  = bzla_exp_bv_const(d_bzla, bvexp);
    eq   = bzla_exp_eq(d_bzla, exp, val);

    idx = eidx ? 0 : 1;

    bvetmp[eidx] = bzla_bv_new_random(d_mm, d_rng, bw);
    bvetmp[idx] =
        n == 1 ? bzla_bv_copy(d_mm, bve) : bzla_bv_new_random(d_mm, d_rng, bw);
    bvexptmp = create_bv(d_mm, bvetmp[0], bvetmp[1]);

    /* init bv model */
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[idx], bvetmp[idx]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[eidx], bvetmp[eidx]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, exp, bvexptmp);

    // printf ("eidx %d bvetmp[0] %s bvetmp[1] %s\n", eidx, bzla_bv_to_char
    // (d_mm, bvetmp[0]), bzla_bv_to_char (d_mm, bvetmp[1]));
    /* -> first test local completeness  */
    /* we must find a solution within n move(s) */
    res[eidx] = inv_bv(d_bzla, exp, bvexp, bve, eidx);
    ASSERT_NE(res[eidx], nullptr);
    res[idx] = n == 1 ? bzla_bv_copy(d_mm, bve)
                      : inv_bv(d_bzla, exp, bvexp, res[eidx], idx);
    ASSERT_NE(res[idx], nullptr);
    /* Note: this is also tested within the inverse function(s) */
    tmp = create_bv(d_mm, res[0], res[1]);
    ASSERT_EQ(bzla_bv_compare(tmp, bvexp), 0);
    bzla_bv_free(d_mm, tmp);
    bzla_bv_free(d_mm, res[0]);
    bzla_bv_free(d_mm, res[1]);
    /* try to find the exact given solution */
    if (n == 1)
    {
      for (i = 0, res[eidx] = 0; i < TEST_PROP_COMPLETE_N_TESTS; i++)
      {
        res[eidx] = inv_bv(d_bzla, exp, bvexp, bve, eidx);
        ASSERT_NE(res[eidx], nullptr);
        if (!bzla_bv_compare(res[eidx], bvres)) break;
        bzla_bv_free(d_mm, res[eidx]);
        res[eidx] = nullptr;
      }
      ASSERT_NE(res[eidx], nullptr);
      ASSERT_EQ(bzla_bv_compare(res[eidx], bvres), 0);
      bzla_bv_free(d_mm, res[eidx]);
    }

    /* -> then test completeness of the whole propagation algorithm
     *    (we must find a solution within n move(s)) */
    ((BzlaPropSolver *) d_bzla->slv)->stats.moves = 0;
    bzla_assume_exp(d_bzla, eq);
    bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
    bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[idx], bvetmp[idx]);
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, e[eidx], bvetmp[eidx]);
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
    // printf ("moves %u n %u\n", ((BzlaPropSolver *) g_btor->slv)->stats.moves,
    // n);
    ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    bzla_reset_incremental_usage(d_bzla);
#else
    (void) n;
    (void) eidx;
    (void) bw;
    (void) bve;
    (void) bvres;
    (void) bvexp;
    (void) create_exp;
    (void) create_bv;
    (void) inv_bv;
#endif
  }

  void prop_complete_binary(
      uint32_t n,
      BzlaNode *(*create_exp)(Bzla *, BzlaNode *, BzlaNode *),
      BzlaBitVector *(*create_bv)(BzlaMemMgr *,
                                  const BzlaBitVector *,
                                  const BzlaBitVector *),
      BzlaBitVector *(*inv_bv)(
          Bzla *, BzlaNode *, BzlaBitVector *, BzlaBitVector *, int32_t))
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
          prop_complete_binary_eidx(
              n, 1, bw, bve[0], bve[1], bvexp, create_exp, create_bv, inv_bv);
          prop_complete_binary_eidx(
              n, 0, bw, bve[1], bve[0], bvexp, create_exp, create_bv, inv_bv);
        }
        bzla_bv_free(d_mm, bve[1]);
        bzla_bv_free(d_mm, bvexp);
      }
      bzla_bv_free(d_mm, bve[0]);
    }
  }
};

/*------------------------------------------------------------------------*/

TEST_F(TestProp, one_complete_add)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_add, bzla_bv_add, inv_add_bv);
#endif
}

TEST_F(TestProp, one_complete_and)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_and, bzla_bv_and, inv_and_bv);
#endif
}

TEST_F(TestProp, one_complete_eq)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_eq, bzla_bv_eq, inv_eq_bv);
#endif
}

TEST_F(TestProp, one_complete_ult)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_ult, bzla_bv_ult, inv_ult_bv);
#endif
}

TEST_F(TestProp, one_complete_sll)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_sll, bzla_bv_sll, inv_sll_bv);
#endif
}

TEST_F(TestProp, one_complete_srl)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_srl, bzla_bv_srl, inv_srl_bv);
#endif
}

TEST_F(TestProp, one_complete_mul)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_mul, bzla_bv_mul, inv_mul_bv);
#endif
}

TEST_F(TestProp, one_complete_udiv)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_udiv, bzla_bv_udiv, inv_udiv_bv);
#endif
}

TEST_F(TestProp, one_complete_urem)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_urem, bzla_bv_urem, inv_urem_bv);
#endif
}

TEST_F(TestProp, one_complete_concat)
{
#ifndef NDEBUG
  prop_complete_binary(1, bzla_exp_bv_concat, bzla_bv_concat, inv_concat_bv);
#endif
}

/*------------------------------------------------------------------------*/

TEST_F(TestProp, complete_add)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_add, bzla_bv_add, inv_add_bv);
#endif
}

TEST_F(TestProp, complete_and)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_and, bzla_bv_and, inv_and_bv);
#endif
}

TEST_F(TestProp, complete_eq)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_eq, bzla_bv_eq, inv_eq_bv);
#endif
}

TEST_F(TestProp, complete_ult)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_ult, bzla_bv_ult, inv_ult_bv);
#endif
}

TEST_F(TestProp, complete_sll)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_sll, bzla_bv_sll, inv_sll_bv);
#endif
}

TEST_F(TestProp, complete_srl)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_srl, bzla_bv_srl, inv_srl_bv);
#endif
}

TEST_F(TestProp, complete_mul)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_mul, bzla_bv_mul, inv_mul_bv);
#endif
}

TEST_F(TestProp, complete_udiv)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_udiv, bzla_bv_udiv, inv_udiv_bv);
#endif
}

TEST_F(TestProp, complete_urem)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_urem, bzla_bv_urem, inv_urem_bv);
#endif
}

TEST_F(TestProp, complete_concat)
{
#ifndef NDEBUG
  prop_complete_binary(2, bzla_exp_bv_concat, bzla_bv_concat, inv_concat_bv);
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

          /* -> first test local completeness
           *    we must find a solution within one move */
          res = inv_slice_bv(d_bzla, exp, bvexp, bve, 0);
          ASSERT_NE(res, nullptr);
          /* Note: this is also tested within inverse function */
          tmp = bzla_bv_slice(d_mm, res, up, lo);
          ASSERT_EQ(bzla_bv_compare(tmp, bvexp), 0);
          bzla_bv_free(d_mm, tmp);
          bzla_bv_free(d_mm, res);
          /* try to find exact given solution */
          for (k = 0, res = 0; k < TEST_PROP_COMPLETE_N_TESTS; k++)
          {
            res = inv_slice_bv(d_bzla, exp, bvexp, bve, 0);
            ASSERT_NE(res, nullptr);
            if (!bzla_bv_compare(res, bve)) break;
            bzla_bv_free(d_mm, res);
            res = 0;
          }
          ASSERT_NE(res, nullptr);
          ASSERT_EQ(bzla_bv_compare(res, bve), 0);
          bzla_bv_free(d_mm, res);

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
