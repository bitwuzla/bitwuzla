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
      BzlaPropIsInv is_inv_fun,
      BzlaPropComputeValue inv_fun)
  {
    int32_t i, idx_s, sat_res;
    BzlaNode *e[2], *exp, *val, *eq;
    BzlaBitVector *bvetmp[2], *bvexptmp, *res[2], *tmp;
    BzlaSortId sort;
    BzlaIntHashTable *domains;
    BzlaIntHashTableIterator iit;
    (void) is_inv_fun;

    domains                           = bzla_hashint_map_new(d_bzla->mm);
    BZLA_PROP_SOLVER(d_bzla)->domains = domains;

    sort = bzla_sort_bv(d_bzla, bw);
    e[0] = bzla_exp_var(d_bzla, sort, 0);
    e[1] = bzla_exp_var(d_bzla, sort, 0);
    exp  = create_exp(d_bzla, e[0], e[1]);
    val  = bzla_exp_bv_const(d_bzla, bvexp);
    eq   = bzla_exp_eq(d_bzla, exp, val);

    bzla_prop_solver_init_domains(d_bzla, domains, exp);

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

    TEST_PROP_LOG("idx_x %d bvetmp[0] %s bvetmp[1] %s target %s\n",
                  idx_x,
                  bzla_bv_to_char(d_mm, bvetmp[0]),
                  bzla_bv_to_char(d_mm, bvetmp[1]),
                  bzla_bv_to_char(d_mm, bvexp));

    /* -> first test local completeness  */
    /* we must find a solution within n move(s) */
    assert(is_inv_fun(d_mm, bvexp, bve, idx_x));
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
        assert(is_inv_fun(d_mm, bvexp, bve, idx_x));
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
    sat_res = bzla_prop_solver_sat(d_bzla);
    ASSERT_EQ(sat_res, BZLA_RESULT_SAT);
    TEST_PROP_LOG(
        "moves %u n %u\n", ((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    ASSERT_LE(((BzlaPropSolver *) d_bzla->slv)->stats.moves, n);
    bzla_reset_incremental_usage(d_bzla);
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
        TEST_PROP_LOG("bve[0] %s bve[1] %s bvexp %s\n",
                      bzla_bv_to_char(d_mm, bve[0]),
                      bzla_bv_to_char(d_mm, bve[1]),
                      bzla_bv_to_char(d_mm, bvexp));
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

// TODO disabled for now, need to rethink inverse value computation with
// propagator domains, will probably not need it in the future
#if 0
TEST_F (TestProp, bzla_proputils_inv_interval_ult)
{
  bool res;
  BzlaBitVector *s, *t, *min, *max, *tmp_t, *tmp_x;
  std::vector<BzlaBvDomain *> domains;
  uint32_t bw_t = 1, bw_s = 3;
  uint64_t umin, umax;

  for (uint32_t i = 0; i < 3; ++i)
  {
    for (uint32_t j = 0; j < 3; ++j)
    {
      for (uint32_t k = 0; k < 3; ++k)
      {
        std::stringstream ss;
        ss << (i == 0 ? '0' : (i == 1 ? '1' : 'x'))
           << (j == 0 ? '0' : (j == 1 ? '1' : 'x'))
           << (k == 0 ? '0' : (k == 1 ? '1' : 'x'));
        domains.push_back (
            bzla_bvprop_new_from_char (d_mm, ss.str ().c_str ()));
      }
    }
  }

  for (uint32_t i = 0; i < (uint32_t) (1 << bw_t); i++)
  {
    t = bzla_bv_uint64_to_bv (d_mm, i, bw_t);
    for (uint32_t j = 0; j < (uint32_t) (1 << bw_s); j++)
    {
      s = bzla_bv_uint64_to_bv (d_mm, i, bw_s);
      for (BzlaBvDomain *d : domains)
      {
        for (uint32_t idx = 0; idx < 2; ++idx)
        {
          res =
              bzla_proputils_inv_interval_ult (d_mm, t, s, idx, d, &min, &max);
          if (res)
          {
            /* all values in interval must produce t */
            umin = bzla_bv_to_uint64 (min);
            umax = bzla_bv_to_uint64 (max);
            for (uint32_t k = umin; k <= umax; ++k)
            {
              tmp_x = bzla_bv_uint64_to_bv (d_mm, k, bw_s);
              tmp_t = idx ? bzla_bv_ult (d_mm, s, tmp_x)
                          : bzla_bv_ult (d_mm, tmp_x, s);
              ASSERT_EQ (bzla_bv_compare (tmp_t, t), 0);
              bzla_bv_free (d_mm, tmp_x);
              bzla_bv_free (d_mm, tmp_t);
            }
            bzla_bv_free (d_mm, min);
            bzla_bv_free (d_mm, max);
          }
          else
          {
            /* either x->hi or x->lo already do not produce t */
            bool conflict;
            tmp_t = idx ? bzla_bv_ult (d_mm, s, d->lo)
                        : bzla_bv_ult (d_mm, d->lo, s);
            conflict = bzla_bv_compare (tmp_t, t) != 0;
            bzla_bv_free (d_mm, tmp_t);
            tmp_t = idx ? bzla_bv_ult (d_mm, s, d->hi)
                        : bzla_bv_ult (d_mm, d->hi, s);
            conflict = conflict || (bzla_bv_compare (tmp_t, t) != 0);
            bzla_bv_free (d_mm, tmp_t);
            ASSERT_TRUE (conflict);
          }
        }
      }
      bzla_bv_free (d_mm, s);
    }
    bzla_bv_free (d_mm, t);
  }

  while (!domains.empty ())
  {
    bzla_bvprop_free (d_mm, domains.back ());
    domains.pop_back ();
  }
}
#endif

/*------------------------------------------------------------------------*/

TEST_F(TestProp, one_complete_add)
{
  prop_complete_binary(
      1, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, bzla_proputils_inv_add);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_add,
                        bzla_bv_add,
                        bzla_is_inv_add,
                        bzla_proputils_inv_add_bvprop);
#endif
}

TEST_F(TestProp, one_complete_and)
{
  prop_complete_binary(
      1, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, bzla_proputils_inv_and);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_and,
                        bzla_bv_and,
                        bzla_is_inv_and,
                        bzla_proputils_inv_and_bvprop);
#endif
}

TEST_F(TestProp, one_complete_eq)
{
  prop_complete_binary(
      1, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq);
#if 0
  prop_complete_binary (
      1, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq_bvprop);
#endif
}

TEST_F(TestProp, one_complete_ult)
{
  prop_complete_binary(
      1, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, bzla_proputils_inv_ult);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_ult,
                        bzla_bv_ult,
                        bzla_is_inv_ult,
                        bzla_proputils_inv_ult_bvprop);
#endif
}

TEST_F(TestProp, one_complete_sll)
{
  prop_complete_binary(
      1, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, bzla_proputils_inv_sll);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_sll,
                        bzla_bv_sll,
                        bzla_is_inv_sll,
                        bzla_proputils_inv_sll_bvprop);
#endif
}

TEST_F(TestProp, one_complete_srl)
{
  prop_complete_binary(
      1, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, bzla_proputils_inv_srl);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_srl,
                        bzla_bv_srl,
                        bzla_is_inv_srl,
                        bzla_proputils_inv_srl_bvprop);
#endif
}

TEST_F(TestProp, one_complete_mul)
{
  prop_complete_binary(
      1, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, bzla_proputils_inv_mul);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_mul,
                        bzla_bv_mul,
                        bzla_is_inv_mul,
                        bzla_proputils_inv_mul_bvprop);
#endif
}

TEST_F(TestProp, one_complete_udiv)
{
  prop_complete_binary(1,
                       bzla_exp_bv_udiv,
                       bzla_bv_udiv,
                       bzla_is_inv_udiv,
                       bzla_proputils_inv_udiv);
#if 0
  prop_complete_binary (1,
                        bzla_exp_bv_udiv,
                        bzla_bv_udiv,
                        bzla_is_inv_udiv,
                        bzla_proputils_inv_udiv_bvprop);
#endif
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

/*------------------------------------------------------------------------*/

TEST_F(TestProp, complete_add)
{
  prop_complete_binary(
      2, bzla_exp_bv_add, bzla_bv_add, bzla_is_inv_add, bzla_proputils_inv_add);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_add,
                        bzla_bv_add,
                        bzla_is_inv_add,
                        bzla_proputils_inv_add_bvprop);
#endif
}

TEST_F(TestProp, complete_and)
{
  prop_complete_binary(
      2, bzla_exp_bv_and, bzla_bv_and, bzla_is_inv_and, bzla_proputils_inv_and);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_and,
                        bzla_bv_and,
                        bzla_is_inv_and,
                        bzla_proputils_inv_and_bvprop);
#endif
}

TEST_F(TestProp, complete_eq)
{
  prop_complete_binary(
      2, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq);
#if 0
  prop_complete_binary (
      2, bzla_exp_eq, bzla_bv_eq, bzla_is_inv_eq, bzla_proputils_inv_eq_bvprop);
#endif
}

TEST_F(TestProp, complete_ult)
{
  prop_complete_binary(
      2, bzla_exp_bv_ult, bzla_bv_ult, bzla_is_inv_ult, bzla_proputils_inv_ult);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_ult,
                        bzla_bv_ult,
                        bzla_is_inv_ult,
                        bzla_proputils_inv_ult_bvprop);
#endif
}

TEST_F(TestProp, complete_sll)
{
  prop_complete_binary(
      2, bzla_exp_bv_sll, bzla_bv_sll, bzla_is_inv_sll, bzla_proputils_inv_sll);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_sll,
                        bzla_bv_sll,
                        bzla_is_inv_sll,
                        bzla_proputils_inv_sll_bvprop);
#endif
}

TEST_F(TestProp, complete_srl)
{
  prop_complete_binary(
      2, bzla_exp_bv_srl, bzla_bv_srl, bzla_is_inv_srl, bzla_proputils_inv_srl);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_srl,
                        bzla_bv_srl,
                        bzla_is_inv_srl,
                        bzla_proputils_inv_srl_bvprop);
#endif
}

TEST_F(TestProp, complete_mul)
{
  prop_complete_binary(
      2, bzla_exp_bv_mul, bzla_bv_mul, bzla_is_inv_mul, bzla_proputils_inv_mul);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_mul,
                        bzla_bv_mul,
                        bzla_is_inv_mul,
                        bzla_proputils_inv_mul_bvprop);
#endif
}

TEST_F(TestProp, complete_udiv)
{
  prop_complete_binary(2,
                       bzla_exp_bv_udiv,
                       bzla_bv_udiv,
                       bzla_is_inv_udiv,
                       bzla_proputils_inv_udiv);
#if 0
  prop_complete_binary (2,
                        bzla_exp_bv_udiv,
                        bzla_bv_udiv,
                        bzla_is_inv_udiv,
                        bzla_proputils_inv_udiv_bvprop);
#endif
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
          bzla_prop_solver_init_domains(d_bzla, domains, exp);
          BZLA_PROP_SOLVER(d_bzla)->domains = domains;

          /* -> first test local completeness
           *    we must find a solution within one move */
          res = bzla_proputils_inv_slice(d_bzla, exp, bvexp, bve, 0, domains);
          ASSERT_NE(res, nullptr);
          /* Note: this is also tested within inverse function */
          tmp = bzla_bv_slice(d_mm, res, up, lo);
          ASSERT_EQ(bzla_bv_compare(tmp, bvexp), 0);
          bzla_bv_free(d_mm, tmp);
          bzla_bv_free(d_mm, res);
          /* try to find exact given solution */
          for (k = 0, res = 0; k < TEST_PROP_COMPLETE_N_TESTS; k++)
          {
            res = bzla_proputils_inv_slice(d_bzla, exp, bvexp, bve, 0, domains);
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
