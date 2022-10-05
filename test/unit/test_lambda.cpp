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
#include "bzlabeta.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

class TestLambda : public TestBzla
{
 protected:
  void SetUp() override
  {
    TestBzla::SetUp();
    d_elem_sort  = bzla_sort_bv(d_bzla, s_elem_bw);
    d_index_sort = bzla_sort_bv(d_bzla, s_index_bw);
    d_array_sort = bzla_sort_array(d_bzla, d_index_sort, d_elem_sort);
  }

  void TearDown() override
  {
    if (d_elem_sort)
    {
      bzla_sort_release(d_bzla, d_elem_sort);
      d_elem_sort = 0;
    }
    if (d_index_sort)
    {
      bzla_sort_release(d_bzla, d_index_sort);
      d_index_sort = 0;
    }
    if (d_array_sort)
    {
      bzla_sort_release(d_bzla, d_array_sort);
      d_array_sort = 0;
    }
    TestBzla::TearDown();
  }

  void assert_parameterized(int32_t argc, ...)
  {
    int32_t i;
    va_list ap;
    BzlaNode *e;

    va_start(ap, argc);
    for (i = 0; i < argc; i++)
    {
      e = va_arg(ap, BzlaNode *);
      ASSERT_TRUE(bzla_node_real_addr(e)->parameterized);
    }
    va_end(ap);
  }

  void assert_not_parameterized(int32_t argc, ...)
  {
    int32_t i;
    va_list ap;
    BzlaNode *e;

    va_start(ap, argc);
    for (i = 0; i < argc; i++)
    {
      e = va_arg(ap, BzlaNode *);
      ASSERT_FALSE(bzla_node_real_addr(e)->parameterized);
    }
    va_end(ap);
  }

  BzlaNode *apply_and_reduce(Bzla *bzla,
                             BzlaNode *args[],
                             int32_t argc,
                             BzlaNode *lambda)
  {
    assert(bzla);
    assert(argc >= 0);
    assert(argc < 1 || args);
    assert(lambda);

    int32_t i;
    BzlaNode *result, *cur;
    BzlaNodePtrStack unassign;
    BzlaMemMgr *mm;

    mm = bzla->mm;

    BZLA_INIT_STACK(mm, unassign);

    cur = lambda;
    for (i = 0; i < argc; i++)
    {
      assert(bzla_node_is_regular(cur));
      assert(bzla_node_is_lambda(cur));
      bzla_beta_assign_param(bzla, cur, args[i]);
      BZLA_PUSH_STACK(unassign, cur);
      cur = bzla_node_real_addr(cur->e[1]);
    }

    result = bzla_beta_reduce_full(bzla, lambda, 0);

    while (!BZLA_EMPTY_STACK(unassign))
    {
      cur = BZLA_POP_STACK(unassign);
      bzla_beta_unassign_params(bzla, cur);
    }

    BZLA_RELEASE_STACK(unassign);

    return result;
  }

  void unary_param_exp_test(BzlaNode *(*func)(Bzla *, BzlaNode *) )
  {
    BzlaNode *result;
    BzlaNode *var, *expected, *param, *param_exp, *lambda;
    BzlaSortId lambda_index_sort;

    lambda_index_sort = d_elem_sort;
    var               = bzla_exp_var(d_bzla, d_elem_sort, "v1");
    expected          = func(d_bzla, var);
    param             = bzla_exp_param(d_bzla, lambda_index_sort, "p1");
    param_exp         = func(d_bzla, param);
    lambda            = bzla_exp_lambda(d_bzla, param, param_exp);
    result            = apply_and_reduce(d_bzla, &var, 1, lambda);

    ASSERT_EQ(result, expected);
    assert_parameterized(2, param, param_exp);
    assert_not_parameterized(4, var, expected, lambda, result);

    bzla_node_release(d_bzla, result);
    bzla_node_release(d_bzla, lambda);
    bzla_node_release(d_bzla, param_exp);
    bzla_node_release(d_bzla, param);
    bzla_node_release(d_bzla, expected);
    bzla_node_release(d_bzla, var);
  }

  void param_extension_test(BzlaNode *(*func)(Bzla *, BzlaNode *, uint32_t))
  {
    BzlaNode *result;
    BzlaNode *var, *param, *expected, *param_exp, *lambda;
    BzlaSortId lower_sort, upper_sort;
    int32_t lower, upper;

    lower      = s_elem_bw / 2 + 1;
    upper      = s_elem_bw - 1;
    lower_sort = bzla_sort_bv(d_bzla, lower);
    upper_sort = bzla_sort_bv(d_bzla, upper);

    var       = bzla_exp_var(d_bzla, lower_sort, "v1");
    param     = bzla_exp_param(d_bzla, lower_sort, "p1");
    expected  = func(d_bzla, var, upper_sort);
    param_exp = func(d_bzla, param, upper_sort);
    lambda    = bzla_exp_lambda(d_bzla, param, param_exp);
    result    = apply_and_reduce(d_bzla, &var, 1, lambda);

    ASSERT_EQ(result, expected);
    assert_parameterized(2, param, param_exp);
    assert_not_parameterized(4, var, expected, lambda, result);

    bzla_sort_release(d_bzla, lower_sort);
    bzla_sort_release(d_bzla, upper_sort);
    bzla_node_release(d_bzla, result);
    bzla_node_release(d_bzla, lambda);
    bzla_node_release(d_bzla, expected);
    bzla_node_release(d_bzla, param_exp);
    bzla_node_release(d_bzla, param);
    bzla_node_release(d_bzla, var);
  }

  /* (lambda x . bin_exp (x, v2)) (v1) or (lambda x . bin_exp (v1, x)) (v2) */
  void binary_param_exp_test(int32_t param_pos,
                             BzlaNode *(*func)(Bzla *, BzlaNode *, BzlaNode *) )
  {
    assert(param_pos == 0 || param_pos == 1);

    BzlaNode *result;
    BzlaNode *param_exp, *v1, *v2, *expected, *x;
    BzlaSortId v1_sort, v2_sort, x_sort;
    int32_t x_bw, v1_bw, v2_bw;

    v1_bw = s_elem_bw;
    v2_bw = s_elem_bw;

    if (func == bzla_exp_implies || func == bzla_exp_iff)
    {
      v1_bw = 1;
      v2_bw = 1;
    }

    x_bw = (param_pos == 0) ? v1_bw : v2_bw;

    v1_sort = bzla_sort_bv(d_bzla, v1_bw);
    v2_sort = bzla_sort_bv(d_bzla, v2_bw);
    x_sort  = bzla_sort_bv(d_bzla, x_bw);

    v1       = bzla_exp_var(d_bzla, v1_sort, "v1");
    v2       = bzla_exp_var(d_bzla, v2_sort, "v2");
    expected = func(d_bzla, v1, v2);
    x        = bzla_exp_param(d_bzla, x_sort, "x");

    if (param_pos == 0)
      param_exp = func(d_bzla, x, v2);
    else
      param_exp = func(d_bzla, v1, x);

    BzlaNode *lambda = bzla_exp_lambda(d_bzla, x, param_exp);

    if (param_pos == 0)
      result = apply_and_reduce(d_bzla, &v1, 1, lambda);
    else
      result = apply_and_reduce(d_bzla, &v2, 1, lambda);

    ASSERT_EQ(result, expected);
    assert_parameterized(2, x, param_exp);
    assert_not_parameterized(5, v1, v2, expected, lambda, result);

    bzla_sort_release(d_bzla, v1_sort);
    bzla_sort_release(d_bzla, v2_sort);
    bzla_sort_release(d_bzla, x_sort);
    bzla_node_release(d_bzla, result);
    bzla_node_release(d_bzla, lambda);
    bzla_node_release(d_bzla, param_exp);
    bzla_node_release(d_bzla, x);
    bzla_node_release(d_bzla, expected);
    bzla_node_release(d_bzla, v2);
    bzla_node_release(d_bzla, v1);
  }

  static constexpr int32_t s_index_bw = 32;
  static constexpr int32_t s_elem_bw  = 16;

  BzlaIntHashTable *d_htable = nullptr;
  BzlaSortId d_elem_sort     = 0;
  BzlaSortId d_index_sort    = 0;
  BzlaSortId d_array_sort    = 0;
};

/*---------------------------------------------------------------------------
 * constant lambda tests
 *---------------------------------------------------------------------------*/

TEST_F(TestLambda, const_lambda_const)
{
  BzlaNode *result;
  BzlaNode *x, *c, *i, *lambda;

  x      = bzla_exp_param(d_bzla, d_index_sort, "x");
  c      = bzla_exp_bv_zero(d_bzla, d_elem_sort);
  i      = bzla_exp_var(d_bzla, d_index_sort, "i");
  lambda = bzla_exp_lambda(d_bzla, x, c);

  /* (lambda x . 0) (i) */
  result = apply_and_reduce(d_bzla, &i, 1, lambda);
  ASSERT_EQ(result, c);
  assert_not_parameterized(1, result);
  bzla_node_release(d_bzla, result);

  /* (lambda x . 0) () */
  result = apply_and_reduce(d_bzla, 0, 0, lambda);
  ASSERT_EQ(result, c);
  assert_parameterized(1, x);
  assert_not_parameterized(4, result, c, i, lambda);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, c);
  bzla_node_release(d_bzla, x);
}

TEST_F(TestLambda, const_lambda_var)
{
  BzlaNode *result;
  BzlaNode *x, *a, *i, *lambda;

  x      = bzla_exp_param(d_bzla, d_index_sort, "x");
  a      = bzla_exp_var(d_bzla, d_elem_sort, "a");
  i      = bzla_exp_var(d_bzla, d_index_sort, "i");
  lambda = bzla_exp_lambda(d_bzla, x, a);

  /* (lambda x . a) (i) */
  result = apply_and_reduce(d_bzla, &i, 1, lambda);
  ASSERT_EQ(result, a);
  assert_not_parameterized(1, result);
  bzla_node_release(d_bzla, result);

  /* (lambda x . a) () */
  result = apply_and_reduce(d_bzla, 0, 0, lambda);
  ASSERT_EQ(result, a);
  assert_parameterized(1, x);
  assert_not_parameterized(4, result, lambda, i, a);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, i);
}

TEST_F(TestLambda, const_lambda_param)
{
  BzlaNode *result;
  BzlaNode *x, *a, *lambda;

  x      = bzla_exp_param(d_bzla, d_elem_sort, "x");
  a      = bzla_exp_var(d_bzla, d_elem_sort, "a");
  lambda = bzla_exp_lambda(d_bzla, x, x);

  /* (lambda x . x) (a) */
  result = apply_and_reduce(d_bzla, &a, 1, lambda);
  ASSERT_EQ(result, a);
  assert_not_parameterized(1, result);
  bzla_node_release(d_bzla, result);

  /* (lambda x . x) () */
  result = apply_and_reduce(d_bzla, 0, 0, lambda);
  ASSERT_EQ(result, lambda);
  assert_parameterized(1, x);
  assert_not_parameterized(3, result, lambda, a);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, x);
}

TEST_F(TestLambda, const_lambda_negated)
{
  BzlaNode *result;
  BzlaNode *a, *not_a, *x, *not_x, *lambda;

  a      = bzla_exp_var(d_bzla, d_elem_sort, "a");
  not_a  = bzla_exp_bv_not(d_bzla, a);
  x      = bzla_exp_param(d_bzla, d_elem_sort, "x");
  not_x  = bzla_exp_bv_not(d_bzla, x);
  lambda = bzla_exp_lambda(d_bzla, x, not_x);

  /* (lambda x . not (x)) (not (a)) */
  result = apply_and_reduce(d_bzla, &not_a, 1, lambda);
  ASSERT_EQ(result, a);
  assert_not_parameterized(1, result);
  bzla_node_release(d_bzla, result);

  /* (lambda x . not (x)) () */
  result = apply_and_reduce(d_bzla, 0, 0, lambda);
  ASSERT_EQ(result, lambda);
  assert_parameterized(2, x, not_x);
  assert_not_parameterized(4, result, lambda, not_a, a);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, not_x);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, not_a);
  bzla_node_release(d_bzla, a);
}

/* (lambda x . a) () */
TEST_F(TestLambda, unassigned_param)
{
  BzlaNode *result;
  BzlaNode *x, *a, *lambda;

  x      = bzla_exp_param(d_bzla, d_index_sort, "x");
  a      = bzla_exp_var(d_bzla, d_elem_sort, "a");
  lambda = bzla_exp_lambda(d_bzla, x, a);
  result = apply_and_reduce(d_bzla, 0, 0, lambda);

  ASSERT_EQ(result, a);
  assert_parameterized(1, x);
  assert_not_parameterized(3, result, lambda, a);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, x);
}

/*---------------------------------------------------------------------------
 * unary expression tests
 *---------------------------------------------------------------------------*/

TEST_F(TestLambda, param_not) { unary_param_exp_test(bzla_exp_bv_not); }

TEST_F(TestLambda, param_neg) { unary_param_exp_test(bzla_exp_bv_neg); }

TEST_F(TestLambda, param_redor) { unary_param_exp_test(bzla_exp_bv_redor); }

TEST_F(TestLambda, param_redxor) { unary_param_exp_test(bzla_exp_bv_redxor); }

TEST_F(TestLambda, param_redand) { unary_param_exp_test(bzla_exp_bv_redand); }

TEST_F(TestLambda, param_slice)
{
  BzlaNode *result;
  BzlaNode *var, *param, *expected, *slice, *lambda;
  int32_t lower, upper;

  lower = s_elem_bw / 2 + 1;
  upper = s_elem_bw - 1;

  var      = bzla_exp_var(d_bzla, d_elem_sort, "v1");
  param    = bzla_exp_param(d_bzla, d_elem_sort, "p1");
  expected = bzla_exp_bv_slice(d_bzla, var, upper, lower);
  slice    = bzla_exp_bv_slice(d_bzla, param, upper, lower);
  lambda   = bzla_exp_lambda(d_bzla, param, slice);
  result   = apply_and_reduce(d_bzla, &var, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, param, slice);
  assert_not_parameterized(4, var, expected, lambda, result);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, slice);
  bzla_node_release(d_bzla, param);
  bzla_node_release(d_bzla, var);
}

TEST_F(TestLambda, param_uext) { param_extension_test(bzla_exp_bv_uext); }

TEST_F(TestLambda, param_sext) { param_extension_test(bzla_exp_bv_sext); }

/*---------------------------------------------------------------------------
 * binary expression tests
 *---------------------------------------------------------------------------*/

TEST_F(TestLambda, param_implies)
{
  binary_param_exp_test(0, bzla_exp_implies);
  binary_param_exp_test(1, bzla_exp_implies);
}

TEST_F(TestLambda, param_iff)
{
  binary_param_exp_test(0, bzla_exp_iff);
  binary_param_exp_test(1, bzla_exp_iff);
}

TEST_F(TestLambda, param_xor)
{
  binary_param_exp_test(0, bzla_exp_bv_xor);
  binary_param_exp_test(1, bzla_exp_bv_xor);
}

TEST_F(TestLambda, param_xnor)
{
  binary_param_exp_test(0, bzla_exp_bv_xnor);
  binary_param_exp_test(1, bzla_exp_bv_xnor);
}

TEST_F(TestLambda, param_and)
{
  binary_param_exp_test(0, bzla_exp_bv_and);
  binary_param_exp_test(1, bzla_exp_bv_and);
}

TEST_F(TestLambda, param_nand)
{
  binary_param_exp_test(0, bzla_exp_bv_nand);
  binary_param_exp_test(1, bzla_exp_bv_nand);
}

TEST_F(TestLambda, param_or)
{
  binary_param_exp_test(0, bzla_exp_bv_or);
  binary_param_exp_test(1, bzla_exp_bv_or);
}

TEST_F(TestLambda, param_nor)
{
  binary_param_exp_test(0, bzla_exp_bv_nor);
  binary_param_exp_test(1, bzla_exp_bv_nor);
}

TEST_F(TestLambda, param_eq)
{
  binary_param_exp_test(0, bzla_exp_eq);
  binary_param_exp_test(1, bzla_exp_eq);
}

TEST_F(TestLambda, param_ne)
{
  binary_param_exp_test(0, bzla_exp_ne);
  binary_param_exp_test(1, bzla_exp_ne);
}

TEST_F(TestLambda, param_add)
{
  binary_param_exp_test(0, bzla_exp_bv_add);
  binary_param_exp_test(1, bzla_exp_bv_add);
}

TEST_F(TestLambda, param_uaddo)
{
  binary_param_exp_test(0, bzla_exp_bv_uaddo);
  binary_param_exp_test(1, bzla_exp_bv_uaddo);
}

TEST_F(TestLambda, param_saddo)
{
  binary_param_exp_test(0, bzla_exp_bv_saddo);
  binary_param_exp_test(1, bzla_exp_bv_saddo);
}

TEST_F(TestLambda, param_mul)
{
  binary_param_exp_test(0, bzla_exp_bv_mul);
  binary_param_exp_test(1, bzla_exp_bv_mul);
}

TEST_F(TestLambda, param_umulo)
{
  binary_param_exp_test(0, bzla_exp_bv_umulo);
  binary_param_exp_test(1, bzla_exp_bv_umulo);
}

TEST_F(TestLambda, param_smulo)
{
  binary_param_exp_test(0, bzla_exp_bv_smulo);
  binary_param_exp_test(1, bzla_exp_bv_smulo);
}

TEST_F(TestLambda, param_ult)
{
  binary_param_exp_test(0, bzla_exp_bv_ult);
  binary_param_exp_test(1, bzla_exp_bv_ult);
}

TEST_F(TestLambda, param_slt)
{
  binary_param_exp_test(0, bzla_exp_bv_slt);
  binary_param_exp_test(1, bzla_exp_bv_slt);
}

TEST_F(TestLambda, param_ulte)
{
  binary_param_exp_test(0, bzla_exp_bv_ulte);
  binary_param_exp_test(1, bzla_exp_bv_ulte);
}

TEST_F(TestLambda, param_slte)
{
  binary_param_exp_test(0, bzla_exp_bv_slte);
  binary_param_exp_test(1, bzla_exp_bv_slte);
}

TEST_F(TestLambda, param_ugt)
{
  binary_param_exp_test(0, bzla_exp_bv_ugt);
  binary_param_exp_test(1, bzla_exp_bv_ugt);
}

TEST_F(TestLambda, param_sgt)
{
  binary_param_exp_test(0, bzla_exp_bv_sgt);
  binary_param_exp_test(1, bzla_exp_bv_sgt);
}

TEST_F(TestLambda, param_ugte)
{
  binary_param_exp_test(0, bzla_exp_bv_ugte);
  binary_param_exp_test(1, bzla_exp_bv_ugte);
}

TEST_F(TestLambda, param_sgte)
{
  binary_param_exp_test(0, bzla_exp_bv_sgte);
  binary_param_exp_test(1, bzla_exp_bv_sgte);
}

TEST_F(TestLambda, param_sll)
{
  binary_param_exp_test(0, bzla_exp_bv_sll);
  binary_param_exp_test(1, bzla_exp_bv_sll);
}

TEST_F(TestLambda, param_srl)
{
  binary_param_exp_test(0, bzla_exp_bv_srl);
  binary_param_exp_test(1, bzla_exp_bv_srl);
}

TEST_F(TestLambda, param_sra)
{
  binary_param_exp_test(0, bzla_exp_bv_sra);
  binary_param_exp_test(1, bzla_exp_bv_sra);
}

TEST_F(TestLambda, param_rol)
{
  binary_param_exp_test(0, bzla_exp_bv_rol);
  binary_param_exp_test(1, bzla_exp_bv_rol);
}

TEST_F(TestLambda, param_ror)
{
  binary_param_exp_test(0, bzla_exp_bv_ror);
  binary_param_exp_test(1, bzla_exp_bv_ror);
}

TEST_F(TestLambda, param_sub)
{
  binary_param_exp_test(0, bzla_exp_bv_sub);
  binary_param_exp_test(1, bzla_exp_bv_sub);
}

TEST_F(TestLambda, param_usubo)
{
  binary_param_exp_test(0, bzla_exp_bv_usubo);
  binary_param_exp_test(1, bzla_exp_bv_usubo);
}

TEST_F(TestLambda, param_ssubo)
{
  binary_param_exp_test(0, bzla_exp_bv_ssubo);
  binary_param_exp_test(1, bzla_exp_bv_ssubo);
}

TEST_F(TestLambda, param_udiv)
{
  binary_param_exp_test(0, bzla_exp_bv_udiv);
  binary_param_exp_test(1, bzla_exp_bv_udiv);
}

TEST_F(TestLambda, param_sdiv)
{
  binary_param_exp_test(0, bzla_exp_bv_sdiv);
  binary_param_exp_test(1, bzla_exp_bv_sdiv);
}

TEST_F(TestLambda, param_sdivo)
{
  binary_param_exp_test(0, bzla_exp_bv_sdivo);
  binary_param_exp_test(1, bzla_exp_bv_sdivo);
}

TEST_F(TestLambda, param_urem)
{
  binary_param_exp_test(0, bzla_exp_bv_urem);
  binary_param_exp_test(1, bzla_exp_bv_urem);
}

TEST_F(TestLambda, param_srem)
{
  binary_param_exp_test(0, bzla_exp_bv_srem);
  binary_param_exp_test(1, bzla_exp_bv_srem);
}

TEST_F(TestLambda, param_smod)
{
  binary_param_exp_test(0, bzla_exp_bv_smod);
  binary_param_exp_test(1, bzla_exp_bv_smod);
}

TEST_F(TestLambda, param_concat)
{
  binary_param_exp_test(0, bzla_exp_bv_concat);
  binary_param_exp_test(1, bzla_exp_bv_concat);
}

/* (lambda x . read(a, x)) (i) */
TEST_F(TestLambda, param_read)
{
  BzlaNode *result;
  BzlaNode *x, *i, *a, *expected, *read, *lambda;

  x        = bzla_exp_param(d_bzla, d_index_sort, "x");
  i        = bzla_exp_var(d_bzla, d_index_sort, "i");
  a        = bzla_exp_array(d_bzla, d_array_sort, "a");
  expected = bzla_exp_read(d_bzla, a, i);
  read     = bzla_exp_read(d_bzla, a, x);
  lambda   = bzla_exp_lambda(d_bzla, x, read);
  result   = apply_and_reduce(d_bzla, &i, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, x, read);
  assert_not_parameterized(5, result, lambda, expected, a, i);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, read);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, x);
}

/*---------------------------------------------------------------------------
 * ternary expression tests
 *---------------------------------------------------------------------------*/

// !!! currently broken as we do not support lambda hashing yet
/* (lambda x . write (a, i, x)) (e) */
TEST_F(TestLambda, DISABLED_param_write1)
{
  BzlaNode *result;
  BzlaNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  i         = bzla_exp_var(d_bzla, d_index_sort, "i");
  e         = bzla_exp_var(d_bzla, d_elem_sort, "e");
  a         = bzla_exp_array(d_bzla, d_array_sort, "a");
  expected  = bzla_exp_lambda_write(d_bzla, a, i, e);
  x         = bzla_exp_param(d_bzla, d_elem_sort, "x");
  param_exp = bzla_exp_lambda_write(d_bzla, a, i, x);
  lambda    = bzla_exp_lambda(d_bzla, x, param_exp);
  result    = apply_and_reduce(d_bzla, &e, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, x, param_exp);
  assert_not_parameterized(6, result, lambda, expected, a, e, i);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, param_exp);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, e);
  bzla_node_release(d_bzla, i);
}

// !!! currently broken as we do not support lambda hashing yet
/* (lambda x . write (a, x, e)) (i) */
TEST_F(TestLambda, DISABLED_param_write2)
{
  BzlaNode *result;
  BzlaNode *i, *e, *a, *expected, *x, *param_exp, *lambda;

  i         = bzla_exp_var(d_bzla, d_index_sort, "i");
  e         = bzla_exp_var(d_bzla, d_elem_sort, "e");
  a         = bzla_exp_array(d_bzla, d_array_sort, "a");
  expected  = bzla_exp_lambda_write(d_bzla, a, i, e);
  x         = bzla_exp_param(d_bzla, d_index_sort, "p");
  param_exp = bzla_exp_lambda_write(d_bzla, a, x, e);
  lambda    = bzla_exp_lambda(d_bzla, x, param_exp);
  result    = apply_and_reduce(d_bzla, &i, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, x, param_exp);
  assert_not_parameterized(6, result, lambda, expected, a, e, i);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, param_exp);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, e);
  bzla_node_release(d_bzla, i);
}

/* (lambda x . x ? v2 : v3) (v1) */
TEST_F(TestLambda, param_bcond1)
{
  BzlaNode *result;
  BzlaNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BzlaSortId sort;

  sort      = bzla_sort_bv(d_bzla, 1);
  v1        = bzla_exp_var(d_bzla, sort, "v1");
  x         = bzla_exp_param(d_bzla, sort, "x");
  v2        = bzla_exp_var(d_bzla, d_elem_sort, "v2");
  v3        = bzla_exp_var(d_bzla, d_elem_sort, "v3");
  expected  = bzla_exp_cond(d_bzla, v1, v2, v3);
  param_exp = bzla_exp_cond(d_bzla, x, v2, v3);
  lambda    = bzla_exp_lambda(d_bzla, x, param_exp);
  result    = apply_and_reduce(d_bzla, &v1, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, x, param_exp);
  assert_not_parameterized(6, result, lambda, expected, v3, v2, v1);

  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, param_exp);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, v3);
  bzla_node_release(d_bzla, v2);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, v1);
}

/* (lambda x . v1 ? x : v3) (v2) */
TEST_F(TestLambda, param_bcond2)
{
  BzlaNode *result;
  BzlaNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BzlaSortId sort;

  sort      = bzla_sort_bv(d_bzla, 1);
  v1        = bzla_exp_var(d_bzla, sort, "v1");
  x         = bzla_exp_param(d_bzla, d_elem_sort, "x");
  v2        = bzla_exp_var(d_bzla, d_elem_sort, "v2");
  v3        = bzla_exp_var(d_bzla, d_elem_sort, "v3");
  expected  = bzla_exp_cond(d_bzla, v1, v2, v3);
  param_exp = bzla_exp_cond(d_bzla, v1, x, v3);
  lambda    = bzla_exp_lambda(d_bzla, x, param_exp);
  result    = apply_and_reduce(d_bzla, &v2, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, x, param_exp);
  assert_not_parameterized(6, result, lambda, expected, v3, v2, v1);

  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, param_exp);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, v3);
  bzla_node_release(d_bzla, v2);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, v1);
}

/* (lambda x . v1 ? v2 : x) (v3) */
TEST_F(TestLambda, param_bcond3)
{
  BzlaNode *result;
  BzlaNode *v1, *v2, *v3, *x, *expected, *param_exp, *lambda;
  BzlaSortId sort;

  sort      = bzla_sort_bv(d_bzla, 1);
  v1        = bzla_exp_var(d_bzla, sort, "v1");
  x         = bzla_exp_param(d_bzla, d_elem_sort, "x");
  v2        = bzla_exp_var(d_bzla, d_elem_sort, "v2");
  v3        = bzla_exp_var(d_bzla, d_elem_sort, "v3");
  expected  = bzla_exp_cond(d_bzla, v1, v2, v3);
  param_exp = bzla_exp_cond(d_bzla, v1, v2, x);
  lambda    = bzla_exp_lambda(d_bzla, x, param_exp);
  result    = apply_and_reduce(d_bzla, &v3, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(2, x, param_exp);
  assert_not_parameterized(6, result, lambda, expected, v3, v2, v1);

  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, param_exp);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, v3);
  bzla_node_release(d_bzla, v2);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, v1);
}

/* NOTE: right now, we have to use a read on the array condition as lambdas
 * return bit-vectors only. */
TEST_F(TestLambda, param_acond)
{
  BzlaNode *result;
  BzlaNode *var, *index, *e_if, *e_else, *expected_acond, *expected,
      *expected_cond;
  BzlaNode *param, *param_cond, *param_acond, *param_exp, *lambda;

  var            = bzla_exp_var(d_bzla, d_index_sort, "v1");
  index          = bzla_exp_var(d_bzla, d_index_sort, "i");
  expected_cond  = bzla_exp_eq(d_bzla, var, index);
  e_if           = bzla_exp_array(d_bzla, d_array_sort, "a1");
  e_else         = bzla_exp_array(d_bzla, d_array_sort, "a2");
  expected_acond = bzla_exp_cond(d_bzla, expected_cond, e_if, e_else);
  expected       = bzla_exp_read(d_bzla, expected_acond, var);

  param       = bzla_exp_param(d_bzla, d_index_sort, "p");
  param_cond  = bzla_exp_eq(d_bzla, param, index);
  param_acond = bzla_exp_cond(d_bzla, param_cond, e_if, e_else);
  param_exp   = bzla_exp_read(d_bzla, param_acond, param);
  lambda      = bzla_exp_lambda(d_bzla, param, param_exp);
  result      = apply_and_reduce(d_bzla, &var, 1, lambda);

  ASSERT_EQ(result, expected);
  assert_parameterized(4, param, param_cond, param_acond, param_exp);
  assert_not_parameterized(4, result, lambda, expected, expected_acond);
  assert_not_parameterized(5, e_else, e_if, expected_cond, index, var);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, param_exp);
  bzla_node_release(d_bzla, param_acond);
  bzla_node_release(d_bzla, param_cond);
  bzla_node_release(d_bzla, param);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, expected_acond);
  bzla_node_release(d_bzla, e_else);
  bzla_node_release(d_bzla, e_if);
  bzla_node_release(d_bzla, expected_cond);
  bzla_node_release(d_bzla, index);
  bzla_node_release(d_bzla, var);
}

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

/* (lambda x . read ((lambda y . y), x)) */
TEST_F(TestLambda, bounded_reduce1)
{
  BzlaNode *result;
  BzlaNode *x, *y, *l2, *r, *l1, *v, *expected;

  x  = bzla_exp_param(d_bzla, d_index_sort, "x");
  y  = bzla_exp_param(d_bzla, d_index_sort, "y");
  l2 = bzla_exp_lambda(d_bzla, y, y);
  r  = bzla_exp_apply_n(d_bzla, l2, &x, 1);
  l1 = bzla_exp_lambda(d_bzla, x, r);
  v  = bzla_exp_var(d_bzla, d_index_sort, "v");

  expected = bzla_exp_apply_n(d_bzla, l2, &v, 1);

  /* bound 2: stop at second lambda */
  bzla_beta_assign_param(d_bzla, l1, v);
  result = bzla_beta_reduce_bounded(d_bzla, l1, 2);
  bzla_beta_unassign_params(d_bzla, l1);

  ASSERT_EQ(result, expected);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, expected);

  /* bound 3: stop at third lambda */
  bzla_beta_assign_param(d_bzla, l1, v);
  result = bzla_beta_reduce_bounded(d_bzla, l1, 3);
  bzla_beta_unassign_params(d_bzla, l1);

  ASSERT_EQ(result, v);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, v);
  bzla_node_release(d_bzla, l1);
  bzla_node_release(d_bzla, r);
  bzla_node_release(d_bzla, l2);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, x);
}

TEST_F(TestLambda, bounded_reduce2)
{
  BzlaNode *result;
  BzlaNode *x, *i, *eq, *l, *j, *expected;

  x        = bzla_exp_param(d_bzla, d_index_sort, "x");
  i        = bzla_exp_var(d_bzla, d_index_sort, "i");
  eq       = bzla_exp_eq(d_bzla, x, i);
  l        = bzla_exp_lambda(d_bzla, x, eq);
  j        = bzla_exp_var(d_bzla, d_index_sort, "j");
  expected = bzla_exp_eq(d_bzla, i, j);

  bzla_beta_assign_param(d_bzla, l, j);
  result = bzla_beta_reduce_bounded(d_bzla, l, 0);
  ASSERT_EQ(result, expected);
  bzla_node_release(d_bzla, result);

  result = bzla_beta_reduce_bounded(d_bzla, l, 1);
  ASSERT_EQ(result, l);
  bzla_node_release(d_bzla, result);

  result = bzla_beta_reduce_bounded(d_bzla, eq, 1);
  ASSERT_EQ(result, expected);
  bzla_node_release(d_bzla, result);

  result = bzla_beta_reduce_bounded(d_bzla, l, 2);
  ASSERT_EQ(result, expected);
  bzla_beta_unassign_params(d_bzla, l);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, j);
  bzla_node_release(d_bzla, l);
  bzla_node_release(d_bzla, eq);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, x);
}

TEST_F(TestLambda, bounded_reduce3)
{
  BzlaNode *result;
  BzlaNode *x, *y, *l1, *a, *l2, *i, *expected;

  x        = bzla_exp_param(d_bzla, d_index_sort, "x");
  y        = bzla_exp_param(d_bzla, d_index_sort, "y");
  l1       = bzla_exp_lambda(d_bzla, x, x);
  a        = bzla_exp_apply_n(d_bzla, l1, &y, 1);
  l2       = bzla_exp_lambda(d_bzla, y, a);
  i        = bzla_exp_var(d_bzla, d_index_sort, "i");
  expected = bzla_exp_apply_n(d_bzla, l1, &i, 1);

  bzla_beta_assign_param(d_bzla, l2, i);
  result = bzla_beta_reduce_bounded(d_bzla, l2, 1);
  ASSERT_EQ(result, l2);
  bzla_node_release(d_bzla, result);

  result = bzla_beta_reduce_bounded(d_bzla, l2, 2);
  ASSERT_EQ(result, expected);
  bzla_node_release(d_bzla, result);

  result = bzla_beta_reduce_bounded(d_bzla, l2, 3);
  ASSERT_EQ(result, i);
  bzla_beta_unassign_params(d_bzla, l2);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, l2);
  bzla_node_release(d_bzla, l1);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, x);
}

/*---------------------------------------------------------------------------
 * reduction tests (with reduced expressions)
 *---------------------------------------------------------------------------*/

TEST_F(TestLambda, reduce_write1)
{
  BzlaNode *result;
  BzlaNode *a, *i, *e, *param, *read, *eq, *cond, *lambda;

  a      = bzla_exp_array(d_bzla, d_array_sort, "a");
  i      = bzla_exp_var(d_bzla, d_index_sort, "i");
  e      = bzla_exp_var(d_bzla, d_elem_sort, "e");
  param  = bzla_exp_param(d_bzla, d_index_sort, "p");
  read   = bzla_exp_read(d_bzla, a, param);
  eq     = bzla_exp_eq(d_bzla, param, i);
  cond   = bzla_exp_cond(d_bzla, eq, e, read);
  lambda = bzla_exp_lambda(d_bzla, param, cond);
  result = apply_and_reduce(d_bzla, &i, 1, lambda);

  ASSERT_EQ(result, e);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, cond);
  bzla_node_release(d_bzla, eq);
  bzla_node_release(d_bzla, read);
  bzla_node_release(d_bzla, param);
  bzla_node_release(d_bzla, e);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, a);
}

TEST_F(TestLambda, reduce_write2)
{
  BzlaNode *result;
  BzlaNode *a, *i, *e, *param, *read, *expected, *eq, *cond, *lambda;

  a        = bzla_exp_array(d_bzla, d_array_sort, "a");
  i        = bzla_exp_var(d_bzla, d_index_sort, "i");
  e        = bzla_exp_var(d_bzla, d_elem_sort, "e");
  param    = bzla_exp_param(d_bzla, d_index_sort, "p");
  read     = bzla_exp_read(d_bzla, a, param);
  expected = bzla_exp_read(d_bzla, a, i);
  eq       = bzla_exp_ne(d_bzla, param, i);
  cond     = bzla_exp_cond(d_bzla, eq, e, read);
  lambda   = bzla_exp_lambda(d_bzla, param, cond);
  result   = apply_and_reduce(d_bzla, &i, 1, lambda);

  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda);
  bzla_node_release(d_bzla, cond);
  bzla_node_release(d_bzla, eq);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, read);
  bzla_node_release(d_bzla, param);
  bzla_node_release(d_bzla, e);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, a);
}

TEST_F(TestLambda, reduce_nested_writes)
{
  BzlaNode *result;
  BzlaNode *i, *a, *e2, *w2, *e1, *w1;

  i = bzla_exp_var(d_bzla, d_index_sort, "i");
  /* w2 = write (a, i, e2) */
  a  = bzla_exp_array(d_bzla, d_array_sort, "a");
  e2 = bzla_exp_var(d_bzla, d_elem_sort, "e2");
  w2 = bzla_exp_lambda_write(d_bzla, a, i, e2);
  /* w1 = write (w1, not i, e1) */
  e1     = bzla_exp_var(d_bzla, d_elem_sort, "e1");
  w1     = bzla_exp_lambda_write(d_bzla, w2, bzla_node_invert(i), e1);
  result = apply_and_reduce(d_bzla, &i, 1, w1);

  ASSERT_EQ(result, e2);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, w1);
  bzla_node_release(d_bzla, e1);
  bzla_node_release(d_bzla, w2);
  bzla_node_release(d_bzla, e2);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, i);
}

/* (lambda x . (lambda y . (x + y))) (a b) */
TEST_F(TestLambda, reduce_nested_lambdas_add1)
{
  BzlaNode *result;
  BzlaNode *a, *b, *expected, *x, *y, *add, *fun;

  a                   = bzla_exp_var(d_bzla, d_elem_sort, "a");
  b                   = bzla_exp_var(d_bzla, d_elem_sort, "b");
  BzlaNode *args[2]   = {a, b};
  expected            = bzla_exp_bv_add(d_bzla, a, b);
  x                   = bzla_exp_param(d_bzla, d_elem_sort, "x");
  y                   = bzla_exp_param(d_bzla, d_elem_sort, "y");
  BzlaNode *params[2] = {x, y};
  add                 = bzla_exp_bv_add(d_bzla, x, y);
  fun                 = bzla_exp_fun(d_bzla, params, 2, add);

  result = apply_and_reduce(d_bzla, args, 2, fun);
  ASSERT_EQ(result, expected);
  bzla_node_release(d_bzla, result);

  BzlaNode *apply = bzla_exp_apply_n(d_bzla, fun, args, 2);
  result          = bzla_beta_reduce_full(d_bzla, apply, 0);
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, apply);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, fun);
  bzla_node_release(d_bzla, add);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, b);
  bzla_node_release(d_bzla, a);
}

/* (lambda x . (x + read(lambda y . y, b))) (a) */
TEST_F(TestLambda, reduce_nested_lambdas_add2)
{
  BzlaNode *result;
  BzlaNode *a, *b, *expected, *x, *y, *lambda1, *lambda2, *app, *add;
  BzlaSortId lambda_index_sort;

  lambda_index_sort = d_elem_sort;
  a                 = bzla_exp_var(d_bzla, d_elem_sort, "a");
  b                 = bzla_exp_var(d_bzla, d_elem_sort, "b");
  expected          = bzla_exp_bv_add(d_bzla, a, b);
  x                 = bzla_exp_param(d_bzla, lambda_index_sort, "x");
  y                 = bzla_exp_param(d_bzla, lambda_index_sort, "y");
  lambda2           = bzla_exp_lambda(d_bzla, y, y);
  app               = bzla_exp_apply_n(d_bzla, lambda2, &b, 1);
  add               = bzla_exp_bv_add(d_bzla, x, app);
  lambda1           = bzla_exp_lambda(d_bzla, x, add);
  result            = apply_and_reduce(d_bzla, &a, 1, lambda1);

  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, lambda1);
  bzla_node_release(d_bzla, add);
  bzla_node_release(d_bzla, app);
  bzla_node_release(d_bzla, lambda2);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, b);
  bzla_node_release(d_bzla, a);
}

/* (lambda x . not (read (lambda y . y, x + var))) (a) */
TEST_F(TestLambda, reduce_nested_lambdas_read)
{
  BzlaNode *result;
  BzlaNode *a, *var, *y, *lambda1, *lambda2, *x, *add, *app, *napp;
  BzlaNode *expected, *expected_add;

  var     = bzla_exp_var(d_bzla, d_elem_sort, "var");
  y       = bzla_exp_param(d_bzla, d_elem_sort, "y");
  lambda2 = bzla_exp_lambda(d_bzla, y, y);
  x       = bzla_exp_param(d_bzla, d_elem_sort, "x");
  add     = bzla_exp_bv_add(d_bzla, x, var);
  app     = bzla_exp_apply_n(d_bzla, lambda2, &add, 1);
  napp    = bzla_exp_bv_not(d_bzla, app);
  lambda1 = bzla_exp_lambda(d_bzla, x, napp);
  a       = bzla_exp_var(d_bzla, d_elem_sort, "a");
  /* exptected not (a + var) */
  expected_add = bzla_exp_bv_add(d_bzla, a, var);
  expected     = bzla_exp_bv_not(d_bzla, expected_add);
  result       = apply_and_reduce(d_bzla, &a, 1, lambda1);

  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, expected_add);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, lambda1);
  bzla_node_release(d_bzla, napp);
  bzla_node_release(d_bzla, app);
  bzla_node_release(d_bzla, add);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, lambda2);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, var);
}

/* (lambda x1 . (lambda x2 . ... (lambda x1000 . var))) (i1 ... i1000) */
TEST_F(TestLambda, reduce_nested_lambdas_const_n1000)
{
  BzlaNode *result;
  BzlaNode **params, **indices, *var, *fun;
  int32_t i, nesting_lvl;
  size_t size;

  nesting_lvl = 1000;
  size        = nesting_lvl * sizeof(BzlaNode *);
  var         = bzla_exp_var(d_bzla, d_elem_sort, 0);

  params  = (BzlaNode **) bzla_mem_malloc(d_bzla->mm, size);
  indices = (BzlaNode **) bzla_mem_malloc(d_bzla->mm, size);

  for (i = nesting_lvl - 1; i >= 0; i--)
  {
    indices[i] = bzla_exp_var(d_bzla, d_index_sort, 0);
    params[i]  = bzla_exp_param(d_bzla, d_index_sort, 0);
  }
  fun = bzla_exp_fun(d_bzla, params, nesting_lvl, var);

  result = apply_and_reduce(d_bzla, indices, nesting_lvl, fun);
  ASSERT_EQ(result, var);
  bzla_node_release(d_bzla, result);

  BzlaNode *apply = bzla_exp_apply_n(d_bzla, fun, indices, nesting_lvl);
  result          = bzla_beta_reduce_full(d_bzla, apply, 0);
  ASSERT_EQ(result, var);

  for (i = 0; i < nesting_lvl; i++)
  {
    bzla_node_release(d_bzla, params[i]);
    bzla_node_release(d_bzla, indices[i]);
  }

  bzla_mem_free(d_bzla->mm, params, size);
  bzla_mem_free(d_bzla->mm, indices, size);

  bzla_node_release(d_bzla, fun);
  bzla_node_release(d_bzla, apply);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, var);
}

TEST_F(TestLambda, hashing1)
{
  BzlaNode *w0, *w1, *i, *e, *a;
  BzlaSortId array_sort, sort;

  sort       = bzla_sort_bv(d_bzla, 32);
  array_sort = bzla_sort_array(d_bzla, sort, sort);

  a  = bzla_exp_array(d_bzla, array_sort, 0);
  i  = bzla_exp_var(d_bzla, sort, 0);
  e  = bzla_exp_var(d_bzla, sort, 0);
  w0 = bzla_exp_lambda_write(d_bzla, a, i, e);
  w1 = bzla_exp_lambda_write(d_bzla, a, i, e);
  ASSERT_EQ(w0, w1);

  bzla_sort_release(d_bzla, array_sort);
  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, a);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, e);
  bzla_node_release(d_bzla, w0);
  bzla_node_release(d_bzla, w1);
}

TEST_F(TestLambda, hashing2)
{
  BzlaNode *ite0, *ite1, *i, *e, *a0, *a1, *eq;
  BzlaSortId array_sort, sort;

  sort       = bzla_sort_bv(d_bzla, 32);
  array_sort = bzla_sort_array(d_bzla, sort, sort);

  a0   = bzla_exp_array(d_bzla, array_sort, 0);
  a1   = bzla_exp_array(d_bzla, array_sort, 0);
  i    = bzla_exp_var(d_bzla, sort, 0);
  e    = bzla_exp_var(d_bzla, sort, 0);
  eq   = bzla_exp_eq(d_bzla, i, e);
  ite0 = bzla_exp_cond(d_bzla, eq, a0, a1);
  ite1 = bzla_exp_cond(d_bzla, eq, a0, a1);
  ASSERT_EQ(ite0, ite1);

  bzla_node_release(d_bzla, ite1);
  ite1 = bzla_exp_cond(d_bzla, bzla_node_invert(eq), a1, a0);
  ASSERT_EQ(ite0, ite1);

  bzla_sort_release(d_bzla, array_sort);
  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, a0);
  bzla_node_release(d_bzla, a1);
  bzla_node_release(d_bzla, i);
  bzla_node_release(d_bzla, e);
  bzla_node_release(d_bzla, eq);
  bzla_node_release(d_bzla, ite0);
  bzla_node_release(d_bzla, ite1);
}

/* check if hashing considers commutativity */
TEST_F(TestLambda, hashing3)
{
  BzlaNode *l0, *l1, *v, *p0, *p1, *eq0, *eq1;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 32);

  /* NOTE: order p0, v, p1 is important here */
  p0 = bzla_exp_param(d_bzla, sort, 0);
  v  = bzla_exp_var(d_bzla, sort, 0);
  p1 = bzla_exp_param(d_bzla, sort, 0);

  eq0 = bzla_exp_eq(d_bzla, p0, v);
  eq1 = bzla_exp_eq(d_bzla, v, p1);

  l0 = bzla_exp_lambda(d_bzla, p0, eq0);
  l1 = bzla_exp_lambda(d_bzla, p1, eq1);
  ASSERT_EQ(l0, l1);

  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, p0);
  bzla_node_release(d_bzla, p1);
  bzla_node_release(d_bzla, v);
  bzla_node_release(d_bzla, eq0);
  bzla_node_release(d_bzla, eq1);
  bzla_node_release(d_bzla, l0);
  bzla_node_release(d_bzla, l1);
}

TEST_F(TestLambda, hashing4)
{
  BzlaNode *f0, *f1, *p0[2], *p1[2], *eq0, *eq1;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 32);

  p0[0] = bzla_exp_param(d_bzla, sort, 0);
  p0[1] = bzla_exp_param(d_bzla, sort, 0);
  p1[0] = bzla_exp_param(d_bzla, sort, 0);
  p1[1] = bzla_exp_param(d_bzla, sort, 0);

  eq0 = bzla_exp_eq(d_bzla, p0[0], p0[1]);
  eq1 = bzla_exp_eq(d_bzla, p1[0], p1[1]);

  f0 = bzla_exp_fun(d_bzla, p0, 2, eq0);
  f1 = bzla_exp_fun(d_bzla, p1, 2, eq1);
  ASSERT_EQ(f0, f1);

  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, p0[0]);
  bzla_node_release(d_bzla, p0[1]);
  bzla_node_release(d_bzla, p1[0]);
  bzla_node_release(d_bzla, p1[1]);
  bzla_node_release(d_bzla, eq0);
  bzla_node_release(d_bzla, eq1);
  bzla_node_release(d_bzla, f0);
  bzla_node_release(d_bzla, f1);
}

TEST_F(TestLambda, quantifier_hashing1)
{
  BzlaNode *x0, *y0, *eq0, *f0, *e0;
  BzlaNode *x1, *y1, *eq1, *f1, *e1;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 32);
  x0   = bzla_exp_param(d_bzla, sort, 0);
  y0   = bzla_exp_param(d_bzla, sort, 0);
  eq0  = bzla_exp_eq(d_bzla, x0, y0);
  f0   = bzla_exp_forall(d_bzla, y0, eq0);
  e0   = bzla_exp_exists(d_bzla, x0, f0);

  x1  = bzla_exp_param(d_bzla, sort, 0);
  y1  = bzla_exp_param(d_bzla, sort, 0);
  eq1 = bzla_exp_eq(d_bzla, x1, y1);
  f1  = bzla_exp_forall(d_bzla, y1, eq1);
  e1  = bzla_exp_exists(d_bzla, x1, f1);
  ASSERT_EQ(e0, e1);

  bzla_node_release(d_bzla, x0);
  bzla_node_release(d_bzla, y0);
  bzla_node_release(d_bzla, eq0);
  bzla_node_release(d_bzla, f0);
  bzla_node_release(d_bzla, e0);
  bzla_node_release(d_bzla, x1);
  bzla_node_release(d_bzla, y1);
  bzla_node_release(d_bzla, eq1);
  bzla_node_release(d_bzla, f1);
  bzla_node_release(d_bzla, e1);
  bzla_sort_release(d_bzla, sort);
}

TEST_F(TestLambda, quantifier_hashing2)
{
  BzlaNode *x0, *x1, *x2, *x3, *y0, *y1, *y2, *y3;
  BzlaNode *a0, *a1, *a2, *a3, *a4, *a5, *a6, *r0;
  BzlaNode *f0, *e0, *f1, *e1, *f2, *e2, *f3, *e3;
  BzlaNode *x10, *x11, *x12, *x13, *y10, *y11, *y12, *y13;
  BzlaNode *a10, *a11, *a12, *a13, *a14, *a15, *a16, *r10;
  BzlaNode *f10, *e10, *f11, *e11, *f12, *e12, *f13, *e13;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 32);
  x0   = bzla_exp_param(d_bzla, sort, 0);
  x1   = bzla_exp_param(d_bzla, sort, 0);
  x2   = bzla_exp_param(d_bzla, sort, 0);
  x3   = bzla_exp_param(d_bzla, sort, 0);
  y0   = bzla_exp_param(d_bzla, sort, 0);
  y1   = bzla_exp_param(d_bzla, sort, 0);
  y2   = bzla_exp_param(d_bzla, sort, 0);
  y3   = bzla_exp_param(d_bzla, sort, 0);

  a0 = bzla_exp_bv_and(d_bzla, x0, y0);
  a1 = bzla_exp_bv_and(d_bzla, a0, x1);
  a2 = bzla_exp_bv_and(d_bzla, a1, y1);
  a3 = bzla_exp_bv_and(d_bzla, a2, x2);
  a4 = bzla_exp_bv_and(d_bzla, a3, y2);
  a5 = bzla_exp_bv_and(d_bzla, a4, x3);
  a6 = bzla_exp_bv_and(d_bzla, a5, y3);
  r0 = bzla_exp_bv_redor(d_bzla, a6);
  f0 = bzla_exp_forall(d_bzla, x0, r0);
  e0 = bzla_exp_exists(d_bzla, y0, f0);
  e1 = bzla_exp_exists(d_bzla, y1, e0);
  f1 = bzla_exp_forall(d_bzla, x1, e1);
  f2 = bzla_exp_forall(d_bzla, x2, f1);
  e2 = bzla_exp_exists(d_bzla, y2, f2);
  f3 = bzla_exp_forall(d_bzla, x3, e2);
  e3 = bzla_exp_exists(d_bzla, y3, f3);

  x10 = bzla_exp_param(d_bzla, sort, 0);
  x11 = bzla_exp_param(d_bzla, sort, 0);
  x12 = bzla_exp_param(d_bzla, sort, 0);
  x13 = bzla_exp_param(d_bzla, sort, 0);
  y10 = bzla_exp_param(d_bzla, sort, 0);
  y11 = bzla_exp_param(d_bzla, sort, 0);
  y12 = bzla_exp_param(d_bzla, sort, 0);
  y13 = bzla_exp_param(d_bzla, sort, 0);

  a10 = bzla_exp_bv_and(d_bzla, x10, y10);
  a11 = bzla_exp_bv_and(d_bzla, a10, x11);
  a12 = bzla_exp_bv_and(d_bzla, a11, y11);
  a13 = bzla_exp_bv_and(d_bzla, a12, x12);
  a14 = bzla_exp_bv_and(d_bzla, a13, y12);
  a15 = bzla_exp_bv_and(d_bzla, a14, x13);
  a16 = bzla_exp_bv_and(d_bzla, a15, y13);
  r10 = bzla_exp_bv_redor(d_bzla, a16);
  f10 = bzla_exp_forall(d_bzla, x10, r10);
  e10 = bzla_exp_exists(d_bzla, y10, f10);
  e11 = bzla_exp_exists(d_bzla, y11, e10);
  f11 = bzla_exp_forall(d_bzla, x11, e11);
  f12 = bzla_exp_forall(d_bzla, x12, f11);
  e12 = bzla_exp_exists(d_bzla, y12, f12);
  f13 = bzla_exp_forall(d_bzla, x13, e12);
  e13 = bzla_exp_exists(d_bzla, y13, f13);

  ASSERT_EQ(e3, e13);

  bzla_node_release(d_bzla, x0);
  bzla_node_release(d_bzla, x1);
  bzla_node_release(d_bzla, x2);
  bzla_node_release(d_bzla, x3);
  bzla_node_release(d_bzla, y0);
  bzla_node_release(d_bzla, y1);
  bzla_node_release(d_bzla, y2);
  bzla_node_release(d_bzla, y3);
  bzla_node_release(d_bzla, a0);
  bzla_node_release(d_bzla, a1);
  bzla_node_release(d_bzla, a2);
  bzla_node_release(d_bzla, a3);
  bzla_node_release(d_bzla, a4);
  bzla_node_release(d_bzla, a5);
  bzla_node_release(d_bzla, a6);
  bzla_node_release(d_bzla, r0);
  bzla_node_release(d_bzla, f0);
  bzla_node_release(d_bzla, e0);
  bzla_node_release(d_bzla, e1);
  bzla_node_release(d_bzla, f1);
  bzla_node_release(d_bzla, f2);
  bzla_node_release(d_bzla, e2);
  bzla_node_release(d_bzla, f3);
  bzla_node_release(d_bzla, e3);
  bzla_node_release(d_bzla, x10);
  bzla_node_release(d_bzla, x11);
  bzla_node_release(d_bzla, x12);
  bzla_node_release(d_bzla, x13);
  bzla_node_release(d_bzla, y10);
  bzla_node_release(d_bzla, y11);
  bzla_node_release(d_bzla, y12);
  bzla_node_release(d_bzla, y13);
  bzla_node_release(d_bzla, a10);
  bzla_node_release(d_bzla, a11);
  bzla_node_release(d_bzla, a12);
  bzla_node_release(d_bzla, a13);
  bzla_node_release(d_bzla, a14);
  bzla_node_release(d_bzla, a15);
  bzla_node_release(d_bzla, a16);
  bzla_node_release(d_bzla, r10);
  bzla_node_release(d_bzla, f10);
  bzla_node_release(d_bzla, e10);
  bzla_node_release(d_bzla, e11);
  bzla_node_release(d_bzla, f11);
  bzla_node_release(d_bzla, f12);
  bzla_node_release(d_bzla, e12);
  bzla_node_release(d_bzla, f13);
  bzla_node_release(d_bzla, e13);
  bzla_sort_release(d_bzla, sort);
}

#if 0
/* (lambda x . (lambda y . (x + y))) (a) */
TEST_F (TestLambda, partial_reduce_nested_lambdas_add1)
{
  BzlaNode *result;
  BzlaNode *a, *x, *y, *add, *params[2] = {x, y}, *fun;

  a = bzla_exp_var (d_bzla, d_elem_sort, "a");
  x = bzla_exp_param (d_bzla, d_elem_sort, "x");
  y = bzla_exp_param (d_bzla, d_elem_sort, "y");
  add = bzla_exp_bv_add (d_bzla, x, y);
  fun = bzla_exp_fun (d_bzla, params, 2, add); 
  result = apply_and_reduce (d_bzla, 1, &a, fun);

  /* expected: lambda y' . (a + y') */
  ASSERT_TRUE (bzla_node_is_lambda (result));
  ASSERT_NE (result, fun->e[1]);
  ASSERT_NE (result->e[0], fun->e[1]->e[0]);
  ASSERT_EQ (bzla_node_real_addr (result->e[1])->kind, BZLA_BV_ADD_NODE);
  ASSERT_EQ (bzla_node_real_addr (result->e[1])->e[0], a);
  ASSERT_EQ (bzla_node_real_addr (result->e[1])->e[1], result->e[0]);

  bzla_node_release (d_bzla, result);
  bzla_node_release (d_bzla, fun);
  bzla_node_release (d_bzla, add);
  bzla_node_release (d_bzla, y);
  bzla_node_release (d_bzla, x);
  bzla_node_release (d_bzla, a);
}
#endif

/*---------------------------------------------------------------------------
 * additional tests
 *---------------------------------------------------------------------------*/

TEST_F(TestLambda, define_fun)
{
  int32_t i;
  int32_t nesting_lvl = 1000;
  size_t size;
  BzlaNode **params, **lambdas, **ands, *left, *right, *expected, *result;

  size    = nesting_lvl * sizeof(BzlaNode *);
  params  = (BzlaNode **) bzla_mem_malloc(d_bzla->mm, size);
  lambdas = (BzlaNode **) bzla_mem_malloc(d_bzla->mm, size);
  ands = (BzlaNode **) bzla_mem_malloc(d_bzla->mm, size - sizeof(BzlaNode *));

  for (i = 0; i < nesting_lvl; i++)
    params[i] = bzla_exp_param(d_bzla, d_elem_sort, 0);

  ASSERT_GT(nesting_lvl, 1);
  left  = params[0];
  right = params[1];
  for (i = 0; i < nesting_lvl - 1; i++)
  {
    ands[i] = bzla_exp_bv_and(d_bzla, left, right);

    if (i + 2 < nesting_lvl)
    {
      left  = params[i + 2];
      right = ands[i];
    }
  }

  /* build expected */
  expected = ands[nesting_lvl - 2];
  for (i = nesting_lvl - 1; i >= 0; i--)
  {
    ASSERT_NE(expected, nullptr);
    lambdas[i] = bzla_exp_lambda(d_bzla, params[i], expected);
    expected   = lambdas[i];
  }

  result = bzla_exp_fun(d_bzla, params, nesting_lvl, ands[nesting_lvl - 2]);

  ASSERT_EQ(result, expected);

  for (i = 0; i < nesting_lvl; i++)
  {
    bzla_node_release(d_bzla, lambdas[i]);
    bzla_node_release(d_bzla, params[i]);

    if (i < nesting_lvl - 1) bzla_node_release(d_bzla, ands[i]);
  }

  bzla_mem_free(d_bzla->mm, params, size);
  bzla_mem_free(d_bzla->mm, lambdas, size);
  bzla_mem_free(d_bzla->mm, ands, size - sizeof(BzlaNode *));
  bzla_node_release(d_bzla, result);
}
