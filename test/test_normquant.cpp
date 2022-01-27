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
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
#include "preprocess/bzlanormquant.h"
}

class TestNormQuant : public TestBzla
{
};

/*
 * exp: \not (\exists x,y . x = y)
 * res: \forall x,y . x != y
 *
 */
TEST_F(TestNormQuant, inv_exists)
{
  BzlaNode *exists, *eqx, *eqy, *x[2], *y[2], *expected, *result;
  BzlaSortId sort;

  sort   = bzla_sort_bv(d_bzla, 32);
  x[0]   = bzla_exp_param(d_bzla, sort, "x0");
  x[1]   = bzla_exp_param(d_bzla, sort, "x1");
  eqx    = bzla_exp_eq(d_bzla, x[0], x[1]);
  exists = bzla_exp_exists_n(d_bzla, x, 2, eqx);

  y[0]     = bzla_exp_param(d_bzla, sort, "y0");
  y[1]     = bzla_exp_param(d_bzla, sort, "y1");
  eqy      = bzla_exp_eq(d_bzla, y[0], y[1]);
  expected = bzla_exp_forall_n(d_bzla, y, 2, bzla_node_invert(eqy));

  result = bzla_normalize_quantifiers_node(d_bzla, bzla_node_invert(exists));
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x[0]);
  bzla_node_release(d_bzla, x[1]);
  bzla_node_release(d_bzla, eqx);
  bzla_node_release(d_bzla, y[0]);
  bzla_node_release(d_bzla, y[1]);
  bzla_node_release(d_bzla, eqy);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

/*
 * exp: \not (\forall x,y . x = y)
 * res: \exists x,y . x != y
 *
 */
TEST_F(TestNormQuant, inv_forall)
{
  BzlaNode *forall, *eqx, *eqy, *x[2], *y[2], *expected, *result;
  BzlaSortId sort;

  sort   = bzla_sort_bv(d_bzla, 32);
  x[0]   = bzla_exp_param(d_bzla, sort, 0);
  x[1]   = bzla_exp_param(d_bzla, sort, 0);
  eqx    = bzla_exp_eq(d_bzla, x[0], x[1]);
  forall = bzla_node_invert(bzla_exp_forall_n(d_bzla, x, 2, eqx));

  y[0]     = bzla_exp_param(d_bzla, sort, 0);
  y[1]     = bzla_exp_param(d_bzla, sort, 0);
  eqy      = bzla_exp_eq(d_bzla, y[0], y[1]);
  expected = bzla_exp_exists_n(d_bzla, y, 2, bzla_node_invert(eqy));

  result = bzla_normalize_quantifiers_node(d_bzla, forall);
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x[0]);
  bzla_node_release(d_bzla, x[1]);
  bzla_node_release(d_bzla, eqx);
  bzla_node_release(d_bzla, y[0]);
  bzla_node_release(d_bzla, y[1]);
  bzla_node_release(d_bzla, eqy);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

/*
 * exp: \forall x . \not (\exists y . x = y)
 * res: \forall x,y . x != y
 *
 */
TEST_F(TestNormQuant, inv_exists_nested1)
{
  BzlaNode *forall, *exists, *eqx, *x[2];
  BzlaNode *expected, *eqy, *y[2];
  BzlaNode *result;
  BzlaSortId sort;

  sort   = bzla_sort_bv(d_bzla, 32);
  x[0]   = bzla_exp_param(d_bzla, sort, 0);
  x[1]   = bzla_exp_param(d_bzla, sort, 0);
  eqx    = bzla_exp_eq(d_bzla, x[0], x[1]);
  exists = bzla_exp_exists(d_bzla, x[0], eqx);
  forall = bzla_exp_forall(d_bzla, x[1], bzla_node_invert(exists));

  y[0]     = bzla_exp_param(d_bzla, sort, 0);
  y[1]     = bzla_exp_param(d_bzla, sort, 0);
  eqy      = bzla_exp_eq(d_bzla, y[0], y[1]);
  expected = bzla_exp_forall_n(d_bzla, y, 2, bzla_node_invert(eqy));

  result = bzla_normalize_quantifiers_node(d_bzla, forall);
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x[0]);
  bzla_node_release(d_bzla, x[1]);
  bzla_node_release(d_bzla, eqx);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, y[0]);
  bzla_node_release(d_bzla, y[1]);
  bzla_node_release(d_bzla, eqy);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

/*
 * exp: \not (\forall x . \not (\exists y . x = y))
 * res: \exists x, y . x = y
 *
 */
TEST_F(TestNormQuant, inv_exists_nested2)
{
  BzlaNode *forall, *exists, *eqx, *x[2];
  BzlaNode *expected, *eqy, *y[2];
  BzlaNode *result;
  BzlaSortId sort;

  sort   = bzla_sort_bv(d_bzla, 32);
  x[0]   = bzla_exp_param(d_bzla, sort, 0);
  x[1]   = bzla_exp_param(d_bzla, sort, 0);
  eqx    = bzla_exp_eq(d_bzla, x[0], x[1]);
  exists = bzla_exp_exists(d_bzla, x[0], eqx);
  forall =
      bzla_node_invert(bzla_exp_forall(d_bzla, x[1], bzla_node_invert(exists)));

  y[0]     = bzla_exp_param(d_bzla, sort, 0);
  y[1]     = bzla_exp_param(d_bzla, sort, 0);
  eqy      = bzla_exp_eq(d_bzla, y[0], y[1]);
  expected = bzla_exp_exists_n(d_bzla, y, 2, eqy);

  result = bzla_normalize_quantifiers_node(d_bzla, forall);
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x[0]);
  bzla_node_release(d_bzla, x[1]);
  bzla_node_release(d_bzla, eqx);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, y[0]);
  bzla_node_release(d_bzla, y[1]);
  bzla_node_release(d_bzla, eqy);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

/*
 * exp: \not (\forall x . \exists y . \forall z . x /\ y /\ z)
 * res: \exists x . \forall y . \exists z . \not (x /\ y /\ z)
 *
 */
TEST_F(TestNormQuant, inv_prefix)
{
  BzlaNode *forall0, *forall1, *exists, *x[3], *_and;
  BzlaNode *exists0, *expected, *forall, *y[3], *andy;
  BzlaNode *result;
  BzlaSortId sort;

  sort    = bzla_sort_bool(d_bzla);
  x[0]    = bzla_exp_param(d_bzla, sort, 0);
  x[1]    = bzla_exp_param(d_bzla, sort, 0);
  x[2]    = bzla_exp_param(d_bzla, sort, 0);
  _and    = bzla_exp_bv_and_n(d_bzla, x, 3);
  forall0 = bzla_exp_forall(d_bzla, x[0], _and);
  exists  = bzla_exp_exists(d_bzla, x[1], forall0);
  forall1 = bzla_node_invert(bzla_exp_forall(d_bzla, x[2], exists));

  y[0]     = bzla_exp_param(d_bzla, sort, 0);
  y[1]     = bzla_exp_param(d_bzla, sort, 0);
  y[2]     = bzla_exp_param(d_bzla, sort, 0);
  andy     = bzla_exp_bv_and_n(d_bzla, y, 3);
  exists0  = bzla_exp_exists(d_bzla, y[0], bzla_node_invert(andy));
  forall   = bzla_exp_forall(d_bzla, y[1], exists0);
  expected = bzla_exp_exists(d_bzla, y[2], forall);

  result = bzla_normalize_quantifiers_node(d_bzla, forall1);
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x[0]);
  bzla_node_release(d_bzla, x[1]);
  bzla_node_release(d_bzla, x[2]);
  bzla_node_release(d_bzla, _and);
  bzla_node_release(d_bzla, forall0);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, forall1);

  bzla_node_release(d_bzla, y[0]);
  bzla_node_release(d_bzla, y[1]);
  bzla_node_release(d_bzla, y[2]);
  bzla_node_release(d_bzla, andy);
  bzla_node_release(d_bzla, exists0);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: \forall x . \not ((\exists y . x > y) /\ (\exists z . x < z))
 *
 * after fixing polarities:
 *
 * res: \forall x . \not ((\forall y . x > y) /\ (\forall z . x < z))
 *
 */
TEST_F(TestNormQuant, inv_and_exists)
{
  BzlaNode *forall, *exists0, *exists1, *_and, *x, *y[2], *ult, *ugt;
  BzlaNode *expected, *forall0, *forall1, *_or, *X, *Y[2], *ugte, *ulte;
  BzlaNode *result;
  BzlaSortId sort;

  sort    = bzla_sort_bv(d_bzla, 32);
  x       = bzla_exp_param(d_bzla, sort, 0);
  y[0]    = bzla_exp_param(d_bzla, sort, 0);
  y[1]    = bzla_exp_param(d_bzla, sort, 0);
  ugt     = bzla_exp_bv_ugt(d_bzla, x, y[0]);
  exists0 = bzla_exp_exists(d_bzla, y[0], ugt);
  ult     = bzla_exp_bv_ult(d_bzla, x, y[1]);
  exists1 = bzla_exp_exists(d_bzla, y[1], ult);
  _and    = bzla_exp_bv_and(d_bzla, exists0, exists1);
  forall  = bzla_exp_forall(d_bzla, x, bzla_node_invert(_and));

  X        = bzla_exp_param(d_bzla, sort, 0);
  Y[0]     = bzla_exp_param(d_bzla, sort, 0);
  Y[1]     = bzla_exp_param(d_bzla, sort, 0);
  ulte     = bzla_exp_bv_ugt(d_bzla, X, Y[0]);
  forall0  = bzla_exp_forall(d_bzla, Y[0], ulte);
  ugte     = bzla_exp_bv_ult(d_bzla, X, Y[1]);
  forall1  = bzla_exp_forall(d_bzla, Y[1], ugte);
  _or      = bzla_exp_bv_and(d_bzla, forall0, forall1);
  expected = bzla_exp_forall(d_bzla, X, bzla_node_invert(_or));

  result = bzla_normalize_quantifiers_node(d_bzla, forall);
  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, y[0]);
  bzla_node_release(d_bzla, y[1]);
  bzla_node_release(d_bzla, ugt);
  bzla_node_release(d_bzla, exists0);
  bzla_node_release(d_bzla, ult);
  bzla_node_release(d_bzla, exists1);
  bzla_node_release(d_bzla, _and);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, X);
  bzla_node_release(d_bzla, Y[0]);
  bzla_node_release(d_bzla, Y[1]);
  bzla_node_release(d_bzla, ulte);
  bzla_node_release(d_bzla, forall0);
  bzla_node_release(d_bzla, ugte);
  bzla_node_release(d_bzla, forall1);
  bzla_node_release(d_bzla, _or);
  bzla_node_release(d_bzla, expected);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: \forall x . (\not ((\not \exists y . y > x) /\ x > 0))
 *
 * after eliminating negated quantifiers:
 *
 * res: \forall x . (\not ((\forall y . y <= x) /\ x > 0))
 *
 * after fixing ploarities:
 *
 * res: \forall x . (\not ((\exists y . y <= x) /\ x > 0))
 *
 */
TEST_F(TestNormQuant, normalize_negated_quant)
{
  BzlaNode *x, *y;
  BzlaNode *forallx, *existsy, *yugtx, *xugt0, *zero, *_and;
  BzlaNode *result;
  BzlaSortId sort;

  sort    = bzla_sort_bv(d_bzla, 32);
  x       = bzla_exp_param(d_bzla, sort, "x");
  y       = bzla_exp_param(d_bzla, sort, "y");
  zero    = bzla_exp_bv_zero(d_bzla, sort);
  xugt0   = bzla_exp_bv_ugt(d_bzla, x, zero);
  yugtx   = bzla_exp_bv_ugt(d_bzla, y, x);
  existsy = bzla_exp_exists(d_bzla, y, yugtx);
  _and    = bzla_exp_bv_and(d_bzla, bzla_node_invert(existsy), xugt0);
  forallx = bzla_exp_forall(d_bzla, x, bzla_node_invert(_and));

  result = bzla_normalize_quantifiers_node(d_bzla, forallx);
  ASSERT_EQ(result, forallx);

  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, forallx);
  bzla_node_release(d_bzla, existsy);
  bzla_node_release(d_bzla, yugtx);
  bzla_node_release(d_bzla, xugt0);
  bzla_node_release(d_bzla, zero);
  bzla_node_release(d_bzla, _and);
  bzla_node_release(d_bzla, result);
  bzla_sort_release(d_bzla, sort);
}

TEST_F(TestNormQuant, expand_quant)
{
  BzlaNode *forall, *x, *_and, *redandx, *result, *expected;
  BzlaNode *exists, *X, *redandX;
  BzlaSortId sort;

  bzla_opt_set(d_bzla, BZLA_OPT_RW_LEVEL, 0);

  sort    = bzla_sort_bv(d_bzla, 32);
  x       = bzla_exp_param(d_bzla, sort, "x");
  redandx = bzla_exp_bv_redand(d_bzla, x);
  forall  = bzla_exp_forall(d_bzla, x, redandx);
  _and    = bzla_exp_bv_and(d_bzla, bzla_node_invert(forall), forall);
  result  = bzla_normalize_quantifiers_node(d_bzla, _and);

  X        = bzla_exp_param(d_bzla, sort, "X");
  redandX  = bzla_exp_bv_redand(d_bzla, X);
  exists   = bzla_exp_exists(d_bzla, X, bzla_node_invert(redandX));
  expected = bzla_exp_bv_and(d_bzla, forall, exists);

  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, redandx);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, _and);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, X);
  bzla_node_release(d_bzla, redandX);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, expected);
  bzla_sort_release(d_bzla, sort);
  bzla_opt_set(d_bzla, BZLA_OPT_RW_LEVEL, 3);
}

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: v = \exists x, y . x < y ? v0 : v1
 *
 * after eliminating ITE:
 *
 * res_ite: v = v_ite
 *	    /\ \not ((\exists x, y . x < y) /\ v_ite != v0)
 *	    /\ \not (\not (\exists x, y . x < y) /\ v_ite != v1)
 *
 * after fixing polarities:
 *
 * res: v = v_ite
 *	/\ \not ((\forall x, y . x < y) /\ v_ite != v0)
 *	/\ \not (\not (\exists x, y . x < y) /\ v_ite != v1)
 *
 */
TEST_F(TestNormQuant, elim_ite1)
{
  BzlaNode *forall, *exists, *xy[2], *v0, *v1, *ult, *ite;
  BzlaNode *expected, *XY[2], *V[4], *eq, *eq0, *eq1, *eq2, *v;
  BzlaNode *and0, *and1, *and2, *and3, *ultXY;
  BzlaNode *result;
  BzlaSortId sort;

  sort   = bzla_sort_bv(d_bzla, 32);
  v      = bzla_exp_var(d_bzla, sort, "v");
  v0     = bzla_exp_var(d_bzla, sort, "v0");
  v1     = bzla_exp_var(d_bzla, sort, "v1");
  xy[0]  = bzla_exp_param(d_bzla, sort, "x");
  xy[1]  = bzla_exp_param(d_bzla, sort, "y");
  ult    = bzla_exp_bv_ult(d_bzla, xy[0], xy[1]);
  exists = bzla_exp_exists_n(d_bzla, xy, 2, ult);
  ite    = bzla_exp_cond(d_bzla, exists, v0, v1);
  eq     = bzla_exp_eq(d_bzla, v, ite);

  result = bzla_normalize_quantifiers_node(d_bzla, eq);

  V[0]   = bzla_exp_param(d_bzla, sort, "V0");
  V[1]   = bzla_exp_param(d_bzla, sort, "V_ite");
  V[2]   = bzla_exp_param(d_bzla, sort, "V1");
  V[3]   = bzla_exp_param(d_bzla, sort, "V");
  XY[0]  = bzla_exp_param(d_bzla, sort, "x0");
  XY[1]  = bzla_exp_param(d_bzla, sort, "y0");
  ultXY  = bzla_exp_bv_ult(d_bzla, XY[0], XY[1]);
  forall = bzla_exp_forall_n(d_bzla, XY, 2, ultXY);
  eq0    = bzla_exp_eq(d_bzla, V[1], V[0]);
  eq1    = bzla_exp_eq(d_bzla, V[1], V[2]);
  eq2    = bzla_exp_eq(d_bzla, V[3], V[1]);
  and0   = bzla_exp_bv_and(d_bzla, forall, bzla_node_invert(eq0));
  and1 =
      bzla_exp_bv_and(d_bzla, bzla_node_invert(exists), bzla_node_invert(eq1));
  and2 =
      bzla_exp_bv_and(d_bzla, bzla_node_invert(and0), bzla_node_invert(and1));
  and3     = bzla_exp_bv_and(d_bzla, eq2, and2);
  expected = bzla_exp_exists_n(d_bzla, V, 4, and3);

  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, v);
  bzla_node_release(d_bzla, v0);
  bzla_node_release(d_bzla, v1);
  bzla_node_release(d_bzla, xy[0]);
  bzla_node_release(d_bzla, xy[1]);
  bzla_node_release(d_bzla, ult);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, ite);
  bzla_node_release(d_bzla, eq);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, XY[0]);
  bzla_node_release(d_bzla, XY[1]);
  bzla_node_release(d_bzla, ultXY);
  bzla_node_release(d_bzla, and0);
  bzla_node_release(d_bzla, and1);
  bzla_node_release(d_bzla, and2);
  bzla_node_release(d_bzla, and3);
  bzla_node_release(d_bzla, eq0);
  bzla_node_release(d_bzla, eq1);
  bzla_node_release(d_bzla, eq2);
  bzla_node_release(d_bzla, V[0]);
  bzla_node_release(d_bzla, V[1]);
  bzla_node_release(d_bzla, V[2]);
  bzla_node_release(d_bzla, V[3]);
  bzla_node_release(d_bzla, expected);
  bzla_sort_release(d_bzla, sort);
}

/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: \forall x . x = (\exists y . x < y) ? v0 : v1
 *
 * after eliminating ITE:
 *
 * res_ite: \exists v0,v1 . \forall x. x = v_ite(x)
 *                     /\ \not ((\exists y . x < y) /\ v_ite(x) != v0)
 *                     /\ \not (\not (\exists y . x < y) /\ v_ite(x) != v1)
 *
 * after fixing polarities:
 *
 * res: \exists v0,v1 . \forall x . x = v_ite(x)
 *		    /\ \not ((\forall y . x < y) /\ v_ite(x) != v0)
 *		    /\ \not (\not (\exists y . x < y) /\ v_ite(x) != v1)
 *
 */
TEST_F(TestNormQuant, elim_ite2)
{
  BzlaNode *forall, *exists, *x, *y, *v0, *v1, *ult, *ite, *eqx;
  BzlaNode *expected, *existsY, *forallY, *X, *Y[2], *Z, *ultY1, *ultY;
  BzlaNode *eqZX, *eqZv1, *eqZv0, *imp_if, *imp_else, *and0, *and1;
  BzlaNode *result, *uf, *V[2], *forallX;
  BzlaSortId sort;

  sort   = bzla_sort_bv(d_bzla, 32);
  v0     = bzla_exp_var(d_bzla, sort, "v0");
  v1     = bzla_exp_var(d_bzla, sort, "v1");
  x      = bzla_exp_param(d_bzla, sort, "x");
  y      = bzla_exp_param(d_bzla, sort, "y");
  ult    = bzla_exp_bv_ult(d_bzla, x, y);
  exists = bzla_exp_exists(d_bzla, y, ult);
  ite    = bzla_exp_cond(d_bzla, exists, v0, v1);
  eqx    = bzla_exp_eq(d_bzla, x, ite);
  forall = bzla_exp_forall(d_bzla, x, eqx);

  result = bzla_normalize_quantifiers_node(d_bzla, forall);
  /* new UF introduced for ITE */
  ASSERT_EQ(d_bzla->ufs->count, 1u);
  uf = (BzlaNode *) d_bzla->ufs->first->key;

  X    = bzla_exp_param(d_bzla, sort, 0);
  Y[0] = bzla_exp_param(d_bzla, sort, 0);
  Y[1] = bzla_exp_param(d_bzla, sort, 0);
  Z    = bzla_exp_apply_n(d_bzla, uf, &X, 1);

  V[0]     = bzla_exp_param(d_bzla, sort, "V0");
  V[1]     = bzla_exp_param(d_bzla, sort, "V1");
  eqZX     = bzla_exp_eq(d_bzla, X, Z);
  eqZv0    = bzla_exp_eq(d_bzla, Z, V[0]);
  eqZv1    = bzla_exp_eq(d_bzla, Z, V[1]);
  ultY     = bzla_exp_bv_ult(d_bzla, X, Y[0]);
  ultY1    = bzla_exp_bv_ult(d_bzla, X, Y[1]);
  forallY  = bzla_exp_forall(d_bzla, Y[0], ultY);
  existsY  = bzla_exp_exists(d_bzla, Y[1], ultY1);
  imp_if   = bzla_exp_bv_and(d_bzla, forallY, bzla_node_invert(eqZv0));
  imp_else = bzla_exp_bv_and(
      d_bzla, bzla_node_invert(existsY), bzla_node_invert(eqZv1));
  and0 = bzla_exp_bv_and(
      d_bzla, bzla_node_invert(imp_if), bzla_node_invert(imp_else));
  and1     = bzla_exp_bv_and(d_bzla, eqZX, and0);
  forallX  = bzla_exp_forall(d_bzla, X, and1);
  expected = bzla_exp_exists_n(d_bzla, V, 2, forallX);

  ASSERT_EQ(result, expected);

  bzla_node_release(d_bzla, v0);
  bzla_node_release(d_bzla, v1);
  bzla_node_release(d_bzla, V[0]);
  bzla_node_release(d_bzla, V[1]);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, ult);
  bzla_node_release(d_bzla, exists);
  bzla_node_release(d_bzla, ite);
  bzla_node_release(d_bzla, eqx);
  bzla_node_release(d_bzla, forall);
  bzla_node_release(d_bzla, result);
  bzla_node_release(d_bzla, X);
  bzla_node_release(d_bzla, Y[0]);
  bzla_node_release(d_bzla, Y[1]);
  bzla_node_release(d_bzla, Z);
  bzla_node_release(d_bzla, eqZX);
  bzla_node_release(d_bzla, eqZv0);
  bzla_node_release(d_bzla, eqZv1);
  bzla_node_release(d_bzla, ultY);
  bzla_node_release(d_bzla, ultY1);
  bzla_node_release(d_bzla, existsY);
  bzla_node_release(d_bzla, forallY);
  bzla_node_release(d_bzla, imp_if);
  bzla_node_release(d_bzla, imp_else);
  bzla_node_release(d_bzla, and0);
  bzla_node_release(d_bzla, and1);
  bzla_node_release(d_bzla, forallX);
  bzla_node_release(d_bzla, expected);
  bzla_sort_release(d_bzla, sort);
}

#if 0
/*
 * NOTE: since we don't have NNF we need to fix the polarities of the
 * quantifiers (quantifier is flipped if uneven number of not)
 *
 * exp: v2 = (\exists y . v2 < y) ? v0 : v1
 *
 * after eliminating ITE:
 *
 * res: \exists v0,v1,v2,v_ite .
 *	   v2 = v_ite
 *         /\ \not ((\exists y . v2 < y) /\ v_ite != v0)
 *         /\ \not ((\forall y . v2 >= y) /\ v_ite != v!)
 *
 * after fixing polarities:
 *
 * res: \exists v0,v1,v2,v_ite .
 *	   v2 = v_ite
 *	   /\ \not ((\forall y . v2 < y) /\ v_ite != v0)
 *	   /\ \not ((\exists y . v2 >= y) /\ v_ite != v1)
 */
TEST_F (TestNormQuant, elim_top_ite)
{
  BzlaNode *exists, *y, *v0, *v1, *v2, *ult, *ite, *eqv;
  BzlaNode *expected, *existsY, *forallY, *Y[2], *ugte, *ultY;
  BzlaNode *eqZv2, *eqZv1, *eqZv0, *imp_if, *imp_else, *and0, *and1;
  BzlaNode *result, *V[4];

  v0 = bzla_exp_var (d_bzla, 32, "v0");
  v1 = bzla_exp_var (d_bzla, 32, "v1");
  v2 = bzla_exp_var (d_bzla, 32, "v2");
  y = bzla_exp_param (d_bzla, 32, "y");
  ult = bzla_exp_bv_ult (d_bzla, v2, y); 
  exists = bzla_exp_exists (d_bzla, y, ult);
  ite = bzla_exp_cond (d_bzla, exists, v0, v1); 
  eqv = bzla_exp_eq (d_bzla, v2, ite);

  result = bzla_normalize_quantifiers_node (d_bzla, eqv);

  Y[0] = bzla_exp_param (d_bzla, 32, "Y0");
  Y[1] = bzla_exp_param (d_bzla, 32, "Y1");

  V[0] = bzla_exp_param (d_bzla, 32, "V0");
  V[1] = bzla_exp_param (d_bzla, 32, "V1");
  V[2] = bzla_exp_param (d_bzla, 32, "V2");
  V[3] = bzla_exp_param (d_bzla, 32, "V_ite");
  eqZv2 = bzla_exp_eq (d_bzla, V[2], V[3]);
  eqZv0 = bzla_exp_eq (d_bzla, V[3], V[0]); 
  eqZv1 = bzla_exp_eq (d_bzla, V[3], V[1]);
  ultY = bzla_exp_bv_ult (d_bzla, V[2], Y[0]);
  ugte = bzla_exp_bv_ugte (d_bzla, V[2], Y[1]);
  forallY = bzla_exp_forall (d_bzla, Y[0], ultY);
  existsY = bzla_exp_exists (d_bzla, Y[1], ugte);
  imp_if = bzla_exp_bv_and (d_bzla, forallY, bzla_node_invert (eqZv0));
  imp_else = bzla_exp_bv_and (d_bzla, existsY, bzla_node_invert (eqZv1));
  and0 = bzla_exp_bv_and (d_bzla, bzla_node_invert (imp_if),
		       bzla_node_invert (imp_else));
  and1 = bzla_exp_bv_and (d_bzla, eqZv2, and0); 
  expected = bzla_exp_exists_n (d_bzla, V, 4, and1);

  printf ("\n"); bzla_dump_smt2_node (d_bzla, stdout, result, -1);
  printf ("\n"); bzla_dump_smt2_node (d_bzla, stdout, expected, -1);
  ASSERT_EQ (result, expected);

  bzla_node_release (d_bzla, v0);
  bzla_node_release (d_bzla, v1);
  bzla_node_release (d_bzla, v2);
  bzla_node_release (d_bzla, V[0]);
  bzla_node_release (d_bzla, V[1]);
  bzla_node_release (d_bzla, V[2]);
  bzla_node_release (d_bzla, V[3]);
  bzla_node_release (d_bzla, y);
  bzla_node_release (d_bzla, ult);
  bzla_node_release (d_bzla, exists);
  bzla_node_release (d_bzla, ite);
  bzla_node_release (d_bzla, eqv);
  bzla_node_release (d_bzla, result);
  bzla_node_release (d_bzla, Y[0]);
  bzla_node_release (d_bzla, Y[1]);
  bzla_node_release (d_bzla, eqZv2);
  bzla_node_release (d_bzla, eqZv0);
  bzla_node_release (d_bzla, eqZv1);
  bzla_node_release (d_bzla, ultY);
  bzla_node_release (d_bzla, ugte);
  bzla_node_release (d_bzla, existsY);
  bzla_node_release (d_bzla, forallY);
  bzla_node_release (d_bzla, imp_if);
  bzla_node_release (d_bzla, imp_else);
  bzla_node_release (d_bzla, and0);
  bzla_node_release (d_bzla, and1);
  bzla_node_release (d_bzla, expected);
}
#endif

/*
 * test quantifier hashing
 *
 * Ex0-Ex1.x0=x1 == Ey0-Ey1.y0=y1
 * Ex0x1.x0=x1 == Ey0y1.y1==y0
 *
 *
 *
 *
 */
