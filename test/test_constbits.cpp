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
#include "bzlaexp.h"
#include "bzlanode.h"
}

class TestConstBits : public TestBzla
{
};

#define TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(node) \
  do                                                 \
  {                                                  \
    bzla_node_release(d_bzla, node);                 \
    bzla_node_release(d_bzla, n0);                   \
    bzla_node_release(d_bzla, n1);                   \
  } while (0)

#define TEST_CBITS_CLEAN_UP_NODES    \
  do                                 \
  {                                  \
    bzla_node_release(d_bzla, n0);   \
    bzla_node_release(d_bzla, n1);   \
    bzla_node_release(d_bzla, v0);   \
    bzla_node_release(d_bzla, v1);   \
    bzla_node_release(d_bzla, zero); \
    bzla_node_release(d_bzla, ones); \
  } while (0)

#define TEST_CBITS_CLEAN_UP_NODES_ALL(node) \
  do                                        \
  {                                         \
    bzla_node_release(d_bzla, node);        \
    TEST_CBITS_CLEAN_UP_NODES;              \
  } while (0)

TEST_F(TestConstBits, const)
{
  BzlaNode *n, *real_n;
  BzlaBitVector *bv;
  uint32_t i;

  bv = bzla_bv_char_to_bv(d_bzla->mm, "00010011");
  n  = bzla_exp_bv_const(d_bzla, bv);
  /* constants are normalized such that LSB = 0 */
  assert(bzla_node_is_inverted(n));
  real_n = bzla_node_real_addr(n);
  bzla_synthesize_exp(d_bzla, n, 0);
  assert(real_n->av);
  assert(real_n->av->width == 8);
  for (i = 0; i < real_n->av->width; i++)
    assert(bzla_aig_is_const(real_n->av->aigs[i]));
  /* Note: n is inverted due to normalization */
  assert(bzla_aig_is_true(real_n->av->aigs[0]));
  assert(bzla_aig_is_true(real_n->av->aigs[1]));
  assert(bzla_aig_is_true(real_n->av->aigs[2]));
  assert(bzla_aig_is_false(real_n->av->aigs[3]));
  assert(bzla_aig_is_true(real_n->av->aigs[4]));
  assert(bzla_aig_is_true(real_n->av->aigs[5]));
  assert(bzla_aig_is_false(real_n->av->aigs[6]));
  assert(bzla_aig_is_false(real_n->av->aigs[7]));
  bzla_node_release(d_bzla, n);
  bzla_bv_free(d_bzla->mm, bv);
}

TEST_F(TestConstBits, concat)
{
  BzlaNode *n0, *n1, *v0, *v1, *zero, *ones;
  BzlaSortId s;
  uint32_t i;

  s    = bzla_sort_bv(d_bzla, 4);
  zero = bzla_exp_bv_zero(d_bzla, s);
  ones = bzla_exp_bv_ones(d_bzla, s);
  v0   = bzla_exp_var(d_bzla, s, "v0");
  v1   = bzla_exp_var(d_bzla, s, "v1");
  /* n0 = 0000 :: v0 = 0000xxxx */
  n0 = bzla_exp_bv_concat(d_bzla, zero, v0);
  assert(!bzla_node_is_inverted(n0));
  bzla_synthesize_exp(d_bzla, n0, 0);
  /* n1 = 1111 :: v1 = 1111xxxx */
  n1 = bzla_exp_bv_concat(d_bzla, ones, v1);
  assert(!bzla_node_is_inverted(n1));
  bzla_synthesize_exp(d_bzla, n1, 0);
  for (i = 0; i < 4; i++)
  {
    assert(bzla_aig_is_false(n0->av->aigs[i]));
    assert(bzla_aig_is_true(n1->av->aigs[i]));
  }
  for (i = 4; i < 8; i++)
  {
    assert(!bzla_aig_is_const(n0->av->aigs[i]));
    assert(!bzla_aig_is_const(n1->av->aigs[i]));
  }
  TEST_CBITS_CLEAN_UP_NODES;
  bzla_sort_release(d_bzla, s);
}

/* add ------------------------------------------------------------ */

/**
 * xxxC + xxxC = xxxC
 */
TEST_F(TestConstBits, add_xxxC)
{
  BzlaNode *n0, *n1, *v0, *v1, *zero, *ones, *add;
  BzlaSortId s1, s3;
  uint32_t i;

  s1 = bzla_sort_bv(d_bzla, 1);
  s3 = bzla_sort_bv(d_bzla, 3);

  zero = bzla_exp_bv_zero(d_bzla, s1);
  ones = bzla_exp_bv_ones(d_bzla, s1);

  v0 = bzla_exp_var(d_bzla, s3, "v0");
  v1 = bzla_exp_var(d_bzla, s3, "v1");

  /* xxx0 + xxx0 = xxx0 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, zero);
  n1  = bzla_exp_bv_concat(d_bzla, v1, zero);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xxx0 + xxx1 = xxx1 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, zero);
  n1  = bzla_exp_bv_concat(d_bzla, v1, ones);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xxx1 + xxx0 = xxx1 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, ones);
  n1  = bzla_exp_bv_concat(d_bzla, v1, zero);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xxx1 + xxx1 = xxx0 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, ones);
  n1  = bzla_exp_bv_concat(d_bzla, v1, ones);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[3]));

  /* clean up */
  TEST_CBITS_CLEAN_UP_NODES_ALL(add);
  bzla_sort_release(d_bzla, s1);
  bzla_sort_release(d_bzla, s3);
}

/**
 * xxCC + xxCC = xxCC
 */
TEST_F(TestConstBits, add_xxCC)
{
  BzlaNode *n0, *n1, *v0, *v1, *zero, *ones, *one, *two, *add;
  BzlaSortId s2;
  uint32_t i;

  s2 = bzla_sort_bv(d_bzla, 2);

  zero = bzla_exp_bv_zero(d_bzla, s2);
  ones = bzla_exp_bv_ones(d_bzla, s2);
  one  = bzla_exp_bv_one(d_bzla, s2);
  two  = bzla_exp_bv_int(d_bzla, 2, s2);

  v0 = bzla_exp_var(d_bzla, s2, "v0");
  v1 = bzla_exp_var(d_bzla, s2, "v1");

  /* xx00 + xx00 = xx00 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, zero);
  n1  = bzla_exp_bv_concat(d_bzla, v1, zero);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_false(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx01 + xx00 = xx01 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, one);
  n1  = bzla_exp_bv_concat(d_bzla, v1, zero);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[2]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx10 + xx00 = xx10 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, two);
  n1  = bzla_exp_bv_concat(d_bzla, v1, zero);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[2]));
  assert(bzla_aig_is_false(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx11 + xx00 = xx11 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, ones);
  n1  = bzla_exp_bv_concat(d_bzla, v1, zero);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_true(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx00 + xx01 = xx01 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, zero);
  n1  = bzla_exp_bv_concat(d_bzla, v1, one);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[2]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx00 + xx10 = xx10 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, zero);
  n1  = bzla_exp_bv_concat(d_bzla, v1, two);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[2]));
  assert(bzla_aig_is_false(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx00 + xx11 = xx11 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, zero);
  n1  = bzla_exp_bv_concat(d_bzla, v1, ones);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_true(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx01 + xx01 = xx10 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, one);
  n1  = bzla_exp_bv_concat(d_bzla, v1, one);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[2]));
  assert(bzla_aig_is_false(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx10 + xx01 = xx11 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, two);
  n1  = bzla_exp_bv_concat(d_bzla, v1, one);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_true(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx11 + xx01 = xx00 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, ones);
  n1  = bzla_exp_bv_concat(d_bzla, v1, one);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_false(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx01 + xx10 = xx11 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, one);
  n1  = bzla_exp_bv_concat(d_bzla, v1, two);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_true(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx10 + xx10 = xx00 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, two);
  n1  = bzla_exp_bv_concat(d_bzla, v1, two);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_false(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx11 + xx10 = xx01 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, ones);
  n1  = bzla_exp_bv_concat(d_bzla, v1, two);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[2]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx01 + xx11 = xx00 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, one);
  n1  = bzla_exp_bv_concat(d_bzla, v1, ones);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert(bzla_aig_is_false(add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx10 + xx11 = xx01 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, two);
  n1  = bzla_exp_bv_concat(d_bzla, v1, ones);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[2]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* xx11 + xx11 = xx10 */
  n0  = bzla_exp_bv_concat(d_bzla, v0, ones);
  n1  = bzla_exp_bv_concat(d_bzla, v1, ones);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 2; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[2]));
  assert(bzla_aig_is_false(add->av->aigs[3]));

  /* clean up */
  TEST_CBITS_CLEAN_UP_NODES_ALL(add);
  bzla_node_release(d_bzla, one);
  bzla_node_release(d_bzla, two);
  bzla_sort_release(d_bzla, s2);
}

/**
 * CxxC + CxxC = xxxC
 */
TEST_F(TestConstBits, add_CxxC)
{
  BzlaNode *n0, *n1, *v0, *v1, *zero, *ones, *add, *tmp;
  BzlaSortId s1, s2;
  uint32_t i;

  s1 = bzla_sort_bv(d_bzla, 1);
  s2 = bzla_sort_bv(d_bzla, 2);

  zero = bzla_exp_bv_zero(d_bzla, s1);
  ones = bzla_exp_bv_ones(d_bzla, s1);

  v0 = bzla_exp_var(d_bzla, s2, "v0");
  v1 = bzla_exp_var(d_bzla, s2, "v1");

  /* 0xx0 + 0xx0 = xxx0 */
  tmp = bzla_exp_bv_concat(d_bzla, v0, zero);
  n0  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  tmp = bzla_exp_bv_concat(d_bzla, v1, zero);
  n1  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* 0xx1 + 0xx0 = xxx1 */
  tmp = bzla_exp_bv_concat(d_bzla, v0, ones);
  n0  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  tmp = bzla_exp_bv_concat(d_bzla, v1, zero);
  n1  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* 0xx0 + 0xx1 = xxx1 */
  tmp = bzla_exp_bv_concat(d_bzla, v0, zero);
  n0  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  tmp = bzla_exp_bv_concat(d_bzla, v1, ones);
  n1  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_true(add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(add);

  /* 0xx1 + 0xx1 = xxx0 */
  tmp = bzla_exp_bv_concat(d_bzla, v0, ones);
  n0  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  tmp = bzla_exp_bv_concat(d_bzla, v1, ones);
  n1  = bzla_exp_bv_concat(d_bzla, zero, tmp);
  bzla_node_release(d_bzla, tmp);
  add = bzla_exp_bv_add(d_bzla, n0, n1);
  bzla_synthesize_exp(d_bzla, add, 0);
  for (i = 0; i < 3; i++) assert(!bzla_aig_is_const(add->av->aigs[i]));
  assert(bzla_aig_is_false(add->av->aigs[3]));

  /* clean up */
  TEST_CBITS_CLEAN_UP_NODES_ALL(add);
  bzla_sort_release(d_bzla, s1);
  bzla_sort_release(d_bzla, s2);
}
