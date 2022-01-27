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
#include "utils/bzlaunionfind.h"
}

class TestUnionFind : public TestBzla
{
 protected:
  void SetUp() override
  {
    TestBzla::SetUp();
    d_mm   = d_bzla->mm;
    d_sort = bzla_sort_bv(d_bzla, 32);
  }

  void TearDown() override
  {
    bzla_sort_release(d_bzla, d_sort);
    TestBzla::TearDown();
  }

  BzlaMemMgr *d_mm  = nullptr;
  BzlaSortId d_sort = 0;
};

TEST_F(TestUnionFind, test1)
{
  BzlaUnionFind *ufind = bzla_ufind_new(d_mm);

  BzlaNode *x = bzla_exp_var(d_bzla, d_sort, "x");

  bzla_ufind_add(ufind, x);

  ASSERT_EQ(bzla_ufind_get_repr(ufind, x), x);

  bzla_ufind_add(ufind, x);

  ASSERT_EQ(bzla_ufind_get_repr(ufind, x), x);

  bzla_node_release(d_bzla, x);

  bzla_ufind_delete(ufind);
}

TEST_F(TestUnionFind, test2)
{
  BzlaUnionFind *ufind = bzla_ufind_new(d_mm);

  BzlaNode *x = bzla_exp_var(d_bzla, d_sort, "x");
  BzlaNode *y = bzla_exp_var(d_bzla, d_sort, "y");

  bzla_ufind_merge(ufind, x, y);
  ASSERT_EQ(bzla_ufind_get_repr(ufind, x), bzla_ufind_get_repr(ufind, y));
  ASSERT_TRUE(bzla_ufind_is_equal(ufind, x, y));
  ASSERT_EQ(bzla_ufind_get_repr(ufind, y), x);

  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, y);

  bzla_ufind_delete(ufind);
}

TEST_F(TestUnionFind, test3)
{
  BzlaUnionFind *ufind = bzla_ufind_new(d_mm);

  BzlaNode *x = bzla_exp_var(d_bzla, d_sort, "x");
  BzlaNode *y = bzla_exp_var(d_bzla, d_sort, "y");
  BzlaNode *z = bzla_exp_var(d_bzla, d_sort, "z");

  bzla_ufind_merge(ufind, x, y);
  bzla_ufind_merge(ufind, y, z);
  ASSERT_EQ(bzla_ufind_get_repr(ufind, x), bzla_ufind_get_repr(ufind, z));
  ASSERT_EQ(bzla_ufind_get_repr(ufind, z), x);

  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, z);

  bzla_ufind_delete(ufind);
}

TEST_F(TestUnionFind, test4)
{
  BzlaUnionFind *ufind = bzla_ufind_new(d_mm);

  BzlaNode *w = bzla_exp_var(d_bzla, d_sort, "w");
  BzlaNode *x = bzla_exp_var(d_bzla, d_sort, "x");
  BzlaNode *y = bzla_exp_var(d_bzla, d_sort, "y");
  BzlaNode *z = bzla_exp_var(d_bzla, d_sort, "z");

  bzla_ufind_merge(ufind, w, x);
  bzla_ufind_merge(ufind, y, z);
  ASSERT_NE(bzla_ufind_get_repr(ufind, x), bzla_ufind_get_repr(ufind, y));

  bzla_ufind_merge(ufind, x, z);

  ASSERT_EQ(bzla_ufind_get_repr(ufind, x), bzla_ufind_get_repr(ufind, y));
  ASSERT_EQ(bzla_ufind_get_repr(ufind, w), bzla_ufind_get_repr(ufind, z));

  bzla_node_release(d_bzla, w);
  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, y);
  bzla_node_release(d_bzla, z);

  bzla_ufind_delete(ufind);
}

TEST_F(TestUnionFind, test5)
{
  BzlaUnionFind *ufind = bzla_ufind_new(d_mm);

  BzlaNode *x     = bzla_exp_var(d_bzla, d_sort, "x");
  BzlaNode *not_x = bzla_exp_bv_not(d_bzla, x);

  bzla_ufind_add(ufind, x);
  bzla_ufind_add(ufind, not_x);

  ASSERT_EQ(bzla_ufind_get_repr(ufind, x), x);
  ASSERT_EQ(bzla_ufind_get_repr(ufind, not_x), not_x);
  ASSERT_FALSE(bzla_ufind_is_equal(ufind, x, not_x));

  bzla_ufind_merge(ufind, x, not_x);

  ASSERT_TRUE(bzla_ufind_is_equal(ufind, x, not_x));

  bzla_node_release(d_bzla, x);
  bzla_node_release(d_bzla, not_x);

  bzla_ufind_delete(ufind);
}
