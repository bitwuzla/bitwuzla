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
#include "bzlasort.h"
}

class TestSort : public TestBzla
{
};

TEST_F(TestSort, bool)
{
  BzlaSortId s0, s1;

  s0 = bzla_sort_bool(d_bzla);
  s1 = bzla_sort_bool(d_bzla);
  ASSERT_EQ(s0, s1);
  bzla_sort_release(d_bzla, s0);
  bzla_sort_release(d_bzla, s1);
}

TEST_F(TestSort, bitvec)
{
  int32_t i, j;
  BzlaSortId s0, s1;

  for (i = 1; i <= 128; i++)
  {
    s0 = bzla_sort_bv(d_bzla, i);
    for (j = 1; j <= 128; j++)
    {
      s1 = bzla_sort_bv(d_bzla, j);
      ASSERT_TRUE(i != j || s0 == s1);
      ASSERT_TRUE(i == j || s0 != s1);
      bzla_sort_release(d_bzla, s1);
    }
    bzla_sort_release(d_bzla, s0);
  }
}

TEST_F(TestSort, array)
{
  int32_t i, j, k, l;
  BzlaSortId s0, s1, s2, s3, a0, a1;

  for (i = 1; i <= 16; i++)
  {
    s0 = bzla_sort_bv(d_bzla, i);
    for (j = 1; j <= 8; j++)
    {
      s1 = bzla_sort_bv(d_bzla, j);
      a0 = bzla_sort_array(d_bzla, s0, s1);
      for (k = 1; k <= 16; k++)
      {
        s2 = bzla_sort_bv(d_bzla, k);
        for (l = 1; l <= 8; l++)
        {
          s3 = bzla_sort_bv(d_bzla, l);
          a1 = bzla_sort_array(d_bzla, s2, s3);
          ASSERT_TRUE(!(i == k && j == l) || a0 == a1);
          ASSERT_TRUE((i == k && j == l) || a0 != a1);
          bzla_sort_release(d_bzla, a1);
          bzla_sort_release(d_bzla, s3);
        }
        bzla_sort_release(d_bzla, s2);
      }
      bzla_sort_release(d_bzla, a0);
      bzla_sort_release(d_bzla, s1);
    }
    bzla_sort_release(d_bzla, s0);
  }
}

#if 0
// TODO: more tests with different sorts (not only bitvec)
TEST_F (TestSort, lst)
{
  BzlaSortId a, b, c, d, l0, l1, l2, l3, l4, l5, l6;

  a = bzla_sort_bv (d_bzla, 2);
  b = bzla_sort_bv (d_bzla, 7);
  c = bzla_sort_bv (d_bzla, 1023);
  d = bzla_sort_bv (d_bzla, 53);

  l0 = bzla_sort_lst (d_bzla, a, b);
  l1 = bzla_sort_lst (d_bzla, l0, c);
  l2 = bzla_sort_lst (d_bzla, l1, d);

  l3 = bzla_sort_lst (d_bzla, a, b);
  l4 = bzla_sort_lst (d_bzla, l3, c);
  l5 = bzla_sort_lst (d_bzla, l4, d);

  ASSERT_EQ (l2, l5);

  bzla_sort_release (d_bzla, l3);
  bzla_sort_release (d_bzla, l4);
  bzla_sort_release (d_bzla, l5);

  l3 = bzla_sort_lst (d_bzla, b, a);
  l4 = bzla_sort_lst (d_bzla, l3, c);
  l5 = bzla_sort_lst (d_bzla, l4, d);

  ASSERT_NE (l2, l5);

  l6 = bzla_sort_lst (d_bzla, l5, l5);

  ASSERT_NE (l6, l2);
  ASSERT_NE (l5, l6);

  bzla_sort_release (d_bzla, a);
  bzla_sort_release (d_bzla, b);
  bzla_sort_release (d_bzla, c);
  bzla_sort_release (d_bzla, d);
  bzla_sort_release (d_bzla, l0);
  bzla_sort_release (d_bzla, l1);
  bzla_sort_release (d_bzla, l2);
  bzla_sort_release (d_bzla, l3);
  bzla_sort_release (d_bzla, l4);
  bzla_sort_release (d_bzla, l5);
  bzla_sort_release (d_bzla, l6);
}
#endif

TEST_F(TestSort, fun)
{
  BzlaSortId a, b, c, s0[2], s1[2], f0, f1, f2, t0, t1, t2;

  a     = bzla_sort_bv(d_bzla, 53);
  b     = bzla_sort_bv(d_bzla, 1);
  c     = bzla_sort_bool(d_bzla);
  s0[0] = a;
  s0[1] = b;
  t0    = bzla_sort_tuple(d_bzla, s0, 2);
  f0    = bzla_sort_fun(d_bzla, t0, c);

  s1[0] = b;
  s1[1] = a;
  t1    = bzla_sort_tuple(d_bzla, s1, 2);
  f1    = bzla_sort_fun(d_bzla, t1, c);
  ASSERT_NE(f0, f1);

  t2 = bzla_sort_tuple(d_bzla, s0, 2);
  f2 = bzla_sort_fun(d_bzla, t2, c);
  ASSERT_EQ(f0, f2);

  bzla_sort_release(d_bzla, a);
  bzla_sort_release(d_bzla, b);
  bzla_sort_release(d_bzla, c);
  bzla_sort_release(d_bzla, f0);
  bzla_sort_release(d_bzla, f1);
  bzla_sort_release(d_bzla, f2);
  bzla_sort_release(d_bzla, t0);
  bzla_sort_release(d_bzla, t1);
  bzla_sort_release(d_bzla, t2);
}

TEST_F(TestSort, tuple)
{
  BzlaSortId a, b, c, d, e[4], t0, t1;

  a = bzla_sort_bv(d_bzla, 53);
  b = bzla_sort_bv(d_bzla, 7);
  c = bzla_sort_bool(d_bzla);
  d = bzla_sort_array(d_bzla, b, a);

  e[0] = a;
  e[1] = b;
  e[2] = c;
  e[3] = d;

  t0 = bzla_sort_tuple(d_bzla, e, 4);
  t1 = bzla_sort_tuple(d_bzla, e, 4);
  ASSERT_EQ(t0, t1);
  bzla_sort_release(d_bzla, t1);

  e[0] = d;
  e[1] = c;
  e[2] = b;
  e[3] = a;
  t1   = bzla_sort_tuple(d_bzla, e, 4);
  ASSERT_NE(t1, t0);

  bzla_sort_release(d_bzla, t0);
  t0 = bzla_sort_tuple(d_bzla, e, 3);
  ASSERT_NE(t0, t1);

  bzla_sort_release(d_bzla, a);
  bzla_sort_release(d_bzla, b);
  bzla_sort_release(d_bzla, c);
  bzla_sort_release(d_bzla, d);
  bzla_sort_release(d_bzla, t0);
  bzla_sort_release(d_bzla, t1);
}
