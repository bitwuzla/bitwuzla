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
}

class TestMap : public TestBzla
{
};

TEST_F(TestMap, new_delete)
{
  BzlaNodeMap *map;
  map = bzla_nodemap_new(d_bzla);
  bzla_nodemap_delete(map);
}

TEST_F(TestMap, map0)
{
  Bzla *bzla_a, *bzla_b;
  BzlaNode *s, *d, *m;
  BzlaNodeMap *map;
  BzlaSortId sort;

  bzla_a = bzla_new();
  bzla_b = bzla_new();

  sort = bzla_sort_bv(bzla_a, 32);
  s    = bzla_exp_var(bzla_a, sort, "s");
  bzla_sort_release(bzla_a, sort);

  sort = bzla_sort_bv(bzla_b, 32);
  d    = bzla_exp_var(bzla_b, sort, "d");
  bzla_sort_release(bzla_b, sort);

  map = bzla_nodemap_new(d_bzla);
  bzla_nodemap_map(map, s, d);
  m = bzla_nodemap_mapped(map, s);
  ASSERT_EQ(m, d);

  bzla_node_release(bzla_a, s);
  bzla_node_release(bzla_b, d);
  bzla_nodemap_delete(map);
  bzla_delete(bzla_a);
  bzla_delete(bzla_b);
}

TEST_F(TestMap, map1)
{
  Bzla *bzla_a;
  BzlaNode *s, *t, *a, *m;
  BzlaSortId sort;
  BzlaNodeMap *map;

  bzla_a = bzla_new();
  sort   = bzla_sort_bv(bzla_a, 32);
  s      = bzla_exp_var(bzla_a, sort, "0");
  t      = bzla_exp_var(bzla_a, sort, "1");
  a      = bzla_exp_bv_and(bzla_a, s, t);
  map    = bzla_nodemap_new(d_bzla);
  bzla_nodemap_map(map, s, a);
  m = bzla_nodemap_mapped(map, s);
  ASSERT_EQ(m, a);

  bzla_sort_release(bzla_a, sort);
  bzla_node_release(bzla_a, t);
  bzla_node_release(bzla_a, s);
  bzla_node_release(bzla_a, a);
  bzla_nodemap_delete(map);
  bzla_delete(bzla_a);
}
