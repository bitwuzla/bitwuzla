/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/backtrackable.h"
#include "env.h"
#include "node/node_manager.h"
#include "preprocess/simplify_cache.h"
#include "test.h"

namespace bzla::test {

class TestSimplifyCache : public TestCommon
{
 protected:
  NodeManager d_nm;
  backtrack::BacktrackManager d_backtrack_mgr;
};

TEST_F(TestSimplifyCache, ctor_dtor)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");
}

TEST_F(TestSimplifyCache, cache1)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");

  Type bt = d_nm.mk_bool_type();
  Node x  = d_nm.mk_const(bt, "x");
  Node y  = d_nm.mk_const(bt, "y");

  cache.add(x, y, preprocess::SimplifyCache::Cacher::REWRITER);
  ASSERT_EQ(cache.get(x), y);
  ASSERT_EQ(cache.get(y), y);
}

TEST_F(TestSimplifyCache, cache2)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");

  Type bt = d_nm.mk_bool_type();
  Node x  = d_nm.mk_const(bt, "x");
  Node y  = d_nm.mk_const(bt, "y");
  Node z  = d_nm.mk_const(bt, "z");

  cache.add(x, y, preprocess::SimplifyCache::Cacher::REWRITER);
  cache.add(y, z, preprocess::SimplifyCache::Cacher::REWRITER);
  ASSERT_EQ(cache.get(x), z);
  ASSERT_EQ(cache.get(y), z);
  ASSERT_EQ(cache.get(z), z);
}

TEST_F(TestSimplifyCache, cache3)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");

  Type bt = d_nm.mk_bool_type();
  Node u  = d_nm.mk_const(bt, "u");
  Node v  = d_nm.mk_const(bt, "v");
  Node w  = d_nm.mk_const(bt, "w");
  Node x  = d_nm.mk_const(bt, "x");
  Node y  = d_nm.mk_const(bt, "y");
  Node z  = d_nm.mk_const(bt, "z");

  cache.add(u, v, preprocess::SimplifyCache::Cacher::REWRITER);
  cache.add(v, w, preprocess::SimplifyCache::Cacher::REWRITER);
  cache.add(w, x, preprocess::SimplifyCache::Cacher::REWRITER);

  cache.add(x, y, preprocess::SimplifyCache::Cacher::REWRITER);
  cache.add(y, z, preprocess::SimplifyCache::Cacher::REWRITER);
  ASSERT_EQ(cache.get(x), z);
  ASSERT_EQ(cache.get(y), z);
  ASSERT_EQ(cache.get(z), z);
  ASSERT_EQ(cache.get(u), z);
  ASSERT_EQ(cache.get(v), z);
  ASSERT_EQ(cache.get(w), z);
}

TEST_F(TestSimplifyCache, cache4)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");

  Type bt = d_nm.mk_bool_type();
  Node w  = d_nm.mk_const(bt, "w");
  Node x  = d_nm.mk_const(bt, "x");
  Node y  = d_nm.mk_const(bt, "y");
  Node z  = d_nm.mk_const(bt, "z");

  cache.add(x, w, preprocess::SimplifyCache::Cacher::REWRITER);
  cache.add(y, x, preprocess::SimplifyCache::Cacher::REWRITER);
  d_backtrack_mgr.push();
  cache.add(z, y, preprocess::SimplifyCache::Cacher::REWRITER);
  ASSERT_EQ(cache.size(), 3);
  ASSERT_EQ(cache.get(w), w);
  ASSERT_EQ(cache.get(z), w);
  ASSERT_EQ(cache.get(x), w);
  ASSERT_EQ(cache.get(y), w);
  d_backtrack_mgr.pop();
  ASSERT_EQ(cache.size(), 2);
  ASSERT_EQ(cache.get(z), z);
  ASSERT_EQ(cache.get(x), w);
  ASSERT_EQ(cache.get(y), w);
  ASSERT_EQ(cache.get(w), w);
}

TEST_F(TestSimplifyCache, cache5)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");

  Type bt = d_nm.mk_bool_type();
  Node x  = d_nm.mk_const(bt, "x");
  Node y  = d_nm.mk_const(bt, "y");
  Node z  = d_nm.mk_const(bt, "z");

  cache.add(x, y, preprocess::SimplifyCache::Cacher::REWRITER);
  d_backtrack_mgr.push();
  cache.add(z, x, preprocess::SimplifyCache::Cacher::REWRITER);
  ASSERT_EQ(cache.size(), 2);
  ASSERT_EQ(cache.get(z), y);
  ASSERT_EQ(cache.get(x), y);
  ASSERT_EQ(cache.get(y), y);
  d_backtrack_mgr.pop();
  ASSERT_EQ(cache.size(), 1);
  ASSERT_EQ(cache.get(z), z);
  ASSERT_EQ(cache.get(x), y);
  ASSERT_EQ(cache.get(y), y);
}

TEST_F(TestSimplifyCache, cache6)
{
  Env env(d_nm);
  preprocess::SimplifyCache cache(env, &d_backtrack_mgr, "test");

  Type bt = d_nm.mk_bool_type();
  Node u  = d_nm.mk_const(bt, "u");
  Node z  = d_nm.mk_const(bt, "z");

  {
    // x and y are intermediate nodes (no external references)
    Node x = d_nm.mk_const(bt, "x");
    Node y = d_nm.mk_const(bt, "y");
    cache.add(u, x, preprocess::SimplifyCache::Cacher::REWRITER);
    cache.add(x, y, preprocess::SimplifyCache::Cacher::REWRITER);
    cache.add(y, z, preprocess::SimplifyCache::Cacher::REWRITER);
  }

  ASSERT_EQ(cache.size(), 3);
  ASSERT_EQ(cache.get(u), z);
  // x and y are deleted during path compression since they have no references
  // anymore
  ASSERT_EQ(cache.size(), 1);
}

}  // namespace bzla::test
