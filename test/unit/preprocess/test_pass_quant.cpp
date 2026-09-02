/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "node/node_utils.h"
#include "preprocess/pass/quant.h"
#include "sat/sat_solver_factory.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassQuant : public TestPreprocessingPass
{
 public:
  TestPassQuant()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory, d_options),
        d_pass(d_env, &d_bm)
  {
    d_bv2 = d_nm.mk_bv_type(2);
  };

  std::unordered_map<Node, std::unordered_set<Node>> collect_binders(
      const std::vector<Node>& roots)
  {
    std::unordered_map<Node, std::unordered_set<Node>> binders;
    std::unordered_set<Node> cache;
    std::vector<Node> visit(roots);
    while (!visit.empty())
    {
      Node cur = visit.back();
      visit.pop_back();
      if (!cache.insert(cur).second)
      {
        continue;
      }
      if (cur.kind() == Kind::FORALL)
      {
        binders[cur[0]].insert(cur);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    return binders;
  }

 protected:
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  preprocess::pass::PassQuant d_pass;
  Type d_bv2;
};

TEST_F(TestPassQuant, uniquify_binders_nested1)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");

  // (forall x. (forall x. (bvule x c))) -- x bound by two binders.
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x, d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})})});

  d_as.push_back(q1);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_nested2)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");
  Node y = d_nm.mk_var(d_bv2, "y");

  // (forall x. (and (forall x. (bvule x c)) (forall y. (bvule y x)
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x,
       d_nm.mk_node(
           Kind::AND,
           {d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})}),
            d_nm.mk_node(Kind::FORALL,
                         {y, d_nm.mk_node(Kind::BV_ULE, {y, x})})})});

  d_as.push_back(q1);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_nested3)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");

  // (forall x. (forall x. (forall x. (bvule x c)))) -- x shadowed down to the
  // innermost binder.
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x,
       d_nm.mk_node(Kind::FORALL,
                    {x,
                     d_nm.mk_node(Kind::FORALL,
                                  {x, d_nm.mk_node(Kind::BV_ULE, {x, c})})})});

  d_as.push_back(q1);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  ASSERT_EQ(binders.size(), 3);
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_nested3_shared_body)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");

  // The same node `(bvule x c)` occurs at all three levels, i.e., it must be
  // mapped to a different node for each of the three binders of `x`.
  Node b  = d_nm.mk_node(Kind::BV_ULE, {x, c});
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x,
       d_nm.mk_node(
           Kind::AND,
           {b,
            d_nm.mk_node(
                Kind::FORALL,
                {x,
                 d_nm.mk_node(Kind::AND,
                              {b, d_nm.mk_node(Kind::FORALL, {x, b})})})})});

  d_as.push_back(q1);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  ASSERT_EQ(binders.size(), 3);
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_shared_shadowing_binder)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node e = d_nm.mk_const(d_bv2, "e");
  Node x = d_nm.mk_var(d_bv2, "x");

  // Shadowing binder, shared by two parents.
  Node n  = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})});
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x,
       d_nm.mk_node(
           Kind::AND,
           {d_nm.mk_node(Kind::OR, {n, d_nm.mk_node(Kind::BV_ULE, {x, d})}),
            d_nm.mk_node(Kind::OR, {n, d_nm.mk_node(Kind::BV_ULE, {x, e})})})});

  d_as.push_back(q1);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  ASSERT_EQ(binders.size(), 2);
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_shadowing_binder_two_parents)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node e = d_nm.mk_const(d_bv2, "e");
  Node x = d_nm.mk_var(d_bv2, "x");

  // Shadowing binder `n`, shared by two distinct parents (i1 and i2), i.e.,
  // it is visited twice while determining which nodes reference `x`.
  Node n  = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})});
  Node i1 = d_nm.mk_node(Kind::ITE, {n, d, e});
  Node i2 = d_nm.mk_node(Kind::ITE, {n, e, d});
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x,
       d_nm.mk_node(Kind::AND,
                    {d_nm.mk_node(Kind::BV_ULE,
                                  {d_nm.mk_node(Kind::BV_ADD, {i1, x}), c}),
                     d_nm.mk_node(Kind::BV_ULE,
                                  {d_nm.mk_node(Kind::BV_ADD, {i2, x}), d})})});

  d_as.push_back(q1);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  ASSERT_EQ(binders.size(), 2);
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_across)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");

  // Nested: (forall x. (forall x. (bvule x c))) -- x bound by two binders.
  Node q1 = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})});
  // Across assertions: another binder of the same variable node x.
  Node q2 = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {c, x})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_nested_across)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");

  // Nested: (forall x. (forall x. (bvule x c))) -- x bound by two binders.
  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {x, d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})})});
  // Across assertions: another binder of the same variable node x.
  Node q2 = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {c, x})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_across_deep_body)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node x = d_nm.mk_var(d_bv2, "x");

  Node q1 = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, c})});
  // Across assertions: another binder of the same variable node x. Its body
  // contains an interior node (bvadd x c), which is more than one level below
  // the binder and thus never visited (and cached) by the outer traversal.
  Node q2 = d_nm.mk_node(
      Kind::FORALL,
      {x, d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_ADD, {x, c}), c})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}
TEST_F(TestPassQuant, uniquify_binders_shared_open_subterm)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c1 = d_nm.mk_const(d_bv2, "c1");
  Node c2 = d_nm.mk_const(d_bv2, "c2");
  Node v  = d_nm.mk_var(d_bv2, "v");
  Node w  = d_nm.mk_var(d_bv2, "w");

  // Open subterm, shared by q1 and q2, referencing the shared binder variable
  // `v`. Uniquifying `v` copies `n`, i.e., its binder must be uniquified, too.
  Node n = d_nm.mk_node(Kind::FORALL, {w, d_nm.mk_node(Kind::BV_ULE, {v, w})});

  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {v, d_nm.mk_node(Kind::OR, {n, d_nm.mk_node(Kind::BV_ULE, {c1, v})})});
  Node q2 = d_nm.mk_node(
      Kind::FORALL,
      {v, d_nm.mk_node(Kind::OR, {n, d_nm.mk_node(Kind::BV_ULE, {c2, v})})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_sibling_shared_nested)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node v = d_nm.mk_var(d_bv2, "v");
  Node w = d_nm.mk_var(d_bv2, "w");

  // Sibling binders of the same variable node `w`, both referencing `v`.
  Node n1 = d_nm.mk_node(Kind::FORALL, {w, d_nm.mk_node(Kind::BV_ULE, {v, w})});
  Node n2 = d_nm.mk_node(Kind::FORALL, {w, d_nm.mk_node(Kind::BV_ULE, {w, v})});

  // q1 registers binder variable `v` first, i.e., the binder of q2 is the one
  // that is uniquified -- which copies both sibling binders of `w`.
  Node q1 = d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {c, v})});
  Node q2 = d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::AND, {n1, n2})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, uniquify_binders_across_inner_rename)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node v = d_nm.mk_var(d_bv2, "v");
  Node w = d_nm.mk_var(d_bv2, "w");

  // q1 binds variable `v` first (asserted first, processed first). Thus, the
  // binder of q2 is the one that is uniquified, and as a consequence, `w` is
  // rebound, too. The second conjunct of q2's body does not reference `v`, but
  // must still be rebuilt with the fresh variable of `w`.
  Node q1 = d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {c, v})});
  Node q2 = d_nm.mk_node(
      Kind::FORALL,
      {v,
       d_nm.mk_node(Kind::FORALL,
                    {w,
                     d_nm.mk_node(Kind::AND,
                                  {d_nm.mk_node(Kind::BV_ULE, {v, c}),
                                   d_nm.mk_node(Kind::BV_ULE, {w, c})})})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
  // No occurrence must be left on the original variable of `w`, which would
  // be free in the result (and its fresh variable unused).
  ASSERT_FALSE(pass.has_free_vars(assertions[1]).first);
}

TEST_F(TestPassQuant, uniquify_binders_sibling_inner_rename)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node v = d_nm.mk_var(d_bv2, "v");
  Node w = d_nm.mk_var(d_bv2, "w");

  // As above, but both binders of `v` are in the same assertion, i.e.,
  // uniquification within one assertion is already sufficient to trigger this.
  Node q1 = d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {c, v})});
  Node q2 = d_nm.mk_node(
      Kind::FORALL,
      {v,
       d_nm.mk_node(Kind::FORALL,
                    {w,
                     d_nm.mk_node(Kind::AND,
                                  {d_nm.mk_node(Kind::BV_ULE, {v, c}),
                                   d_nm.mk_node(Kind::BV_ULE, {w, c})})})});
  d_as.push_back(
      d_nm.mk_node(Kind::ITE, {d_nm.mk_node(Kind::BV_ULE, {c, d}), q2, q1}));
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);

  // Every variable must now be bound by exactly one binder.
  auto binders = collect_binders({assertions[0]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
  ASSERT_FALSE(pass.has_free_vars(assertions[0]).first);
}

TEST_F(TestPassQuant, uniquify_binders_shadowing_binder_below_inner_rename)
{
  d_options.pp_quant_alpha.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  Env env(d_nm, sat_factory, d_options);
  preprocess::pass::PassQuant pass(env, &d_bm);

  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node x = d_nm.mk_var(d_bv2, "x");
  Node y = d_nm.mk_var(d_bv2, "y");

  // Shadowing binder of `x` below a binder (`y`) that references the outer `x`
  // and is therefore uniquified.
  Node shadow =
      d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::BV_ULE, {x, d})});
  Node q = d_nm.mk_node(
      Kind::FORALL,
      {x,
       d_nm.mk_node(
           Kind::FORALL,
           {y,
            d_nm.mk_node(Kind::AND,
                         {d_nm.mk_node(Kind::BV_ULE, {x, c}), shadow})})});
  d_as.push_back(q);
  preprocess::AssertionVector assertions(d_as.view());
  pass.apply(assertions);
  auto binders = collect_binders({assertions[0]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
  ASSERT_FALSE(pass.has_free_vars(assertions[0]).first);
}

// Corresponds to test regress/preprocess/quant/alpha6.smt2 and serves as an
// isolated test case (only the quant preprocessing pass is applied, no SAT
// solver involved).
TEST_F(TestPassQuant, alpha6_no_merge_of_non_equivalent_quants)
{
  Node body;
  Node g = d_nm.mk_const(d_bv2, "g");
  Node h = d_nm.mk_const(d_bv2, "h");
  Node k = d_nm.mk_const(d_bv2, "k");
  //(define-fun block () Bool
  //  (forall ((o (_ BitVec 2)))
  //    (and (forall ((p (_ BitVec 2)) (q (_ BitVec 2))) (bvule (bvand p q) k))
  //         (bvule o k))))
  Node p = d_nm.mk_var(d_bv2, "p");
  Node q = d_nm.mk_var(d_bv2, "q");
  Node o = d_nm.mk_var(d_bv2, "o");
  body   = d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_AND, {p, q}), k});
  Node forall_q  = d_nm.mk_node(Kind::FORALL, {q, body});
  Node forall_pq = d_nm.mk_node(Kind::FORALL, {p, forall_q});
  Node block     = d_nm.mk_node(
      Kind::FORALL,
      {o,
       d_nm.mk_node(Kind::AND,
                    {forall_pq, d_nm.mk_node(Kind::BV_ULE, {o, k})})});

  // (assert (not (forall ((x (_ BitVec 2)))
  //   (and (forall ((v (_ BitVec 2))) (bvule (bvadd v g) x))
  //        block
  //        (bvule x h)))))
  Node x = d_nm.mk_var(d_bv2, "x");
  Node v = d_nm.mk_var(d_bv2, "v");
  body   = d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_ADD, {v, g}), x});
  Node forall_v = d_nm.mk_node(Kind::FORALL, {v, body});
  body          = d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::BV_ULE, {x, h}),
                                d_nm.mk_node(Kind::AND, {block, forall_v})});
  Node forall_x = d_nm.mk_node(Kind::FORALL, {x, body});

  // (assert (forall ((x2 (_ BitVec 2)))
  //   (and (forall ((v2 (_ BitVec 2))) (bvule (bvadd v2 g) v2))
  //        block
  //        (bvule x2 h))))
  Node x2 = d_nm.mk_var(d_bv2, "x2");
  Node v2 = d_nm.mk_var(d_bv2, "v2");
  body = d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_ADD, {v2, g}), v2});
  Node forall_v2 = d_nm.mk_node(Kind::FORALL, {v2, body});
  body           = d_nm.mk_node(Kind::AND,
                                {d_nm.mk_node(Kind::BV_ULE, {x2, h}),
                                 d_nm.mk_node(Kind::AND, {block, forall_v2})});
  Node forall_x2 = d_nm.mk_node(Kind::FORALL, {x2, body});

  d_as.push_back(forall_x);
  d_as.push_back(forall_x2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // forall_x and forall_x2 are not alpha-equivalent and must not be merged.
  ASSERT_NE(assertions[0], assertions[1]);

  // No variable bound by more than one binder.
  auto binders = collect_binders({assertions[0], assertions[1]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, alpha_shared_binder1)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node z = d_nm.mk_var(d_bv2, "z");
  Node v = d_nm.mk_var(d_bv2, "v");
  Node u = d_nm.mk_var(d_bv2, "u");

  // closed_v and closed_u are alpha equivalent.
  Node closed_v =
      d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, c})});
  Node closed_u =
      d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::BV_ULE, {u, c})});

  // body_z and closed_v share the binder variable node `v`.
  Node body_z =
      d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, z})});
  Node q = d_nm.mk_node(
      Kind::FORALL,
      {z,
       d_nm.mk_node(Kind::AND,
                    {d_nm.mk_node(Kind::AND, {closed_v, closed_u}), body_z})});

  d_as.push_back(q);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  Node before = d_env.rewriter().rewrite(assertions[0]);
  d_pass.apply(assertions);
  ASSERT_NE(before, assertions[0]);
  ASSERT_EQ(d_env.statistics().new_or_get_stat<uint64_t>(
                "preprocess::quant::num_alpha_elim"),
            1);

  // No variable bound by more than one binder.
  auto binders = collect_binders({assertions[0]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
  ASSERT_EQ(binders.size(), 3u);
}

TEST_F(TestPassQuant, alpha_shared_binder2)
{
  Node c1 = d_nm.mk_const(d_bv2, "c1");
  Node c2 = d_nm.mk_const(d_bv2, "c2");
  Node v  = d_nm.mk_var(d_bv2, "v");
  Node a  = d_nm.mk_var(d_bv2, "a");
  Node b  = d_nm.mk_var(d_bv2, "b");
  Node w  = d_nm.mk_var(d_bv2, "w");

  Node n = d_nm.mk_node(Kind::FORALL, {w, d_nm.mk_node(Kind::BV_ULE, {v, w})});

  Node q1 = d_nm.mk_node(
      Kind::FORALL,
      {v, d_nm.mk_node(Kind::OR, {n, d_nm.mk_node(Kind::BV_ULE, {c1, v})})});
  Node q2 = d_nm.mk_node(
      Kind::FORALL,
      {v, d_nm.mk_node(Kind::OR, {n, d_nm.mk_node(Kind::BV_ULE, {c2, v})})});
  Node q3 = d_nm.mk_node(
      Kind::FORALL,
      {a,
       d_nm.mk_node(
           Kind::OR,
           {d_nm.mk_node(Kind::FORALL, {b, d_nm.mk_node(Kind::BV_ULE, {b, b})}),
            d_nm.mk_node(Kind::BV_ULE, {c2, a})})});

  d_as.push_back(q1);
  d_as.push_back(q2);
  d_as.push_back(q3);

  preprocess::AssertionVector assertions(d_as.view());
  Node q3_before = d_env.rewriter().rewrite(assertions[2]);
  d_pass.apply(assertions);

  // q3 must NOT be replaced by (the non-equivalent) q2.
  ASSERT_EQ(assertions[2], q3_before);

  // No variable bound by more than one binder.
  auto binders = collect_binders({assertions[0], assertions[1], assertions[2]});
  for (const auto& [var, bs] : binders)
  {
    ASSERT_EQ(bs.size(), 1u);
  }
}

TEST_F(TestPassQuant, has_free_vars)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");

  Node w = d_nm.mk_var(d_bv2, "w");
  Node y = d_nm.mk_var(d_bv2, "y");
  Node b = d_nm.mk_var(d_bv2, "b");

  Node o = d_nm.mk_node(Kind::FORALL, {b, d_nm.mk_node(Kind::BV_ULE, {b, w})});
  Node m = d_nm.mk_node(
      Kind::FORALL,
      {y, d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::BV_ULE, {y, c}), o})});
  Node q = d_nm.mk_node(
      Kind::FORALL,
      {w, d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::BV_ULE, {w, d}), m})});

  d_as.push_back(q);
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  // Note: Unlike apply(), process() does not clear the alpha caches.
  d_pass.process(assertions[0]);

  const Node& norm_m = d_pass.d_alpha_cache.at(d_pass.d_cache.at(m));
  // `w` is free in the alpha-normal form of `m`: it is only renamed when the
  // binder of `w` is normalized, one level further up.
  ASSERT_TRUE(utils::has_x(norm_m, w));
  ASSERT_TRUE(d_pass.has_free_vars(norm_m).first);

  // All three binders of the alpha-normal form of `q` are nested, so each must
  // have its own canonical variable.
  const Node& norm_q = d_pass.d_alpha_cache.at(d_pass.d_cache.at(q));
  ASSERT_EQ(collect_binders({norm_q}).size(), 3u);
}

TEST_F(TestPassQuant, alpha_nested1)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node e = d_nm.mk_const(d_bv2, "e");

  // X: closed, asserted by itself and a subterm of Q
  //    -> its canonical var is acquired + released once
  Node a = d_nm.mk_var(d_bv2, "a");
  Node X = d_nm.mk_node(Kind::FORALL, {a, d_nm.mk_node(Kind::BV_ULE, {a, c})});

  // B: open in variable y
  //    -> reacquires the (now free) canonical var of X
  Node y = d_nm.mk_var(d_bv2, "y");
  Node b = d_nm.mk_var(d_bv2, "b");
  Node B = d_nm.mk_node(Kind::FORALL, {b, d_nm.mk_node(Kind::BV_ULE, {y, b})});

  // Q: closed, contains X
  //    -> has_free_vars() must skip already normalized nodes to not release
  //       canonical variables of closed quants that are atm reacquired by
  //       an open quantifier
  Node qv = d_nm.mk_var(d_bv2, "q");
  Node Q  = d_nm.mk_node(
      Kind::FORALL,
      {qv, d_nm.mk_node(Kind::AND, {X, d_nm.mk_node(Kind::BV_ULE, {qv, d})})});

  Node C = d_nm.mk_node(
      Kind::FORALL,
      {y, d_nm.mk_node(Kind::ITE, {d_nm.mk_node(Kind::BV_ULE, {y, e}), Q, B})});

  Node y2 = d_nm.mk_var(d_bv2, "y2");
  Node b2 = d_nm.mk_var(d_bv2, "b2");
  Node B2 =
      d_nm.mk_node(Kind::FORALL, {b2, d_nm.mk_node(Kind::BV_ULE, {b2, b2})});
  Node C2 = d_nm.mk_node(
      Kind::FORALL,
      {y2,
       d_nm.mk_node(Kind::ITE, {d_nm.mk_node(Kind::BV_ULE, {y2, e}), Q, B2})});

  d_as.push_back(X);
  d_as.push_back(C);
  d_as.push_back(C2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // C and C2 are NOT alpha-equivalent and must not be merged.
  ASSERT_NE(assertions[1], assertions[2]);
}

TEST_F(TestPassQuant, alpha_nested2)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node v = d_nm.mk_var(d_bv2, "v");
  Node u = d_nm.mk_var(d_bv2, "u");

  Node qv = d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, c})});
  Node qu = d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::BV_ULE, {u, c})});

  d_as.push_back(d_nm.mk_node(Kind::NOT, {qv}));
  d_as.push_back(
      d_nm.mk_node(Kind::AND, {qu, d_nm.mk_node(Kind::BV_ULE, {c, d})}));
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_env.statistics().new_or_get_stat<uint64_t>(
                "preprocess::quant::num_alpha_elim"),
            1);
  // Both assertions must now refer to the same quantifier.
  ASSERT_EQ(collect_binders({assertions[0], assertions[1]}).size(), 1u);
}

TEST_F(TestPassQuant, alpha_stats)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node v = d_nm.mk_var(d_bv2, "v");
  Node u = d_nm.mk_var(d_bv2, "u");

  d_as.push_back(
      d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, c})}));
  d_as.push_back(
      d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::BV_ULE, {u, c})}));
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(assertions[0], assertions[1]);
  ASSERT_EQ(d_env.statistics().new_or_get_stat<uint64_t>(
                "preprocess::quant::num_alpha_elim"),
            1);
}
}  // namespace bzla::test
