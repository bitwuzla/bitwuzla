/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_manager.h"
#include "node/node_utils.h"
#include "solver/bv/bv_inverter.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;
using namespace bv;

/* -------------------------------------------------------------------------- */

class TestBvInverter : public TestCommon
{
 protected:
  TestBvInverter()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory, d_options),
        d_inverter(d_env)
  {
  }

  void test_ic(Kind predicate,
               Kind kind,
               uint64_t bw0,
               uint64_t bw1,
               uint64_t bw_t,
               size_t idx,
               size_t idx_x);

  void test_ic_sext(Kind predicate, uint64_t bw_x, uint64_t bw_t, size_t idx);

  void test_ic_bool(Kind predicate, Kind kind, size_t idx, size_t idx_x);

  void test_ic_ineq(Kind predicate, uint64_t bw, size_t idx);

  void test_invert(const Node& node, const Node& x);

  NodeManager d_nm;
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  BvInverter d_inverter;

  std::vector<Kind> d_predicates = {Kind::BV_ULT,
                                    Kind::BV_ULE,
                                    Kind::BV_UGT,
                                    Kind::BV_UGE,
                                    Kind::BV_SLT,
                                    Kind::BV_SLE,
                                    Kind::BV_SGT,
                                    Kind::BV_SGE,
                                    Kind::DISTINCT,
                                    Kind::EQUAL};

 private:
  void test_ic(Kind predicate,
               Kind kind,
               Type type0,
               Type type1,
               Type typet,
               size_t idx,
               size_t idx_x);
  void test_ic(
      Kind predicate, Kind kind, uint64_t bw, size_t idx, size_t idx_x);
};

/* -------------------------------------------------------------------------- */

void
TestBvInverter::test_ic(Kind predicate,
                        Kind kind,
                        Type type0,
                        Type type1,
                        Type typet,
                        size_t idx,
                        size_t idx_x)
{
  Node x    = d_nm.mk_var(idx == 0 ? type0 : type1, "x");
  Node s    = d_nm.mk_const(idx == 0 ? type1 : type0, "s");
  Node t    = d_nm.mk_const(typet, "t");
  Node node = d_nm.mk_node(kind, {idx_x == 0 ? x : s, idx_x == 0 ? s : x});

  Node ic = d_inverter.ic(predicate, node, t, idx, idx_x);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node pred =
      d_nm.mk_node(predicate, {idx == 0 ? node : t, idx == 0 ? t : node});
  Node exists = d_nm.mk_node(Kind::EXISTS, {x, pred});
  Node ass    = d_nm.mk_node(Kind::DISTINCT, {ic, exists});
  ctx.assert_formula(ass);
  Result res = ctx.solve();
  if (res != Result::UNSAT)
  {
    std::cout << "predicate: " << predicate << std::endl;
    std::cout << "kind: " << kind << std::endl;
    std::cout << "idx: " << idx << std::endl;
    std::cout << "ic: " << ic << std::endl;
    std::cout << "vc: " << ass << std::endl;
  }
  ASSERT_EQ(res, Result::UNSAT);
}

void
TestBvInverter::test_ic(Kind predicate,
                        Kind kind,
                        uint64_t bw0,
                        uint64_t bw1,
                        uint64_t bw_t,
                        size_t idx,
                        size_t idx_x)
{
  test_ic(predicate,
          kind,
          d_nm.mk_bv_type(bw0),
          d_nm.mk_bv_type(bw1),
          d_nm.mk_bv_type(bw_t),
          idx,
          idx_x);
}

void
TestBvInverter::test_ic(
    Kind predicate, Kind kind, uint64_t bw, size_t idx, size_t idx_x)
{
  test_ic(predicate, kind, bw, bw, bw, idx, idx_x);
}

void
TestBvInverter::test_ic_sext(Kind predicate,
                             uint64_t bwx,
                             uint64_t bwt,
                             size_t idx)
{
  Type bvx   = d_nm.mk_bv_type(bwx);
  Type bvt   = d_nm.mk_bv_type(bwt);
  Node x     = d_nm.mk_var(bvx, "x");
  Node t     = d_nm.mk_const(bvt, "t");
  uint64_t n = t.type().bv_size() - x.type().bv_size();
  Node node  = d_nm.mk_node(Kind::BV_SIGN_EXTEND, {x}, {n});

  Node ic = d_inverter.ic(predicate, node, t, idx, 0);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node pred =
      d_nm.mk_node(predicate, {idx == 0 ? node : t, idx == 0 ? t : node});
  Node exists = d_nm.mk_node(Kind::EXISTS, {x, pred});
  Node ass    = d_nm.mk_node(Kind::DISTINCT, {ic, exists});

  ctx.assert_formula(ass);
  Result res = ctx.solve();
  if (res != Result::UNSAT)
  {
    std::cout << "predicate: " << predicate << std::endl;
    std::cout << "kind: " << Kind::BV_SIGN_EXTEND << std::endl;
    std::cout << "ic: " << ic << std::endl;
    std::cout << "vc: " << ass << std::endl;
  }
  ASSERT_EQ(res, Result::UNSAT);
}

void
TestBvInverter::test_ic_ineq(Kind predicate, uint64_t bw, size_t idx)
{
  Type bv = d_nm.mk_bv_type(bw);
  Node x  = d_nm.mk_var(bv, "x");
  Node t  = d_nm.mk_const(bv, "t");
  Node node = d_nm.mk_node(predicate, {idx == 0 ? x : t, idx == 0 ? t : x});

  Node ic = d_inverter.ic(node, t, idx);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node ass = d_nm.mk_node(Kind::NOT,
                          {d_nm.mk_node(Kind::EQUAL,
                                        {ic,
                                         d_nm.mk_node(Kind::EXISTS,
                                                      {
                                                          x,
                                                          node,
                                                      })})});
  ctx.assert_formula(ass);
  Result res = ctx.solve();
  if (res != Result::UNSAT)
  {
    std::cout << "predicate: " << predicate << std::endl;
    std::cout << "idx: " << idx << std::endl;
    std::cout << "ic: " << ic << std::endl;
    std::cout << "vc: " << ass << std::endl;
  }
  ASSERT_EQ(res, Result::UNSAT);
}

void
TestBvInverter::test_ic_bool(Kind predicate,
                             Kind kind,
                             size_t idx,
                             size_t idx_x)
{
  test_ic(predicate,
          kind,
          d_nm.mk_bool_type(),
          d_nm.mk_bool_type(),
          d_nm.mk_bool_type(),
          idx,
          idx_x);
}

/* -------------------------------------------------------------------------- */

void
TestBvInverter::test_invert(const Node& node, const Node& x)
{
  auto [invert, conds] = d_inverter.invert(node, x);
  std::cout << "node: " << node << std::endl;
  std::cout << "invert: " << invert << std::endl;
  std::cout << "conditions:" << std::endl;
  for (const auto& c : conds)
  {
    std::cout << "- " << c.first << " => " << c.second << std::endl;
  }
  // SolvingContext ctx(d_nm, d_options);
  // TODO add assertions to check
  // Result res = ctx.solve();
  //
  // if (res != Result::UNSAT)
  // {
  //   std::cout << "node: " << node << std::endl;
  //   std::cout << "invert: " << invert << std::endl;
  //   std::cout << "conditions:" << std::endl;
  //   for (const auto& c : conds)
  //   {
  //     std::cout << "  " << c.first << " => " << c.second << std::endl;
  //   }
  //   std::cout << "assertions:" << std::endl;
  //   auto assertions = ctx.assertions();
  //   std::vector<Node> visit;
  //   for (size_t i = 0, n = assertions.size(); i < n; ++i)
  //   {
  //     std::cout << "  " << assertions[i] << std::endl;
  //     visit.push_back(assertions[i]);
  //   }
  //   std::cout << "model:" << std::endl;
  //   std::unordered_set<Node> cache;
  //   do
  //   {
  //     Node cur = visit.back();
  //     visit.pop_back();
  //     auto [it, inserted] = cache.insert(cur);
  //     if (inserted)
  //     {
  //       if (cur.is_const())
  //       {
  //         std::cout << "  " << cur << ": " << ctx.get_value(cur) <<
  //         std::endl;
  //       }
  //       else
  //       {
  //         visit.insert(visit.end(), cur.begin(), cur.end());
  //       }
  //     }
  //   } while (!visit.empty());
  // }
  // ASSERT_EQ(res, Result::UNSAT);
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBvInverter, and)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      test_ic_bool(Kind::EQUAL, Kind::AND, idx, idx_x);
      test_ic_bool(Kind::DISTINCT, Kind::AND, idx, idx_x);
    }
  }
}

TEST_F(TestBvInverter, or)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      test_ic_bool(Kind::EQUAL, Kind::OR, idx, idx_x);
      test_ic_bool(Kind::DISTINCT, Kind::OR, idx, idx_x);
    }
  }
}

TEST_F(TestBvInverter, bv_and)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_AND, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_AND, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_or)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_OR, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_OR, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_ashr)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_ASHR, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_ASHR, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_mul)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_MUL, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_MUL, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_shl)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_SHL, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_SHL, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_shr)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_SHR, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_SHR, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_udiv)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_UDIV, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_UDIV, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_urem)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_UREM, 1, idx, idx_x);
        test_ic(predicate, Kind::BV_UREM, 4, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_concat)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      for (Kind predicate : d_predicates)
      {
        test_ic(predicate, Kind::BV_CONCAT, 1, 1, 2, idx, idx_x);
        test_ic(predicate, Kind::BV_CONCAT, 2, 1, 3, idx, idx_x);
        test_ic(predicate, Kind::BV_CONCAT, 2, 4, 6, idx, idx_x);
      }
    }
  }
}

TEST_F(TestBvInverter, bv_sext)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (Kind predicate : d_predicates)
    {
      test_ic_sext(predicate, 1, 1, idx);
      test_ic_sext(predicate, 2, 3, idx);
      test_ic_sext(predicate, 1, 3, idx);
      test_ic_sext(predicate, 2, 4, idx);
      test_ic_sext(predicate, 2, 5, idx);
    }
  }
}

TEST_F(TestBvInverter, ineq)
{
  for (Kind predicate : d_predicates)
  {
    test_ic_ineq(predicate, 1, 0);
    test_ic_ineq(predicate, 1, 1);
    test_ic_ineq(predicate, 4, 0);
    test_ic_ineq(predicate, 4, 1);
  }
}

TEST_F(TestBvInverter, invert0)
{
  Type b = d_nm.mk_bv_type(4);
  Node x = d_nm.mk_const(b, "x");
  Node t = d_nm.mk_const(b, "t");

  Node node = d_nm.mk_node(Kind::BV_UGT, {x, t});

  test_invert(node, x);
}

TEST_F(TestBvInverter, invert1)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s2 = d_nm.mk_const(b, "s2");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s2, x});
  Node node = d_nm.mk_node(Kind::BV_UGT, {add, t});

  test_invert(node, x);
}

TEST_F(TestBvInverter, invert2)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s1, x});
  Node node = d_nm.mk_node(Kind::EQUAL, {add, t});

  test_invert(node, x);
}

TEST_F(TestBvInverter, invert3)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");

  Node add1 = d_nm.mk_node(Kind::BV_ADD, {s1, x});
  Node add2 = d_nm.mk_node(Kind::BV_ADD, {add1, s2});
  Node node = d_nm.mk_node(Kind::EQUAL, {add2, t});

  test_invert(node, x);
}

TEST_F(TestBvInverter, invert4)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s2, x});
  Node mul  = d_nm.mk_node(Kind::BV_MUL, {add, s1});
  Node node = d_nm.mk_node(Kind::BV_UGT, {mul, t});

  test_invert(node, x);
}

TEST_F(TestBvInverter, invert5)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");
  Node s3 = d_nm.mk_const(b, "s3");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s2, x});
  Node mul  = d_nm.mk_node(Kind::BV_MUL, {add, s1});
  Node shl  = d_nm.mk_node(Kind::BV_SHL, {mul, s1});
  Node node = d_nm.mk_node(Kind::BV_UGT, {shl, t});

  test_invert(node, x);
}
}  // namespace bzla::test
