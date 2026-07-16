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

  void test_ic_cmp(Kind kind, uint64_t bw, size_t idx, size_t idx_x);

  void test_ic_cmp(Kind predicate, uint64_t bw, size_t idx);

  void check_conds(const Node& node,
                   const Node& x,
                   const Node& invert,
                   const std::vector<Node>& conds);
  void check_inverse(const Node& node,
                     const Node& x,
                     const Node& invert,
                     const std::vector<Node>& conds,
                     bool check_valid);

  void test_invert(const Node& node,
                   const Node& x,
                   bool expect_conds,
                   bool expect_inv  = true,
                   bool check_valid = true,
                   bool under_det   = false);

  NodeManager d_nm;
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  BvInverter d_inverter;
  BvInverter d_inverter_underdet{d_env, true};

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
TestBvInverter::test_ic_cmp(Kind predicate, uint64_t bw, size_t idx)
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

void
TestBvInverter::test_ic_cmp(Kind kind, uint64_t bw, size_t idx, size_t idx_x)
{
  // Bit-vector comparison nodes on the path are only handled under an EQUAL
  // predicate (with a Boolean right-hand side), as reached when chaining
  // inverses in invert().
  Type bv = d_nm.mk_bv_type(bw);
  test_ic(Kind::EQUAL, kind, bv, bv, d_nm.mk_bool_type(), idx, idx_x);
}

/* -------------------------------------------------------------------------- */

void
TestBvInverter::test_invert(const Node& node,
                            const Node& x,
                            bool expect_conds,
                            bool expect_inv,
                            bool check_valid,
                            bool underdet)
{
  BvInverter& inverter = underdet ? d_inverter_underdet : d_inverter;
  auto [invert, conds] = inverter.invert(node, x);
  if (expect_inv != !invert.is_null() || !conds.empty() != expect_conds)
  {
    std::cout << "node: " << node << std::endl;
    if (!invert.is_null())
    {
      std::cout << "invert: " << invert << std::endl;
    }
  }
  ASSERT_EQ(expect_inv, !invert.is_null());
  ASSERT_TRUE(!conds.empty() == expect_conds);
  if (expect_inv)
  {
    check_conds(node, x, invert, conds);
    check_inverse(node, x, invert, conds, check_valid);
  }
}

namespace {
/** Collect all constant leafs of `node` into `consts`. */
void
collect_consts(const Node& node, std::unordered_set<Node>& consts)
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    Node cur = visit.back();
    visit.pop_back();
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      if (cur.is_const())
      {
        consts.insert(cur);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}
}  // namespace

void
TestBvInverter::check_conds(const Node& node,
                            const Node& x,
                            const Node& invert,
                            const std::vector<Node>& conds)
{
  if (conds.empty())
  {
    return;
  }
  // The conditions constrain the fresh choice constants introduced by
  // invert() relative to the constants of the original node. Since the
  // conditions are asserted unconditionally in instantiation lemmas, they
  // must be satisfiable in the choice constants for all values of the
  // original constants:
  //   \forall s, t. \exists y . C
  // where y are the fresh constants introduced by invert() and C is the
  // conjunction of the conditions. We check the negation: assert
  //   (forall y . (not C))
  // with the original constants free, which must be unsatisfiable.
  std::unordered_set<Node> node_consts;
  collect_consts(node, node_consts);
  std::unordered_set<Node> cond_consts;
  for (const auto& c : conds)
  {
    collect_consts(c, cond_consts);
  }
  std::unordered_map<Node, Node> substs;
  std::vector<Node> vars;
  for (const auto& c : cond_consts)
  {
    if (node_consts.find(c) == node_consts.end())
    {
      Node var = d_nm.mk_var(c.type());
      substs.emplace(c, var);
      vars.push_back(var);
    }
  }
  std::unordered_map<Node, Node> subst_cache;
  Node body = d_nm.mk_node(
      Kind::NOT, {utils::substitute(d_nm,
                                    utils::mk_nary(d_nm, Kind::AND, conds),
                                    substs,
                                    subst_cache)});
  for (auto it = vars.rbegin(); it != vars.rend(); ++it)
  {
    body = d_nm.mk_node(Kind::FORALL, {*it, body});
  }
  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  ctx.assert_formula(body);
  Result res = ctx.solve();
  if (res != Result::UNSAT)
  {
    std::cout << "node: " << node << std::endl;
    std::cout << "x: " << x << std::endl;
    std::cout << "invert: " << invert << std::endl;
    std::cout << "conditions:" << std::endl;
    for (const auto& c : conds)
    {
      std::cout << "- " << c << std::endl;
    }
  }
  ASSERT_EQ(res, Result::UNSAT);
}

void
TestBvInverter::check_inverse(const Node& node,
                              const Node& x,
                              const Node& invert,
                              const std::vector<Node>& conds,
                              bool check_valid)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  std::unordered_map<Node, Node> subst_cache;
  Node ass = utils::substitute(d_nm, node, {{x, invert}}, subst_cache);
  if (conds.empty())
  {
    // Unconditional inverses must be valid, i.e., substituting the inverse
    // for x must satisfy the node for all values of the remaining constants.
    // Exception: under-determined inverses (e.g., for concat) disregard that
    // invertibility is conditional and are only expected to satisfy the node
    // for some values (any instantiation is sound, check_valid = false).
    if (check_valid)
    {
      ctx.assert_formula(d_nm.mk_node(Kind::NOT, {ass}));
      Result res = ctx.solve();
      if (res != Result::UNSAT)
      {
        std::cout << "node: " << node << std::endl;
        std::cout << "invert: " << invert << std::endl;
      }
      ASSERT_EQ(res, Result::UNSAT);
    }
    else
    {
      ctx.assert_formula(ass);
      Result res = ctx.solve();
      if (res != Result::SAT)
      {
        std::cout << "node: " << node << std::endl;
        std::cout << "invert: " << invert << std::endl;
      }
      ASSERT_EQ(res, Result::SAT);
    }
  }
  // For conditional inverses, the (conceptual) choice term's value is
  // undetermined when the invertibility condition is false (the conditions
  // are encoded over implications IC => predicate), hence no validity check
  // is performed here. The satisfiability of the conditions themselves is
  // checked in check_conds_satisfiable().
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

TEST_F(TestBvInverter, bv_ult)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      test_ic_cmp(Kind::BV_ULT, 1, idx, idx_x);
      test_ic_cmp(Kind::BV_ULT, 4, idx, idx_x);
    }
  }
}

TEST_F(TestBvInverter, bv_ugt)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      test_ic_cmp(Kind::BV_UGT, 1, idx, idx_x);
      test_ic_cmp(Kind::BV_UGT, 4, idx, idx_x);
    }
  }
}

TEST_F(TestBvInverter, bv_slt)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      test_ic_cmp(Kind::BV_SLT, 1, idx, idx_x);
      test_ic_cmp(Kind::BV_SLT, 4, idx, idx_x);
    }
  }
}

TEST_F(TestBvInverter, bv_sgt)
{
  for (size_t idx : std::vector<size_t>{0, 1})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      test_ic_cmp(Kind::BV_SGT, 1, idx, idx_x);
      test_ic_cmp(Kind::BV_SGT, 4, idx, idx_x);
    }
  }
}

TEST_F(TestBvInverter, ineq)
{
  for (Kind predicate : d_predicates)
  {
    test_ic_cmp(predicate, 1, 0);
    test_ic_cmp(predicate, 1, 1);
    test_ic_cmp(predicate, 4, 0);
    test_ic_cmp(predicate, 4, 1);
  }
}

TEST_F(TestBvInverter, invert0_0)
{
  Type b = d_nm.mk_bv_type(4);
  Node x = d_nm.mk_const(b, "x");
  Node t = d_nm.mk_const(b, "t");
  Node node = d_nm.mk_node(Kind::EQUAL, {x, t});
  test_invert(node, x, false);
}

TEST_F(TestBvInverter, invert0_1)
{
  Type b    = d_nm.mk_bv_type(4);
  Node x    = d_nm.mk_const(b, "x");
  Node t    = d_nm.mk_const(b, "t");
  Node node = d_nm.mk_node(Kind::BV_UGT, {x, t});
  test_invert(node, x, true);
}

TEST_F(TestBvInverter, invert1_0)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1   = d_nm.mk_const(b, "s1");
  Node add  = d_nm.mk_node(Kind::BV_ADD, {s1, x});
  Node node = d_nm.mk_node(Kind::EQUAL, {add, t});
  test_invert(node, x, false);
}

TEST_F(TestBvInverter, invert1_1)
{
  Type b    = d_nm.mk_bv_type(4);
  Node x    = d_nm.mk_const(b, "x");
  Node t    = d_nm.mk_const(b, "t");
  Node s1   = d_nm.mk_const(b, "s1");
  Node add  = d_nm.mk_node(Kind::BV_ADD, {s1, x});
  Node node = d_nm.mk_node(Kind::BV_UGT, {add, t});
  test_invert(node, x, true);
}

TEST_F(TestBvInverter, invert2)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s1, x});
  Node node = d_nm.mk_node(Kind::EQUAL, {add, t});

  test_invert(node, x, false);
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

  test_invert(node, x, false);
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

  test_invert(node, x, true);
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

  test_invert(node, x, true);
}

TEST_F(TestBvInverter, invert6)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");
  Node s3 = d_nm.mk_const(b, "s3");

  Node add1 = d_nm.mk_node(Kind::BV_ADD, {s2, x});
  Node add2 = d_nm.mk_node(Kind::BV_ADD, {add1, s1});
  Node shl  = d_nm.mk_node(Kind::BV_MUL, {add2, s1});
  Node node = d_nm.mk_node(Kind::EQUAL, {shl, t});

  test_invert(node, x, true);
}

TEST_F(TestBvInverter, invert7)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");
  Node s3 = d_nm.mk_const(b, "s3");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s2, x});
  Node mul  = d_nm.mk_node(Kind::BV_MUL, {add, s1});
  Node shl  = d_nm.mk_node(Kind::BV_MUL, {mul, s1});
  Node node = d_nm.mk_node(Kind::EQUAL, {shl, t});

  test_invert(node, x, true);
}

TEST_F(TestBvInverter, invert8)
{
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");
  Node s3 = d_nm.mk_const(b, "s3");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {s2, x});
  Node mul  = d_nm.mk_node(Kind::BV_MUL, {add, x});
  Node shl  = d_nm.mk_node(Kind::BV_MUL, {mul, s1});
  Node node = d_nm.mk_node(Kind::EQUAL, {shl, t});

  test_invert(node, x, false, false);
}

TEST_F(TestBvInverter, invert9)
{
  // (and
  //   (= #b00000000000000000000000000000000
  //     (concat #b000000000000000000000000000000 m))
  //   (and x (not (bvslt #b00000000000000000000000000000000 t))))
  Node zero = d_nm.mk_value(BitVector::mk_zero(4));
  Type b    = d_nm.mk_bv_type(4);
  Node m    = d_nm.mk_const(b, "m");
  Node x    = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node t    = d_nm.mk_const(b, "t");

  Node slt    = d_nm.mk_node(Kind::BV_SLT, {zero, t});
  Node ad     = d_nm.mk_node(Kind::AND, {x, d_nm.mk_node(Kind::NOT, {slt})});
  Node concat = d_nm.mk_node(Kind::BV_CONCAT, {zero, m});
  Node eq =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_value(BitVector::mk_zero(8)), concat});
  Node node = d_nm.mk_node(Kind::AND, {eq, ad});

  test_invert(node, x, true);
  test_invert(node, t, true);
}

TEST_F(TestBvInverter, invert10)
{
  // (and
  //   (= #b00000000000000000000000000000000
  //     (concat #b000000000000000000000000000000 m))
  //   (not (and x (not (bvslt #b00000000000000000000000000000000 t))))
  Node zero = d_nm.mk_value(BitVector::mk_zero(4));
  Type b    = d_nm.mk_bv_type(4);
  Node m    = d_nm.mk_const(b, "m");
  Node x    = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node t    = d_nm.mk_const(b, "t");

  Node slt = d_nm.mk_node(Kind::BV_SLT, {zero, t});
  Node ad  = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(Kind::AND, {x, d_nm.mk_node(Kind::NOT, {slt})})});
  Node concat = d_nm.mk_node(Kind::BV_CONCAT, {zero, m});
  Node eq =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_value(BitVector::mk_zero(8)), concat});
  Node node = d_nm.mk_node(Kind::AND, {eq, ad});

  test_invert(node, x, true);
  test_invert(node, t, true);
}

TEST_F(TestBvInverter, invert_ineq_under_eq)
{
  // Bit-vector comparison nodes on the path, reachable via chaining
  // inverses under a Boolean equality: (= (<cmp> <x> <s>) <p>).
  Type b = d_nm.mk_bv_type(4);
  Node x = d_nm.mk_const(b, "x");
  Node s = d_nm.mk_const(b, "s");
  Node p = d_nm.mk_const(d_nm.mk_bool_type(), "p");
  for (Kind cmp : std::vector<Kind>{Kind::BV_ULT, Kind::BV_SLT})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      Node c    = d_nm.mk_node(cmp, {idx_x == 0 ? x : s, idx_x == 0 ? s : x});
      Node node = d_nm.mk_node(Kind::EQUAL, {c, p});
      test_invert(node, x, true);
      test_invert(d_nm.mk_node(Kind::NOT, {node}), x, true);
      // Nested below the comparison: (= (<cmp> .. (bvadd x s) ..) <p>)
      Node add  = d_nm.mk_node(Kind::BV_ADD, {x, s});
      Node ca   = d_nm.mk_node(cmp, {idx_x == 0 ? add : s,
                                     idx_x == 0 ? s : add});
      test_invert(d_nm.mk_node(Kind::EQUAL, {ca, p}), x, true);
    }
  }
}

TEST_F(TestBvInverter, invert_witness_ops)
{
  // Operators without exact inverses require conditional inverses via
  // fresh choice constants: (= (<op> <x> <s>) t) and negated/inequality
  // variants.
  Type b = d_nm.mk_bv_type(4);
  Node x = d_nm.mk_const(b, "x");
  Node s = d_nm.mk_const(b, "s");
  Node t = d_nm.mk_const(b, "t");
  for (Kind op : std::vector<Kind>{Kind::BV_AND,
                                   Kind::BV_OR,
                                   Kind::BV_MUL,
                                   Kind::BV_SHL,
                                   Kind::BV_SHR,
                                   Kind::BV_ASHR,
                                   Kind::BV_UDIV,
                                   Kind::BV_UREM})
  {
    for (size_t idx_x : std::vector<size_t>{0, 1})
    {
      Node o = d_nm.mk_node(op, {idx_x == 0 ? x : s, idx_x == 0 ? s : x});
      test_invert(d_nm.mk_node(Kind::EQUAL, {o, t}), x, true);
      test_invert(
          d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {o, t})}),
          x,
          true);
      test_invert(d_nm.mk_node(Kind::BV_ULT, {o, t}), x, true);
      test_invert(
          d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::BV_SLT, {t, o})}),
          x,
          true);
    }
  }
}

TEST_F(TestBvInverter, invert_concat)
{
  // Default (not under-determined) inverter: concat requires a conditional
  // inverse.
  Type b2 = d_nm.mk_bv_type(2);
  Node x  = d_nm.mk_const(b2, "x");
  Node s  = d_nm.mk_const(b2, "s");
  Node t  = d_nm.mk_const(d_nm.mk_bv_type(4), "t");
  for (size_t idx_x : std::vector<size_t>{0, 1})
  {
    Node c = d_nm.mk_node(Kind::BV_CONCAT,
                          {idx_x == 0 ? x : s, idx_x == 0 ? s : x});
    test_invert(d_nm.mk_node(Kind::EQUAL, {c, t}), x, true);
  }
}

TEST_F(TestBvInverter, invert_bool_structure)
{
  // Bit-vector literal below Boolean structure.
  Type b = d_nm.mk_bv_type(4);
  Node x = d_nm.mk_const(b, "x");
  Node s = d_nm.mk_const(b, "s");
  Node t = d_nm.mk_const(b, "t");
  Node g = d_nm.mk_const(d_nm.mk_bool_type(), "g");

  Node eq = d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {x, s}), t});
  Node a  = d_nm.mk_node(Kind::AND, {eq, g});
  test_invert(a, x, true);
  test_invert(d_nm.mk_node(Kind::NOT, {a}), x, true);
  test_invert(d_nm.mk_node(Kind::AND, {g, d_nm.mk_node(Kind::NOT, {eq})}),
              x,
              true);
}

TEST_F(TestBvInverter, invert_chain_mixed)
{
  // (not (bvult (bvlshr (bvadd x s1) s2) t))
  Type b  = d_nm.mk_bv_type(4);
  Node x  = d_nm.mk_const(b, "x");
  Node t  = d_nm.mk_const(b, "t");
  Node s1 = d_nm.mk_const(b, "s1");
  Node s2 = d_nm.mk_const(b, "s2");

  Node add  = d_nm.mk_node(Kind::BV_ADD, {x, s1});
  Node shr  = d_nm.mk_node(Kind::BV_SHR, {add, s2});
  Node node = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::BV_ULT, {shr, t})});
  test_invert(node, x, true);
}

TEST_F(TestBvInverter, invert_none)
{
  Type b = d_nm.mk_bv_type(4);
  Node x = d_nm.mk_const(b, "x");
  Node s = d_nm.mk_const(b, "s");
  Node t = d_nm.mk_const(b, "t");
  Node c = d_nm.mk_const(d_nm.mk_bool_type(), "c");

  // x does not occur in node
  test_invert(d_nm.mk_node(Kind::EQUAL, {s, t}), x, false, false);
  // non-invertible node (ite) on path
  test_invert(
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::ITE, {c, x, s}), t}),
      x,
      false,
      false);
  // extract on path is only invertible in under-determined mode
  test_invert(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {2, 1}),
                    d_nm.mk_const(d_nm.mk_bv_type(2), "t2")}),
      x,
      false,
      false);
}

TEST_F(TestBvInverter, invert_underdet_extract)
{
  // Under-determined inverses for extract reconstruct sliced-out bits with
  // fresh constants. The resulting inverse is unconditional and valid (the
  // extracted bits do not depend on the fresh constants).
  Type b  = d_nm.mk_bv_type(4);
  Type b2 = d_nm.mk_bv_type(2);
  Node x  = d_nm.mk_const(b, "x");
  Node s  = d_nm.mk_const(b2, "s");
  Node t  = d_nm.mk_const(b2, "t");

  Node xt = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {2, 1});
  test_invert(d_nm.mk_node(Kind::EQUAL, {xt, t}), x, false, true, true, true);
  // extract below an exact inverse
  Node add = d_nm.mk_node(Kind::BV_ADD, {xt, s});
  test_invert(d_nm.mk_node(Kind::EQUAL, {add, t}), x, false, true, true, true);
  // extract below a conditional inverse
  Node mul = d_nm.mk_node(Kind::BV_MUL, {xt, s});
  test_invert(d_nm.mk_node(Kind::EQUAL, {mul, t}), x, true, true, true, true);
}

TEST_F(TestBvInverter, invert_underdet_concat)
{
  // Under-determined inverses for concat disregard that invertibility is
  // conditional on the sibling. The inverse is unconditional but only
  // satisfies the node for some values of the remaining constants
  // (check_valid = false).
  Type b2 = d_nm.mk_bv_type(2);
  Node x  = d_nm.mk_const(b2, "x");
  Node s  = d_nm.mk_const(b2, "s");
  Node t  = d_nm.mk_const(d_nm.mk_bv_type(4), "t");
  for (size_t idx_x : std::vector<size_t>{0, 1})
  {
    Node c = d_nm.mk_node(Kind::BV_CONCAT,
                          {idx_x == 0 ? x : s, idx_x == 0 ? s : x});
    test_invert(d_nm.mk_node(Kind::EQUAL, {c, t}), x, false, true, false, true);
  }
}

}  // namespace bzla::test
