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
#include "solver/bv/bv_inverter.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;
using namespace bv;

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
               size_t idx);

  void test_ic(Kind predicate, Kind kind, uint64_t bw, size_t idx);

  void test_ic_concat(Kind predicate, uint64_t bw0, uint64_t bw1, size_t idx);

  void test_ic_sext(Kind predicate, uint64_t bw_x, uint64_t bw_t, size_t idx);

  void test_ic_ineq(Kind predicate, uint64_t bw, size_t idx);

  void test_ic_bool(Kind predicate, Kind kind, size_t idx);

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
};

void
TestBvInverter::test_ic(Kind predicate,
                        Kind kind,
                        uint64_t bw0,
                        uint64_t bw1,
                        uint64_t bw_t,
                        size_t idx)
{
  Type bv0 = d_nm.mk_bv_type(bw0);
  Type bv1 = d_nm.mk_bv_type(bw1);
  Type bv  = d_nm.mk_bv_type(bw_t);
  Node x   = d_nm.mk_var(idx == 0 ? bv0 : bv1, "x");
  Node s   = d_nm.mk_const(idx == 0 ? bv1 : bv0, "s");
  Node t   = d_nm.mk_const(bv, "t");

  Node ic = d_inverter.ic(
      predicate, kind, {idx == 0 ? x : s, idx == 0 ? s : x, t}, idx);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node ass = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EQUAL,
          {ic,
           d_nm.mk_node(Kind::EXISTS,
                        {x,
                         d_nm.mk_node(predicate,
                                      {idx == 0 ? d_nm.mk_node(kind, {x, s})
                                                : d_nm.mk_node(kind, {s, x}),
                                       t})})})});
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
TestBvInverter::test_ic(Kind predicate, Kind kind, uint64_t bw, size_t idx)
{
  test_ic(predicate, kind, bw, bw, bw, idx);
}

void
TestBvInverter::test_ic_concat(Kind predicate,
                               uint64_t bw0,
                               uint64_t bw1,
                               size_t idx)
{
  test_ic(predicate, Kind::BV_CONCAT, bw0, bw1, bw0 + bw1, idx);
}

void
TestBvInverter::test_ic_sext(Kind predicate,
                             uint64_t bw0,
                             uint64_t bw1,
                             size_t idx)
{
  Type bv0 = d_nm.mk_bv_type(bw0);
  Type bv1 = d_nm.mk_bv_type(bw1);
  assert(idx == 0 || bw0 >= bw1);
  assert(idx == 1 || bw1 >= bw0);
  Node x     = d_nm.mk_var(idx == 0 ? bv0 : bv1, "x");
  Node t     = d_nm.mk_const(idx == 0 ? bv1 : bv0, "t");
  uint64_t n = t.type().bv_size() - x.type().bv_size();

  Node ic = d_inverter.ic(predicate,
                          Kind::BV_SIGN_EXTEND,
                          {idx == 0 ? x : t, idx == 0 ? t : x},
                          idx);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node ass = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EQUAL,
          {ic,
           d_nm.mk_node(
               Kind::EXISTS,
               {x,
                d_nm.mk_node(
                    predicate,
                    {
                        idx == 0 ? d_nm.mk_node(Kind::BV_SIGN_EXTEND, {x}, {n})
                                 : t,
                        idx == 0 ? t
                                 : d_nm.mk_node(Kind::BV_SIGN_EXTEND, {x}, {n}),
                    })})})});
  ctx.assert_formula(ass);
  Result res = ctx.solve();
  if (res != Result::UNSAT)
  {
    std::cout << "predicate: " << predicate << std::endl;
    std::cout << "kind: " << Kind::BV_SIGN_EXTEND << std::endl;
    std::cout << "idx: " << idx << std::endl;
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

  Node ic = d_inverter.ic(
      predicate, x.kind(), {idx == 0 ? x : t, idx == 0 ? t : x}, idx);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node ass = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EQUAL,
          {ic,
           d_nm.mk_node(Kind::EXISTS,
                        {
                            x,
                            d_nm.mk_node(predicate,
                                         {idx == 0 ? x : t, idx == 0 ? t : x}),
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
TestBvInverter::test_ic_bool(Kind predicate, Kind kind, size_t idx)
{
  Node x = d_nm.mk_var(d_nm.mk_bool_type(), "x");
  Node s = d_nm.mk_const(d_nm.mk_bool_type(), "s");
  Node t = d_nm.mk_const(d_nm.mk_bool_type(), "t");

  Node ic = d_inverter.ic(
      predicate, kind, {idx == 0 ? x : s, idx == 0 ? s : x, t}, idx);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node ass = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EQUAL,
          {ic,
           d_nm.mk_node(Kind::EXISTS,
                        {x,
                         d_nm.mk_node(predicate,
                                      {idx == 0 ? d_nm.mk_node(kind, {x, s})
                                                : d_nm.mk_node(kind, {s, x}),
                                       t})})})});
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

/* -------------------------------------------------------------------------- */

TEST_F(TestBvInverter, and)
{
  test_ic_bool(Kind::EQUAL, Kind::AND, 0);
  test_ic_bool(Kind::EQUAL, Kind::AND, 1);
  test_ic_bool(Kind::DISTINCT, Kind::AND, 0);
  test_ic_bool(Kind::DISTINCT, Kind::AND, 1);
}

TEST_F(TestBvInverter, or)
{
  test_ic_bool(Kind::EQUAL, Kind::OR, 0);
  test_ic_bool(Kind::EQUAL, Kind::OR, 1);
  test_ic_bool(Kind::DISTINCT, Kind::OR, 0);
  test_ic_bool(Kind::DISTINCT, Kind::OR, 1);
}

TEST_F(TestBvInverter, bv_and)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_AND, 1, 0);
    test_ic(predicate, Kind::BV_AND, 1, 1);
    test_ic(predicate, Kind::BV_AND, 4, 0);
    test_ic(predicate, Kind::BV_AND, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_or)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_OR, 1, 0);
    test_ic(predicate, Kind::BV_OR, 1, 1);
    test_ic(predicate, Kind::BV_OR, 4, 0);
    test_ic(predicate, Kind::BV_OR, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_ashr)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_ASHR, 1, 0);
    test_ic(predicate, Kind::BV_ASHR, 1, 1);
    test_ic(predicate, Kind::BV_ASHR, 4, 0);
    test_ic(predicate, Kind::BV_ASHR, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_mul)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_MUL, 1, 0);
    test_ic(predicate, Kind::BV_MUL, 1, 1);
    test_ic(predicate, Kind::BV_MUL, 4, 0);
    test_ic(predicate, Kind::BV_MUL, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_shl)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_SHL, 1, 0);
    test_ic(predicate, Kind::BV_SHL, 1, 1);
    test_ic(predicate, Kind::BV_SHL, 4, 0);
    test_ic(predicate, Kind::BV_SHL, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_shr)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_SHR, 1, 0);
    test_ic(predicate, Kind::BV_SHR, 1, 1);
    test_ic(predicate, Kind::BV_SHR, 4, 0);
    test_ic(predicate, Kind::BV_SHR, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_udiv)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_UDIV, 1, 0);
    test_ic(predicate, Kind::BV_UDIV, 1, 1);
    test_ic(predicate, Kind::BV_UDIV, 4, 0);
    test_ic(predicate, Kind::BV_UDIV, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_urem)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_UREM, 1, 0);
    test_ic(predicate, Kind::BV_UREM, 1, 1);
    test_ic(predicate, Kind::BV_UREM, 4, 0);
    test_ic(predicate, Kind::BV_UREM, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_concat)
{
  for (Kind predicate : d_predicates)
  {
    test_ic_concat(predicate, 1, 1, 0);
    test_ic_concat(predicate, 1, 1, 1);
    test_ic_concat(predicate, 2, 1, 0);
    test_ic_concat(predicate, 2, 1, 1);
    test_ic_concat(predicate, 2, 4, 0);
    test_ic_concat(predicate, 2, 4, 1);
  }
}

TEST_F(TestBvInverter, bv_sext)
{
  for (Kind predicate : d_predicates)
  {
    test_ic_sext(predicate, 1, 1, 0);
    test_ic_sext(predicate, 1, 1, 1);
    test_ic_sext(predicate, 2, 3, 0);
    test_ic_sext(predicate, 3, 1, 1);
    test_ic_sext(predicate, 2, 4, 0);
    test_ic_sext(predicate, 5, 2, 1);
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

}  // namespace bzla::test
