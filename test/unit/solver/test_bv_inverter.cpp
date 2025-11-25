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
  void SetUp() override
  {
    d_bv4 = d_nm.mk_bv_type(4);
    d_x   = d_nm.mk_var(d_bv4, "x");
    d_s   = d_nm.mk_const(d_bv4, "s");
    d_t   = d_nm.mk_const(d_bv4, "t");
  }

  void test_ic(Kind predicate, Kind kind, size_t idx);

  NodeManager d_nm;
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  BvInverter d_inverter;

  Type d_bv4;
  Node d_x;
  Node d_s;
  Node d_t;

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
TestBvInverter::test_ic(Kind predicate, Kind kind, size_t idx)
{
  Node ic = d_inverter.ic(
      predicate, kind, {idx == 0 ? d_x : d_s, idx == 0 ? d_s : d_x, d_t}, idx);
  ASSERT_FALSE(ic.is_null());

  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Node ass = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EQUAL,
          {ic,
           d_nm.mk_node(
               Kind::EXISTS,
               {d_x,
                d_nm.mk_node(predicate,
                             {idx == 0 ? d_nm.mk_node(kind, {d_x, d_s})
                                       : d_nm.mk_node(kind, {d_s, d_x}),
                              d_t})})})});
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

TEST_F(TestBvInverter, bv_and)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_AND, 0);
    test_ic(predicate, Kind::BV_AND, 1);
  }
}

TEST_F(TestBvInverter, bv_ashr)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_ASHR, 0);
    test_ic(predicate, Kind::BV_ASHR, 1);
  }
}

TEST_F(TestBvInverter, bv_mul)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_MUL, 0);
    test_ic(predicate, Kind::BV_MUL, 1);
  }
}

TEST_F(TestBvInverter, bv_shl)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_SHL, 0);
    test_ic(predicate, Kind::BV_SHL, 1);
  }
}

TEST_F(TestBvInverter, bv_shr)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_SHR, 0);
    test_ic(predicate, Kind::BV_SHR, 1);
  }
}

TEST_F(TestBvInverter, bv_udiv)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_UDIV, 0);
    test_ic(predicate, Kind::BV_UDIV, 1);
  }
}

TEST_F(TestBvInverter, bv_urem)
{
  for (Kind predicate : d_predicates)
  {
    test_ic(predicate, Kind::BV_UREM, 0);
    test_ic(predicate, Kind::BV_UREM, 1);
  }
}

// TODO concat
// TODO sext

}  // namespace bzla::test
