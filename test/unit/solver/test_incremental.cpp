/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_manager.h"
#include "sat/sat_solver_factory.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;

class TestIncremental : public TestCommon
{
 protected:
  TestIncremental() : d_sat_factory(d_options) {}

  void test_incremental_counter(uint64_t size, bool is_nondet)
  {
    assert(size > 0);

    SolvingContext ctx = SolvingContext(d_nm, d_options, d_sat_factory);

    Node one = d_nm.mk_value(BitVector::mk_true());
    Node cur = d_nm.mk_value(BitVector::mk_zero(size));

    uint32_t i = 0;
    for (;;)
    {
      Node inc = d_nm.mk_node(Kind::BV_INC, {cur});
      Node next, oracle;

      if (is_nondet)
      {
        Node oracle = i > 0 ? d_nm.mk_const(d_nm.mk_bool_type(),
                                            "oracle" + std::to_string(i))
                            : d_nm.mk_value(true);
        next        = d_nm.mk_node(Kind::ITE, {oracle, inc, cur});
      }
      else
      {
        next = inc;
      }

      cur = next;

      Node nonzero = d_nm.mk_node(Kind::BV_REDOR, {cur});
      Node allzero = d_nm.mk_node(Kind::BV_NOT, {nonzero});

      i += 1;

      // TODO refactor to use solve with assumptions when supported
      ctx.push();
      ctx.assert_formula(d_nm.mk_node(Kind::EQUAL, {allzero, one}));
      Result res = ctx.solve();
      if (res == Result::SAT)
      {
        break;
      }
      ASSERT_EQ(res, Result::UNSAT);
      // TODO check that allzero is an unsat assumption
      // ASSERT_TRUE();
      ctx.pop();
      ASSERT_LT(i, (uint32_t) (1 << size));
    }
    ASSERT_EQ(i, (uint32_t) (1 << size));
  }

  void test_incremental_lt(uint32_t size)
  {
    assert(size > 0);

    SolvingContext ctx = SolvingContext(d_nm, d_options, d_sat_factory);

    Node prev;
    uint32_t i = 0;

    for (;;)
    {
      i += 1;
      Type type = d_nm.mk_bv_type(size);
      Node next = d_nm.mk_const(type, "const" + std::to_string(i));

      if (!prev.is_null())
      {
        ctx.assert_formula(d_nm.mk_node(Kind::BV_ULT, {prev, next}));
      }
      prev = next;

      Result res = ctx.solve();
      if (res == Result::UNSAT)
      {
        break;
      }
      ASSERT_EQ(res, Result::SAT);
      ASSERT_LE(i, (uint32_t) (1 << size));
    }
    ASSERT_EQ(i, (uint32_t) (1 << size) + 1);
  }
  NodeManager d_nm;
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
};

TEST_F(TestIncremental, incremental_counter1)
{
  test_incremental_counter(1, false);
}

TEST_F(TestIncremental, incremental_counter2)
{
  test_incremental_counter(2, false);
}

TEST_F(TestIncremental, incremental_counter3)
{
  test_incremental_counter(3, false);
}

TEST_F(TestIncremental, incremental_counter4)
{
  test_incremental_counter(4, false);
}

TEST_F(TestIncremental, incremental_counter8)
{
  test_incremental_counter(8, false);
}

TEST_F(TestIncremental, incremental_counter1_nondet)
{
  test_incremental_counter(1, true);
}

TEST_F(TestIncremental, incremental_counter2_nondet)
{
  test_incremental_counter(2, true);
}

TEST_F(TestIncremental, incremental_counter3_nondet)
{
  test_incremental_counter(3, true);
}

TEST_F(TestIncremental, incremental_counter4_nondet)
{
  test_incremental_counter(4, true);
}

TEST_F(TestIncremental, incremental_counter8_nondet)
{
  test_incremental_counter(8, true);
}

TEST_F(TestIncremental, lt1) { test_incremental_lt(1); }

TEST_F(TestIncremental, lt2) { test_incremental_lt(2); }

TEST_F(TestIncremental, lt3) { test_incremental_lt(3); }

TEST_F(TestIncremental, lt4) { test_incremental_lt(4); }

TEST_F(TestIncremental, lt8) { test_incremental_lt(8); }

TEST_F(TestIncremental, assume_assert1)
{
  option::Options options;
  options.set<uint64_t>(option::Option::REWRITE_LEVEL, 0);
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);

  Type type   = d_nm.mk_bool_type();
  Type atype  = d_nm.mk_array_type(type, type);
  Node array  = d_nm.mk_const(atype, "array1");
  Node index1 = d_nm.mk_const(type, "index1");
  Node index2 = d_nm.mk_const(type, "index2");
  Node read1  = d_nm.mk_node(Kind::SELECT, {array, index1});
  Node read2  = d_nm.mk_node(Kind::SELECT, {array, index2});
  Node eq     = d_nm.mk_node(Kind::EQUAL, {index1, index2});
  Node ne     = d_nm.mk_node(Kind::DISTINCT, {read1, read2});

  ctx.assert_formula(ne);
  // TODO refactor to use solve with assumptions when supported
  ctx.push();
  ctx.assert_formula(eq);
  Result res = ctx.solve();
  ASSERT_EQ(res, Result::UNSAT);
  // TODO check that eq is an unsat assumption
  // ASSERT_TRUE();
  ctx.pop();
  ASSERT_EQ(ctx.solve(), Result::SAT);
}

TEST_F(TestIncremental, lemmas_on_demand1)
{
  option::Options options;
  options.set<uint64_t>(option::Option::REWRITE_LEVEL, 0);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);

  Type type   = d_nm.mk_bool_type();
  Type atype  = d_nm.mk_array_type(type, type);
  Node array  = d_nm.mk_const(atype, "array1");
  Node index1 = d_nm.mk_const(type, "index1");
  Node index2 = d_nm.mk_const(type, "index2");
  Node read1  = d_nm.mk_node(Kind::SELECT, {array, index1});
  Node read2  = d_nm.mk_node(Kind::SELECT, {array, index2});
  Node eq     = d_nm.mk_node(Kind::EQUAL, {index1, index2});
  Node ne     = d_nm.mk_node(Kind::DISTINCT, {read1, read2});

  ctx.assert_formula(eq);
  // TODO refactor to use solve with assumptions when supported
  ctx.push();
  ctx.assert_formula(ne);
  Result res = ctx.solve();
  ASSERT_EQ(res, Result::UNSAT);
  // TODO check that ne is an unsat assumption
  // ASSERT_TRUE();
  ctx.pop();
  ASSERT_EQ(ctx.solve(), Result::SAT);
}
}  // namespace bzla::test
