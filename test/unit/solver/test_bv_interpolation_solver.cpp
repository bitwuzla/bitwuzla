/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <cstdint>
#include <iostream>
#include <unordered_set>

#include "node/node_manager.h"
#include "node/node_utils.h"
#include "sat/sat_solver_factory.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;

class TestBvInterpolationSolver : public TestCommon
{
 protected:
  constexpr static bool s_all_pp_rw       = true;
  constexpr static bool s_all_ass_configs = true;

  enum class AssumptionConfig
  {
    NONE,
    ALL,
    ONLY_B,
  };

  void SetUp() override
  {
    d_options.bv_solver.set_str("bitblast");
    d_options.produce_interpolants.set(true);
    d_options.dbg_check_interpolant.set(true);
    d_options.log_level.set(0);
  }

  void test_get_interpolant(const std::unordered_set<Node>& A,
                            const std::unordered_set<Node>& B)
  {
    test_get_interpolant_aux(A, B, AssumptionConfig::NONE);
    if (s_all_ass_configs)
    {
      test_get_interpolant_aux(A, B, AssumptionConfig::ALL);
      test_get_interpolant_aux(A, B, AssumptionConfig::ONLY_B);
    }
  }

  void test_get_interpolant_aux(const std::unordered_set<Node>& A,
                                const std::unordered_set<Node>& B,
                                AssumptionConfig config)
  {
    // get interpolant
    test_get_interpolant_aux(
        true, d_options.rewrite_level.dflt(), A, B, config);

    if (s_all_pp_rw)
    {
      // get_interpolant when preprocessing is disabled
      test_get_interpolant_aux(
          false, d_options.rewrite_level.dflt(), A, B, config);
      // get_interpolant when rewriting is disabled
      test_get_interpolant_aux(true, 0, A, B, config);
      // get_interpolant when preprocessing and rewriting is disabled
      test_get_interpolant_aux(false, 0, A, B, config);
    }
  }

  void test_get_interpolant_aux(bool pp,
                                uint64_t rwl,
                                const std::unordered_set<Node>& A,
                                const std::unordered_set<Node>& B,
                                AssumptionConfig config)
  {
    if (d_options.log_level())
    {
      std::cout << std::endl
                << ">> rewrite level: " << rwl
                << "  pp: " << (pp ? "enabled" : "disabled") << std::endl;
    }
    d_options.preprocess.set(pp);
    d_options.rewrite_level.set(rwl);
    sat::SatSolverFactory sat_factory(d_options);
    SolvingContext ctx(d_nm, d_options, sat_factory);
    if (config == AssumptionConfig::ALL)
    {
      ctx.push();
    }
    for (const auto& a : A)
    {
      ctx.assert_formula(a);
    }
    if (config == AssumptionConfig::ONLY_B)
    {
      ctx.push();
    }
    for (const auto& a : B)
    {
      ctx.assert_formula(a);
    }
    // (and A B) must be unsat
    ASSERT_EQ(ctx.solve(), Result::UNSAT);
    Node interpolant = ctx.get_interpolant(A);
    ASSERT_FALSE(interpolant.is_null());
  }

  void test_get_interpolant_inc(const std::unordered_set<Node>& A,
                                const std::unordered_set<Node>& B)
  {
    test_get_interpolant_inc_aux(A, B, AssumptionConfig::NONE);
    if (s_all_ass_configs)
    {
      test_get_interpolant_inc_aux(A, B, AssumptionConfig::ALL);
      test_get_interpolant_inc_aux(A, B, AssumptionConfig::ONLY_B);
    }
  }

  void test_get_interpolant_inc_aux(const std::unordered_set<Node>& A,
                                    const std::unordered_set<Node>& B,
                                    AssumptionConfig config)
  {
    // get interpolant
    test_get_interpolant_aux(
        true, d_options.rewrite_level.dflt(), A, B, config);

    if (s_all_pp_rw)
    {
      // get_interpolant when preprocessing is disabled
      test_get_interpolant_aux(
          false, d_options.rewrite_level.dflt(), A, B, config);
      // get_interpolant when rewriting is disabled
      test_get_interpolant_aux(true, 0, A, B, config);
      // get_interpolant when preprocessing and rewriting is disabled
      test_get_interpolant_aux(false, 0, A, B, config);
    }
  }

  void test_get_interpolant_inc_aux(bool pp,
                                    uint64_t rwl,
                                    const std::unordered_set<Node>& A,
                                    const std::unordered_set<Node>& B,
                                    AssumptionConfig config)
  {
    if (d_options.log_level())
    {
      std::cout << std::endl
                << ">> rewrite level: " << rwl
                << "  pp: " << (pp ? "enabled" : "disabled") << std::endl;
    }
    d_options.preprocess.set(pp);
    d_options.rewrite_level.set(rwl);
    SolvingContext ctx(d_nm, d_options);
    if (config == AssumptionConfig::ALL)
    {
      ctx.push();
    }
    for (const auto& a : A)
    {
      ctx.assert_formula(a);
    }
    for (const auto& a : B)
    {
      ctx.push();
      ctx.assert_formula(a);
      // (and A B) must be unsat
      ASSERT_EQ(ctx.solve(), Result::UNSAT);
      Node interpolant = ctx.get_interpolant(A);
      ASSERT_FALSE(interpolant.is_null());
      ctx.push();
    }
  }

  option::Options d_options;
  NodeManager d_nm;
};

TEST_F(TestBvInterpolationSolver, solve)
{
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ASSERT_NO_FATAL_FAILURE(ctx.solve());
}

TEST_F(TestBvInterpolationSolver, produce_interpolants)
{
  d_options.produce_interpolants.set(false);
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx = SolvingContext(d_nm, d_options, sat_factory);
  ctx.assert_formula(d_nm.mk_const(d_nm.mk_bool_type()));
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({}), "produce_interpolants");
}

TEST_F(TestBvInterpolationSolver, prop)
{
  option::Options options;
  options.bv_solver.set_str("prop");
  options.produce_interpolants.set(true);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ctx.assert_formula(d_nm.mk_const(d_nm.mk_bool_type()));
  ctx.solve();
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, preprop)
{
  option::Options options;
  options.bv_solver.set_str("preprop");
  options.produce_interpolants.set(true);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ctx.assert_formula(d_nm.mk_const(d_nm.mk_bool_type()));
  ctx.solve();
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, not_unsat1)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node B = d_nm.mk_node(Kind::NOT, {x});
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(B);
  ASSERT_EQ(ctx.solve(), Result::SAT);
  // (and A B) not unsat
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, not_unsat2)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node A = d_nm.mk_node(Kind::NOT, {x});
  Node B = d_nm.mk_node(Kind::NOT, {x});
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(A);
  ctx.assert_formula(B);
  ASSERT_EQ(ctx.solve(), Result::SAT);
  // (and A B) not unsat
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({A}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, not_unsat3)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node A = x;
  Node B = x;
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(A);
  ctx.assert_formula(B);
  ASSERT_EQ(ctx.solve(), Result::SAT);
  // (and A B) not unsat
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({A}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, not_unsat4)
{
  Type bv8 = d_nm.mk_bv_type(2);
  Node x   = d_nm.mk_const(bv8, "x");
  Node y   = d_nm.mk_const(bv8, "y");
  Node or0 =
      d_nm.mk_node(Kind::EQUAL, {x, d_nm.mk_value(BitVector::mk_zero(2))});
  Node or1 =
      d_nm.mk_node(Kind::BV_UGE, {x, d_nm.mk_node(Kind::BV_AND, {x, y})});
  Node A = d_nm.mk_node(Kind::OR, {or0, or1});
  Node B = d_nm.mk_node(Kind::BV_ULT, {x, y});
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(A);
  ctx.assert_formula(B);
  ASSERT_EQ(ctx.solve(), Result::SAT);
  // (and A B) not unsat
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({A}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, unknown)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node A = d_nm.mk_node(Kind::NOT, {x});
  Node B = x;
  option::Options options;
  options.produce_interpolants.set(true);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx(d_nm, options, sat_factory);
  ctx.assert_formula(A);
  ctx.assert_formula(B);
  ASSERT_DEATH_DEBUG(ctx.get_interpolant({A}), "d_sat_state == Result::UNSAT");
}

TEST_F(TestBvInterpolationSolver, interpol1)
{
  Node x              = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node A              = d_nm.mk_node(Kind::NOT, {x});
  Node B              = x;
  test_get_interpolant({A}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol2)
{
  Node x              = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y              = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  std::unordered_set<Node> A = {x, d_nm.mk_node(Kind::NOT, {x})};
  Node B                     = y;
  // A is already unsat
  option::Options opts_solve;
  sat::SatSolverFactory sat_factory(opts_solve);
  SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
  for (const auto& a : A)
  {
    ctx_solve.assert_formula(a);
  }
  ASSERT_EQ(ctx_solve.solve(), Result::UNSAT);

  test_get_interpolant_aux(
      A, {B}, TestBvInterpolationSolver::AssumptionConfig::NONE);
  test_get_interpolant_aux(
      A, {B}, TestBvInterpolationSolver::AssumptionConfig::ALL);
  test_get_interpolant_aux(
      A, {B}, TestBvInterpolationSolver::AssumptionConfig::ONLY_B);
}

TEST_F(TestBvInterpolationSolver, interpol3)
{
  Type bv1    = d_nm.mk_bv_type(1);
  Node x      = d_nm.mk_const(bv1, "x");
  Node y      = d_nm.mk_const(bv1, "y");
  Node one    = d_nm.mk_value(BitVector::mk_true());
  Node zero   = d_nm.mk_value(BitVector::mk_false());
  Node bvnoty = d_nm.mk_node(Kind::BV_NOT, {y});

  // (= x (bvnot y))
  Node A0 = d_nm.mk_node(Kind::EQUAL, {x, bvnoty});
  // (= #b0 (bvnot y))
  Node A1 = d_nm.mk_node(Kind::EQUAL, {zero, bvnoty});
  // (and (bvult x (bvnot y)) (= (bvnot y) #b0))
  Node B = d_nm.mk_node(Kind::AND,
                        {d_nm.mk_node(Kind::BV_ULT, {x, bvnoty}),
                         d_nm.mk_node(Kind::EQUAL, {bvnoty, zero})});
  test_get_interpolant({A0, A1}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol4)
{
  Type bv1  = d_nm.mk_bv_type(1);
  Type bv2  = d_nm.mk_bv_type(2);
  Node s0   = d_nm.mk_const(bv2, "s0");
  Node s1   = d_nm.mk_const(bv2, "s1");
  Node s2   = d_nm.mk_const(bv2, "s2");
  Node one  = d_nm.mk_const(bv2, "one");
  Node goal = d_nm.mk_const(bv2, "goal");
  Node o0   = d_nm.mk_const(bv1, "o0");
  Node o1   = d_nm.mk_const(bv1, "o1");

  // (= s0 (_ bv0 2))
  Node A0 =
      d_nm.mk_node(Kind::EQUAL, {s0, d_nm.mk_value(BitVector::mk_zero(2))});
  // (= one (_ bv1 2))
  Node A1 =
      d_nm.mk_node(Kind::EQUAL, {one, d_nm.mk_value(BitVector::mk_one(2))});
  // (= goal (_ bv3 2))
  Node A2 = d_nm.mk_node(Kind::EQUAL,
                         {goal, d_nm.mk_value(BitVector::from_ui(2, 3))});

  // (= s0 goal)
  Node B = d_nm.mk_node(Kind::EQUAL, {s0, goal});

  test_get_interpolant({A0, A1, A2}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol5)
{
  Node x = d_nm.mk_const(d_nm.mk_bv_type(6), "x");
  // (= ((_ extract 5 1) x) ((_ extract 4 0) x))
  Node A0 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {5, 1}),
                          d_nm.mk_node(Kind::BV_EXTRACT, {x}, {4, 0})});
  // (= ((_ extract 0 0) x) (_ bv0 1))
  Node A1 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {0, 0}),
                          d_nm.mk_value(BitVector::mk_zero(1))});
  // (distinct x (_ bv0 6))
  Node B =
      d_nm.mk_node(Kind::DISTINCT, {x, d_nm.mk_value(BitVector::mk_zero(6))});

  test_get_interpolant({A0, A1}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol6)
{
  uint64_t bw = 4;
  Type bv     = d_nm.mk_bv_type(bw);
  Node x      = d_nm.mk_const(bv, "x");
  Node y      = d_nm.mk_const(bv, "y");
  Node z      = d_nm.mk_const(bv, "z");
  Node zero   = d_nm.mk_value(BitVector::mk_zero(bw));
  Node one    = d_nm.mk_value(BitVector::mk_one(bw));
  // (= z (bvadd x y))
  Node A0 = d_nm.mk_node(Kind::EQUAL, {z, d_nm.mk_node(Kind::BV_ADD, {x, y})});
  // (distinct x y)
  Node A1 = d_nm.mk_node(Kind::DISTINCT, {x, y});
  // (and
  //   (distinct x (_ bv0 1024))
  //   (= (bvand x (bvsub x (_ bv1 1024))) (_ bv0 1024))))
  Node A2 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::DISTINCT, {x, zero}),
       d_nm.mk_node(Kind::EQUAL,
                    {d_nm.mk_node(Kind::BV_AND,
                                  {x, d_nm.mk_node(Kind::BV_SUB, {x, one})}),
                     zero})});
  // (and
  //   (distinct y (_ bv0 1024))
  //   (= (bvand y (bvsub y (_ bv1 1024))) (_ bv0 1024)))
  Node A3 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::DISTINCT, {y, zero}),
       d_nm.mk_node(Kind::EQUAL,
                    {d_nm.mk_node(Kind::BV_AND,
                                  {y, d_nm.mk_node(Kind::BV_SUB, {y, one})}),
                     zero})});
  //   (and
  //     (distinct z (_ bv0 1024))
  //     (= (bvand z (bvsub z (_ bv1 1024))) (_ bv0 1024)))
  Node B0 = d_nm.mk_node(Kind::DISTINCT, {z, zero});
  Node B1 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_AND, {z, d_nm.mk_node(Kind::BV_SUB, {z, one})}),
       zero});

  test_get_interpolant({A0, A1, A2, A3}, {B0, B1});
}

TEST_F(TestBvInterpolationSolver, interpol7)
{
  Type bv4 = d_nm.mk_bv_type(4);
  Node a   = d_nm.mk_const(bv4, "a");
  Node b   = d_nm.mk_const(bv4, "b");
  Node c   = d_nm.mk_const(bv4, "c");
  // (bvult a (bvadd b c))
  Node A0 = d_nm.mk_node(Kind::BV_ULT, {a, d_nm.mk_node(Kind::BV_ADD, {b, c})});
  // (bvult c b)
  Node A1 = d_nm.mk_node(Kind::BV_ULT, {c, b});
  // (bvugt c b)
  Node B = d_nm.mk_node(Kind::BV_UGT, {c, b});

  test_get_interpolant({A0, A1}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol8)
{
  uint64_t bw = 16;
  Type bv     = d_nm.mk_bv_type(bw);
  Node x      = d_nm.mk_const(bv, "x");
  Node y      = d_nm.mk_const(bv, "y");
  Node zero   = d_nm.mk_value(BitVector::mk_zero(bw));
  Node one    = d_nm.mk_value(BitVector::mk_one(bw));
  Node two    = d_nm.mk_value(BitVector::from_ui(bw, 2));
  // (distinct (_ bv0 16) (bvadd x y))
  Node A0 =
      d_nm.mk_node(Kind::DISTINCT, {zero, d_nm.mk_node(Kind::BV_ADD, {x, y})});
  // (= (bvadd x (_ bv2 16)) (bvneg (bvadd y (bvmul x (_ bv2 16)))))
  Node A1 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {x, two}),
       d_nm.mk_node(
           Kind::BV_NEG,
           {d_nm.mk_node(Kind::BV_ADD,
                         {y, d_nm.mk_node(Kind::BV_MUL, {x, two})})})});
  option::Options options;
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ctx.assert_formula(A0);
  ctx.assert_formula(A1);
  assert(ctx.solve() == Result::SAT);
  // (= (_ bv0 16) (bvadd x (_ bv1 16)))
  Node B =
      d_nm.mk_node(Kind::EQUAL, {zero, d_nm.mk_node(Kind::BV_ADD, {x, one})});

  test_get_interpolant({A0, A1}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol9)
{
  Type bv32 = d_nm.mk_bv_type(32);
  Type bv30 = d_nm.mk_bv_type(30);
  Node x    = d_nm.mk_const(d_nm.mk_bv_type(2), "x");
  Node one  = d_nm.mk_value(BitVector::mk_one(32));
  Node four = d_nm.mk_value(BitVector::from_ui(32, 4));
  Node xext = d_nm.mk_node(Kind::BV_ZERO_EXTEND, {x}, {30});
  // (bvule
  //  (bvmul
  //    ((_ zero_extend 30) x)
  //    (bvmul
  //      (_ bv4 32)
  //      (bvmul ((_ zero_extend 30) x) (_ bv4 32))))
  //  (_ bv119 32))
  Node A0 = d_nm.mk_node(
      Kind::BV_ULE,
      {d_nm.mk_node(
           Kind::BV_MUL,
           {xext,
            d_nm.mk_node(Kind::BV_MUL,
                         {four, d_nm.mk_node(Kind::BV_MUL, {xext, four})})}),
       d_nm.mk_value(BitVector::from_ui(32, 119))});
  // (bvuge
  //   (bvadd
  //     (_ bv1 32)
  //     (bvmul
  //       ((_ zero_extend 30) x)
  //       (bvmul
  //         (_ bv4 32)
  //         (bvmul
  //           ((_ zero_extend 30) x)
  //           (_ bv4 32)))))
  //   (_ bv128 32))
  Node B = d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(
           Kind::BV_ADD,
           {one,
            {d_nm.mk_node(
                Kind::BV_MUL,
                {xext,
                 d_nm.mk_node(
                     Kind::BV_MUL,
                     {four, d_nm.mk_node(Kind::BV_MUL, {xext, four})})})}}),
       d_nm.mk_value(BitVector::from_ui(32, 128))});

  test_get_interpolant({A0}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol10)
{
  uint64_t bw = 4;
  Type bv     = d_nm.mk_bv_type(bw);
  Node x      = d_nm.mk_const(bv, "x");
  Node s      = d_nm.mk_const(bv, "s");
  Node t      = d_nm.mk_const(bv, "t");
  Node val_x  = d_nm.mk_value(BitVector::from_ui(bw, 3));
  Node val_s  = d_nm.mk_value(BitVector::from_ui(bw, 2));
  Node val_t  = d_nm.mk_value(BitVector::from_ui(bw, 6));
  Node A0 =
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND,
                                 {
                                     d_nm.mk_node(Kind::EQUAL, {x, val_x}),
                                     d_nm.mk_node(Kind::EQUAL, {s, val_s}),
                                 }),
                    d_nm.mk_node(Kind::EQUAL, {t, val_t})});
  Node B =
      d_nm.mk_node(Kind::DISTINCT, {d_nm.mk_node(Kind::BV_MUL, {x, s}), t});
  test_get_interpolant({A0}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol11)
{
  Type bv4    = d_nm.mk_bv_type(4);
  Node x      = d_nm.mk_const(bv4, "x");
  Node s      = d_nm.mk_const(bv4, "s");
  Node t      = d_nm.mk_const(bv4, "t");
  Node val_x0 = d_nm.mk_value(BitVector::from_ui(4, 3));
  Node val_s0 = d_nm.mk_value(BitVector::from_ui(4, 2));
  Node val_t0 = d_nm.mk_value(BitVector::from_ui(4, 6));
  Node val_x1 = d_nm.mk_value(BitVector::from_ui(4, 5));
  Node val_s1 = d_nm.mk_value(BitVector::from_ui(4, 4));
  Node val_t1 = d_nm.mk_value(BitVector::from_ui(4, 4));
  Node val_x2 = d_nm.mk_value(BitVector::from_ui(4, 5));
  Node val_s2 = d_nm.mk_value(BitVector::from_ui(4, 3));
  Node val_t2 = d_nm.mk_value(BitVector::from_ui(4, 15));
  Node or0 =
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND,
                                 {
                                     d_nm.mk_node(Kind::EQUAL, {x, val_x0}),
                                     d_nm.mk_node(Kind::EQUAL, {s, val_s0}),
                                 }),
                    d_nm.mk_node(Kind::EQUAL, {t, val_t0})});
  Node or1 =
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND,
                                 {
                                     d_nm.mk_node(Kind::EQUAL, {x, val_x1}),
                                     d_nm.mk_node(Kind::EQUAL, {s, val_s1}),
                                 }),
                    d_nm.mk_node(Kind::EQUAL, {t, val_t1})});
  Node or2 =
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND,
                                 {
                                     d_nm.mk_node(Kind::EQUAL, {x, val_x2}),
                                     d_nm.mk_node(Kind::EQUAL, {s, val_s2}),
                                 }),
                    d_nm.mk_node(Kind::EQUAL, {t, val_t2})});
  Node A0 = d_nm.mk_node(Kind::OR, {or0, d_nm.mk_node(Kind::OR, {or1, or2})});
  Node B =
      d_nm.mk_node(Kind::DISTINCT, {d_nm.mk_node(Kind::BV_MUL, {x, s}), t});
  test_get_interpolant({A0}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_inc1)
{
  uint64_t bw = 4;
  Type bv     = d_nm.mk_bv_type(bw);
  Node x      = d_nm.mk_const(bv, "x");
  Node s      = d_nm.mk_const(bv, "s");
  Node t      = d_nm.mk_const(bv, "t");
  Node val_x  = d_nm.mk_value(BitVector::from_ui(bw, 3));
  Node val_s  = d_nm.mk_value(BitVector::from_ui(bw, 2));
  Node val_t  = d_nm.mk_value(BitVector::from_ui(bw, 6));
  Node A0 =
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND,
                                 {
                                     d_nm.mk_node(Kind::EQUAL, {x, val_x}),
                                     d_nm.mk_node(Kind::EQUAL, {s, val_s}),
                                 }),
                    d_nm.mk_node(Kind::EQUAL, {t, val_t})});
  Node B =
      d_nm.mk_node(Kind::DISTINCT, {d_nm.mk_node(Kind::BV_MUL, {x, s}), t});
  Node C = d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_UREM, {x, s}), t});
  test_get_interpolant_inc({A0}, {B, C});
}

TEST_F(TestBvInterpolationSolver, interpol_bv_abstr1)
{
  d_options.abstraction.set(true);
  d_options.abstraction_bv_size.set(8);
  Type bv8      = d_nm.mk_bv_type(8);
  Node a        = d_nm.mk_const(bv8, "a");
  Node c        = d_nm.mk_const(bv8, "c");
  Node one      = d_nm.mk_value(BitVector::mk_one(8));
  Node shift_by = d_nm.mk_const(bv8, "shift_by");
  // (bvult shift_by (_ bv8 8))
  Node A0 = d_nm.mk_node(Kind::BV_ULT,
                         {shift_by, d_nm.mk_value(BitVector::from_ui(8, 8))});
  // (= (_ bv1 8) (bvshl (_ bv1 8) shift_by))
  Node A1 = d_nm.mk_node(Kind::EQUAL,
                         {one, d_nm.mk_node(Kind::BV_SHL, {one, shift_by})});
  // (= c (bvudiv a (_ bv1 8)))
  Node A2 =
      d_nm.mk_node(Kind::EQUAL, {c, d_nm.mk_node(Kind::BV_UDIV, {a, one})});
  // (distinct c (bvlshr a shift_by))
  Node B = d_nm.mk_node(Kind::DISTINCT,
                        {c, d_nm.mk_node(Kind::BV_SHR, {a, shift_by})});
  test_get_interpolant({A0, A1, A2}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_bv_abstr2)
{
  d_options.abstraction.set(true);
  d_options.abstraction_bv_size.set(3);
  Type bv3      = d_nm.mk_bv_type(3);
  Node a        = d_nm.mk_const(bv3, "a");
  Node c        = d_nm.mk_const(bv3, "c");
  Node pow2     = d_nm.mk_const(bv3, "pow2");
  Node one      = d_nm.mk_value(BitVector::mk_one(3));
  Node shift_by = d_nm.mk_const(bv3, "shift_by");
  // (bvult shift_by (_ bv3 3))
  Node A0 = d_nm.mk_node(Kind::BV_ULT,
                         {shift_by, d_nm.mk_value(BitVector::from_ui(3, 3))});
  // (= pow2 (bvshl (_ bv1 2) shift_by))
  Node A1 = d_nm.mk_node(Kind::EQUAL,
                         {pow2, d_nm.mk_node(Kind::BV_SHL, {one, shift_by})});
  // (= c (bvudiv a pow2))
  Node A2 =
      d_nm.mk_node(Kind::EQUAL, {c, d_nm.mk_node(Kind::BV_UDIV, {a, pow2})});
  // (distinct c (bvlshr a shift_by))
  Node B = d_nm.mk_node(Kind::DISTINCT,
                        {c, d_nm.mk_node(Kind::BV_SHR, {a, shift_by})});
  test_get_interpolant({A0, A1, A2}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_bv_abstr3)
{
  d_options.abstraction.set(true);
  d_options.abstraction_bv_size.set(6);
  Type bv6      = d_nm.mk_bv_type(6);
  Node a        = d_nm.mk_const(bv6, "a");
  Node c        = d_nm.mk_const(bv6, "c");
  Node pow2     = d_nm.mk_const(bv6, "pow2");
  Node one      = d_nm.mk_value(BitVector::mk_one(6));
  Node mask     = d_nm.mk_const(bv6, "mask");
  Node shift_by = d_nm.mk_const(bv6, "shift_by");
  // (bvult shift_by (_ bv6 6))
  Node A0 = d_nm.mk_node(Kind::BV_ULT,
                         {shift_by, d_nm.mk_value(BitVector::from_ui(6, 6))});
  // (= pow2 (bvshl (_ bv1 6) shift_by))
  Node A1 = d_nm.mk_node(Kind::EQUAL,
                         {pow2, d_nm.mk_node(Kind::BV_SHL, {one, shift_by})});
  // (= mask (bvnot (bvshl (bvnot (_ bv0 6)) shift_by)))
  Node A2 = d_nm.mk_node(
      Kind::EQUAL,
      {mask,
       d_nm.mk_node(
           Kind::BV_NOT,
           {d_nm.mk_node(Kind::BV_SHL,
                         {d_nm.mk_node(Kind::BV_NOT,
                                       {d_nm.mk_value(BitVector::mk_zero(6))}),
                          shift_by})})});
  // (= c (bvurem a pow2))
  Node A3 =
      d_nm.mk_node(Kind::EQUAL, {c, d_nm.mk_node(Kind::BV_UREM, {a, pow2})});
  // (distinct c (bvand mask a))
  Node B =
      d_nm.mk_node(Kind::DISTINCT, {c, d_nm.mk_node(Kind::BV_AND, {mask, a})});
  test_get_interpolant({A0, A1, A2, A3}, {B});
}

#if 0
// For now, since we now strictly follow the definition of interpolation where
// the interpolant may only contain shared uninterpreted symbols, we don't
// support interpolation when arrays and UF are involved.

TEST_F(TestBvInterpolationSolver, interpol_array1)
{
  Type arr = d_nm.mk_array_type(d_nm.mk_bool_type(), d_nm.mk_bool_type());
  Node a1  = d_nm.mk_const(arr, "a1");
  Node a2  = d_nm.mk_const(arr, "a2");
  Node a3  = d_nm.mk_const(arr, "a3");
  Node a4  = d_nm.mk_const(arr, "a4");
  Node a5  = d_nm.mk_const(arr, "a5");

  Node A0 = utils::mk_nary(d_nm,
                           Kind::AND,
                           {
                               d_nm.mk_node(Kind::DISTINCT, {a1, a2}),
                               d_nm.mk_node(Kind::DISTINCT, {a1, a3}),
                               d_nm.mk_node(Kind::DISTINCT, {a1, a4}),
                               d_nm.mk_node(Kind::DISTINCT, {a1, a5}),
                           });
  Node A1 = utils::mk_nary(d_nm,
                           Kind::AND,
                           {
                               d_nm.mk_node(Kind::DISTINCT, {a2, a3}),
                               d_nm.mk_node(Kind::DISTINCT, {a2, a4}),
                               d_nm.mk_node(Kind::DISTINCT, {a2, a5}),
                           });
  Node A2 = utils::mk_nary(d_nm,
                           Kind::AND,
                           {
                               d_nm.mk_node(Kind::DISTINCT, {a3, a4}),
                               d_nm.mk_node(Kind::DISTINCT, {a3, a5}),
                           });
  Node B  = d_nm.mk_node(Kind::DISTINCT, {a4, a5});

  test_get_interpolant({A0, A1, A2}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_array2)
{
  Type bv1  = d_nm.mk_bv_type(1);
  Type arr  = d_nm.mk_array_type(bv1, bv1);
  Node zero = d_nm.mk_value(BitVector::mk_zero(1));
  Node one  = d_nm.mk_value(BitVector::mk_one(1));
  //(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
  Node a = d_nm.mk_const(arr, "a");
  //(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
  Node b = d_nm.mk_const(arr, "b");
  // (= (select a #b0) #b0)
  Node A0 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {a, zero}), zero});
  // (= (select b #b0) #b0)
  Node A1 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {b, zero}), zero});
  // (distinct a b)
  Node A2 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  // (= (select a #b1) #b0)
  Node C0 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {a, one}), zero});
  // (= (select b #b1) #b0)
  Node C1 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {b, one}), zero});

  Node B = d_nm.mk_node(Kind::AND, {C0, C1});

  test_get_interpolant({A0, A1, A2}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_array3)
{
  Type bv3   = d_nm.mk_bv_type(3);
  Type arr   = d_nm.mk_array_type(bv3, bv3);
  Node zero  = d_nm.mk_value(BitVector::mk_zero(3));
  Node one   = d_nm.mk_value(BitVector::mk_one(3));
  Node two   = d_nm.mk_value(BitVector::from_ui(3, 2));
  Node three = d_nm.mk_value(BitVector::from_ui(3, 3));
  Node four  = d_nm.mk_value(BitVector::from_ui(3, 4));
  Node five  = d_nm.mk_value(BitVector::from_ui(3, 5));
  Node six   = d_nm.mk_value(BitVector::from_ui(3, 6));
  Node seven = d_nm.mk_value(BitVector::from_ui(3, 7));
  //(declare-fun a () (Array (_ BitVec 3) (_ BitVec 3)))
  Node a = d_nm.mk_const(arr, "a");
  //(declare-fun b () (Array (_ BitVec 3) (_ BitVec 3)))
  Node b = d_nm.mk_const(arr, "b");
  // (! (= (select a (_ bv1 3)) (select b (_ bv1 3))) :named a0)
  Node A0 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, one}),
                          d_nm.mk_node(Kind::SELECT, {b, one})});
  // (! (= (select a (_ bv3 3)) (select b (_ bv3 3))) :named a1)
  Node A1 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, three}),
                          d_nm.mk_node(Kind::SELECT, {b, three})});
  // (! (= (select a (_ bv5 3)) (select b (_ bv5 3))) :named a2)
  Node A2 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, five}),
                          d_nm.mk_node(Kind::SELECT, {b, five})});
  // (! (= (select a (_ bv7 3)) (select b (_ bv7 3))) :named a3)
  Node A3 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, seven}),
                          d_nm.mk_node(Kind::SELECT, {b, seven})});
  // (! (not (= a b)) :named a4)
  Node A4 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  //(define-fun b0 () Bool (= (select a (_ bv0 3)) (select b (_ bv0 3))))
  Node C0 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, zero}),
                          d_nm.mk_node(Kind::SELECT, {b, zero})});
  //(define-fun b1 () Bool (= (select a (_ bv2 3)) (select b (_ bv2 3))))
  Node C1 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, two}),
                          d_nm.mk_node(Kind::SELECT, {b, two})});
  //(define-fun b2 () Bool (= (select a (_ bv4 3)) (select b (_ bv4 3))))
  Node C2 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, four}),
                          d_nm.mk_node(Kind::SELECT, {b, four})});
  //(define-fun b3 () Bool (= (select a (_ bv6 3)) (select b (_ bv6 3))))
  Node C3 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, six}),
                          d_nm.mk_node(Kind::SELECT, {b, six})});
  Node B  = utils::mk_nary(d_nm, Kind::AND, {C0, C1, C2, C3});
  option::Options options;
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ctx.assert_formula(A0);
  ctx.assert_formula(A1);
  ctx.assert_formula(A2);
  ctx.assert_formula(A3);
  ctx.assert_formula(A4);
  ctx.assert_formula(B);
  assert(ctx.solve() == Result::UNSAT);
  test_get_interpolant({A0, A1, A2, A3, A4}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_array4a)
{
  Type btype = d_nm.mk_bool_type();
  Type arr   = d_nm.mk_array_type(btype, btype);
  // (declare-const h (Array Bool Bool))
  Node h = d_nm.mk_const(arr, "h");
  // (declare-const i Bool)
  Node i = d_nm.mk_const(btype, "i");
  // (declare-const e Bool)
  Node e = d_nm.mk_const(btype, "e");
  // (define-fun hh () (Array Bool Bool) (store h i e))
  Node hh = d_nm.mk_node(Kind::STORE, {h, i, e});
  // (declare-const a Bool)
  Node a = d_nm.mk_const(btype, "a");
  // (declare-const b Bool)
  Node b = d_nm.mk_const(btype, "b");

  // (distinct a b)
  Node A0 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  // (distinct (select h a) (select hh a))
  Node A1 = d_nm.mk_node(Kind::DISTINCT,
                         {d_nm.mk_node(Kind::SELECT, {h, a}),
                          d_nm.mk_node(Kind::SELECT, {hh, a})});
  // (distinct (select h b) (select hh b))
  Node B = d_nm.mk_node(Kind::DISTINCT,
                        {d_nm.mk_node(Kind::SELECT, {h, b}),
                         d_nm.mk_node(Kind::SELECT, {hh, b})});
  test_get_interpolant({A0, A1}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_array4b)
{
  // this should not have an interpolant over h and hh
  Type btype = d_nm.mk_bool_type();
  Type arr   = d_nm.mk_array_type(btype, btype);
  // (declare-const h (Array Bool Bool))
  Node h = d_nm.mk_const(arr, "h");
  // (declare-const hh (Array Bool Bool))
  Node hh = d_nm.mk_const(arr, "hh");
  // (declare-const i Bool)
  Node i = d_nm.mk_const(btype, "i");
  // (declare-const e Bool)
  Node e = d_nm.mk_const(btype, "e");
  // (declare-const a Bool)
  Node a = d_nm.mk_const(btype, "a");
  // (declare-const b Bool)
  Node b = d_nm.mk_const(btype, "b");

  // (= hh (store h i e))
  Node A =
      d_nm.mk_node(Kind::EQUAL, {hh, d_nm.mk_node(Kind::STORE, {h, i, e})});
  // (distinct a b)
  Node B0 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  // (distinct (select h a) (select hh a))
  Node B1 = d_nm.mk_node(Kind::DISTINCT,
                         {d_nm.mk_node(Kind::SELECT, {h, a}),
                          d_nm.mk_node(Kind::SELECT, {hh, a})});
  // (distinct (select h b) (select hh b))
  Node B2 = d_nm.mk_node(Kind::DISTINCT,
                         {d_nm.mk_node(Kind::SELECT, {h, b}),
                          d_nm.mk_node(Kind::SELECT, {hh, b})});
  Node B = utils::mk_nary(d_nm, Kind::AND, {B0, B1, B2});
  test_get_interpolant({A}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_fp1)
{
  Type f16       = d_nm.mk_fp_type(5, 11);
  Node a         = d_nm.mk_const(f16, "a");
  Node b         = d_nm.mk_const(f16, "b");
  Node rm        = d_nm.mk_const(d_nm.mk_rm_type(), "rm");
  Node rna       = d_nm.mk_value(RoundingMode::RNA);
  Node rne       = d_nm.mk_value(RoundingMode::RNE);
  Node rtn       = d_nm.mk_value(RoundingMode::RTN);
  Node rtp       = d_nm.mk_value(RoundingMode::RTP);
  Node rtz       = d_nm.mk_value(RoundingMode::RTZ);
  Node fpneg_a   = d_nm.mk_node(Kind::FP_NEG, {a});
  Node fpabs_a   = d_nm.mk_node(Kind::FP_ABS, {a});
  Node fpposzero = d_nm.mk_value(FloatingPoint::fpzero(5, 11, false));
  Node fpnegzero = d_nm.mk_value(FloatingPoint::fpzero(5, 11, true));
  Node A0 = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NAN, {b})});
  // (not (fp.isNegative b))
  Node A1 = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NEG, {b})});
  // (fp.isPositive b)
  Node A2 = d_nm.mk_node(Kind::FP_IS_POS, {b});
  // (and (fp.leq a a) (not (fp.lt a a)))
  Node A3 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::FP_LEQ, {a, a}),
       d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_LT, {a, a})})});
  // (and
  //           (fp.geq (fp.sqrt RNE a) (fp.roundToIntegral RNE b))
  //           (not (fp.gt (fp.add RNA a a) b)))
  Node A4 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::FP_GEQ,
                    {d_nm.mk_node(Kind::FP_SQRT, {rne, a}),
                     d_nm.mk_node(Kind::FP_RTI, {rne, b})}),
       d_nm.mk_node(
           Kind::NOT,
           {d_nm.mk_node(Kind::FP_GT,
                         {d_nm.mk_node(Kind::FP_ADD, {rna, a, a}), b})})});
  // (fp.geq (fp.add RTN a b) (fp.sub RTN a b))
  Node A5 = d_nm.mk_node(Kind::FP_GEQ,
                         {d_nm.mk_node(Kind::FP_ADD, {rtn, a, b}),
                          d_nm.mk_node(Kind::FP_SUB, {rtn, a, b})});
  // (fp.leq (fp.mul RTP a (_ +zero 5 11)) (_ -zero 5 11))
  Node A6 = d_nm.mk_node(
      Kind::FP_LEQ,
      {d_nm.mk_node(Kind::FP_MUL, {rtp, a, fpposzero}), fpnegzero});
  // (fp.isNaN (fp.div RTP a (_ +zero 5 11)))
  Node A7 = d_nm.mk_node(Kind::FP_IS_NAN,
                         {d_nm.mk_node(Kind::FP_DIV, {rtp, a, fpposzero})});
  // (= (fp.add rm (fp.mul RTZ a b) a) (fp.fma RTZ a b (fp.rem a b)))
  Node A8 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::FP_ADD,
                    {rm, d_nm.mk_node(Kind::FP_MUL, {rtz, a, b}), a}),
       d_nm.mk_node(Kind::FP_FMA,
                    {rtz, a, b, d_nm.mk_node(Kind::FP_REM, {a, b})})});
  // (check-sat-assuming (b0 b1 b2 b3 b4 b5))
  // (define-fun b0 () Bool (= (fp.abs a) b))
  Node C0 = d_nm.mk_node(Kind::EQUAL, {fpabs_a, b});
  // (define-fun b1 () Bool (= (fp.abs a) (fp.abs (fp.neg a))))
  Node C1 = d_nm.mk_node(Kind::EQUAL,
                         {fpabs_a, d_nm.mk_node(Kind::FP_ABS, {fpneg_a})});
  // (define-fun b2 () Bool
  //   (not (and (fp.isNormal (fp.neg a)) (not (fp.isNormal a)))))
  Node C2 = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::FP_IS_NORMAL, {fpneg_a}),
           d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NORMAL, {a})})})});
  // (define-fun b3 () Bool
  //   (not (and (fp.isSubnormal (fp.neg a)) (not (fp.isSubnormal a)))))
  Node C3 = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::FP_IS_SUBNORMAL, {fpneg_a}),
           d_nm.mk_node(Kind::NOT,
                        {d_nm.mk_node(Kind::FP_IS_SUBNORMAL, {a})})})});
  // (define-fun b4 () Bool (and (fp.isZero (fp.neg a)) (not (fp.isNormal a))))
  Node C4 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::FP_IS_ZERO, {fpneg_a}),
       d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NORMAL, {a})})});
  // (define-fun b5 () Bool (not (fp.isInfinite b)))
  Node C5 = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_INF, {b})});

  Node B = utils::mk_nary(d_nm, Kind::AND, {C0, C1, C2, C3, C4, C5});

  test_get_interpolant({A0, A1, A2, A3, A4, A5, A6, A7, A8}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_quant1)
{
  Type btype = d_nm.mk_bool_type();
  Node x     = d_nm.mk_var(btype, "x");
  Node y     = d_nm.mk_var(btype, "y");
  Node z     = d_nm.mk_var(d_nm.mk_bv_type(2), "z");
  // (exists ((x Bool) (y Bool)) (not (and x y)))
  Node A = d_nm.mk_node(
      Kind::EXISTS,
      {x,
       d_nm.mk_node(
           Kind::EXISTS,
           {y, d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::AND, {x, y})})})});
  // (exists ((z (_ BitVec 2))) (= (bvmul z #b10) #b11))
  Node B =
      d_nm.mk_node(
          Kind::EXISTS,
          {z,
           d_nm.mk_node(
               Kind::EQUAL,
               {d_nm.mk_node(Kind::BV_MUL,
                             {z, d_nm.mk_value(BitVector::from_ui(2, 2))}),
                d_nm.mk_value(BitVector::from_ui(2, 3))})});
  test_get_interpolant({A}, {B});
}

TEST_F(TestBvInterpolationSolver, interpol_quant2)
{
  Type bv32 = d_nm.mk_bv_type(32);
  Node c    = d_nm.mk_const(bv32, "c");
  Node c_   = d_nm.mk_const(bv32, "c_");
  Node m    = d_nm.mk_const(bv32, "m");
  Node mm   = d_nm.mk_var(bv32, "mm");

  // (and (bvsle c_ (_ bv4 32)) (bvsle m (_ bv0 32)))
  Node A = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::BV_SLE,
                    {c_, d_nm.mk_value(BitVector::from_ui(32, 4))}),
       d_nm.mk_node(Kind::BV_SLE, {m, d_nm.mk_value(BitVector::mk_zero(32))})});
  // (or
  //    false
  //    (forall ((m (_ BitVec 32)))
  //      (and (bvsle c_ (bvmul m (_ bv2 32)))
  //           (bvsle m (_ bv1 32))
  //           (bvsle m c))))
  Node B = d_nm.mk_node(
          Kind::OR,
          {d_nm.mk_value(false),
           d_nm.mk_node(
               Kind::FORALL,
               {mm,
                utils::mk_nary(
                    d_nm,
                    Kind::AND,
                    {d_nm.mk_node(
                         Kind::BV_SLE,
                         {c_,
                          d_nm.mk_node(
                              Kind::BV_MUL,
                              {mm, d_nm.mk_value(BitVector::from_ui(32, 2))})}),
                     d_nm.mk_node(Kind::BV_SLE,
                                  {mm, d_nm.mk_value(BitVector::mk_one(32))}),
                     d_nm.mk_node(Kind::BV_SLE, {mm, c})})})});
  test_get_interpolant({A}, B);
}
#endif
}  // namespace bzla::test
