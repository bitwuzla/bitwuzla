/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <iostream>

#include "node/node_manager.h"
#include "sat/sat_solver_factory.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;

class TestBvInterpolationSolver : public TestCommon
{
 protected:
  void SetUp() override
  {
    d_options.bv_solver.set_str("bitblast");
    d_options.produce_interpolants.set(true);
    d_options.dbg_check_interpolant.set(true);
    d_options.log_level.set(0);
    d_sat_factory.reset(new sat::SatSolverFactory(d_options));
    d_ctx.reset(new SolvingContext(d_nm, d_options, *d_sat_factory));
  }

  void test_get_interpolant(const std::vector<Node>& A, const Node& C)
  {
    // check if (and A (not C)) is unsat
    option::Options opts_solve;
    SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, *d_sat_factory);
    for (const auto& a : A)
    {
      ctx_solve.assert_formula(a);
    }
    ASSERT_EQ(ctx_solve.solve(), Result::SAT);
    ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
    ASSERT_EQ(ctx_solve.solve(), Result::UNSAT);
    test_get_interpolant_aux(A, C);
  }

  void test_get_interpolant_aux(const std::vector<Node>& A, const Node& C)
  {
    // get interpolant
    {
      d_options.preprocess.set(true);
      d_options.rewrite_level.set(d_options.rewrite_level.dflt());
      SolvingContext ctx = SolvingContext(d_nm, d_options, *d_sat_factory);
      d_ctx->get_interpolant(A, C);
    }
    // get_interpolant when preprocessing is disabled
    {
      d_options.preprocess.set(false);
      d_options.rewrite_level.set(d_options.rewrite_level.dflt());
      SolvingContext ctx = SolvingContext(d_nm, d_options, *d_sat_factory);
      d_ctx->get_interpolant(A, C);
    }
    // get_interpolant when rewriting is disabled
    {
      d_options.preprocess.set(true);
      d_options.rewrite_level.set(0);
      SolvingContext ctx = SolvingContext(d_nm, d_options, *d_sat_factory);
      d_ctx->get_interpolant(A, C);
    }
    // get_interpolant when preprocessing and rewriting is disabled
    {
      d_options.preprocess.set(false);
      d_options.rewrite_level.set(0);
      SolvingContext ctx = SolvingContext(d_nm, d_options, *d_sat_factory);
      d_ctx->get_interpolant(A, C);
    }
  }

  option::Options d_options;
  NodeManager d_nm;
  std::unique_ptr<sat::SatSolverFactory> d_sat_factory;
  std::unique_ptr<SolvingContext> d_ctx;
};

// test with other SAT solver
// error tests with prop solver, solve, unsat cores, value

TEST_F(TestBvInterpolationSolver, solve)
{
  ASSERT_DEATH(d_ctx->solve(), "!d_produce_interpolants");
}

TEST_F(TestBvInterpolationSolver, produce_interpolants)
{
  d_options.produce_interpolants.set(false);
  SolvingContext ctx = SolvingContext(d_nm, d_options, *d_sat_factory);
  ASSERT_DEATH(ctx.get_interpolant({}, d_nm.mk_const(d_nm.mk_bool_type())),
               "produce_interpolants");
}

TEST_F(TestBvInterpolationSolver, prop)
{
  option::Options options;
  options.bv_solver.set_str("prop");
  options.produce_interpolants.set(true);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ASSERT_NO_FATAL_FAILURE(
      ctx.get_interpolant({}, d_nm.mk_const(d_nm.mk_bool_type())));
}

TEST_F(TestBvInterpolationSolver, preprop)
{
  option::Options options;
  options.bv_solver.set_str("preprop");
  options.produce_interpolants.set(true);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ASSERT_NO_FATAL_FAILURE(
      ctx.get_interpolant({}, d_nm.mk_const(d_nm.mk_bool_type())));
}

TEST_F(TestBvInterpolationSolver, bool_conj)
{
  ASSERT_DEATH(d_ctx->get_interpolant({}, d_nm.mk_const(d_nm.mk_bv_type(8))),
               "is_bool");
}

TEST_F(TestBvInterpolationSolver, not_unsat1)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  std::vector<Node> A;
  Node C = x;
  // check if (and A (not C)) is unsat
  option::Options opts_solve;
  sat::SatSolverFactory sat_factory(opts_solve);
  SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
  ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
  ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  // (and A (not C)) not unsat
  ASSERT_EQ(d_ctx->get_interpolant(A, C), Node());
}

TEST_F(TestBvInterpolationSolver, not_unsat2)
{
  Node x              = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  std::vector<Node> A = {d_nm.mk_node(Kind::NOT, {x})};
  Node C              = x;
  // check if (and A (not C)) is unsat
  option::Options opts_solve;
  sat::SatSolverFactory sat_factory(opts_solve);
  SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
  ctx_solve.assert_formula(A[0]);
  ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
  ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  // (and A (not C)) not unsat
  ASSERT_EQ(d_ctx->get_interpolant(A, C), Node());
}

TEST_F(TestBvInterpolationSolver, not_unsat3)
{
  Node x              = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  std::vector<Node> A = {x};
  Node C              = d_nm.mk_node(Kind::NOT, {x});
  // check if (and A (not C)) is unsat
  option::Options opts_solve;
  sat::SatSolverFactory sat_factory(opts_solve);
  SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
  ctx_solve.assert_formula(A[0]);
  ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
  ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  // (and A (not C)) not unsat
  ASSERT_EQ(d_ctx->get_interpolant(A, C), Node());
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
  std::vector<Node> A = {d_nm.mk_node(Kind::OR, {or0, or1})};
  Node C              = d_nm.mk_node(Kind::BV_UGE, {x, y});
  // check if (and A (not C)) is unsat
  option::Options opts_solve;
  sat::SatSolverFactory sat_factory(opts_solve);
  SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
  ctx_solve.assert_formula(A[0]);
  ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
  ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  // (and A (not C)) not unsat
  ASSERT_EQ(d_ctx->get_interpolant(A, C), Node());
}

TEST_F(TestBvInterpolationSolver, interpol1)
{
  Node x              = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  std::vector<Node> A = {d_nm.mk_node(Kind::NOT, {x})};
  Node C              = d_nm.mk_node(Kind::NOT, {x});
  test_get_interpolant(A, C);
}

TEST_F(TestBvInterpolationSolver, interpol2)
{
  Node x              = d_nm.mk_const(d_nm.mk_bool_type());
  Node y              = d_nm.mk_const(d_nm.mk_bool_type());
  std::vector<Node> A = {x, d_nm.mk_node(Kind::NOT, {x})};
  Node C              = d_nm.mk_node(Kind::NOT, {y});
  // check if (and A (not C)) is unsat (A is already unsat)
  option::Options opts_solve;
  sat::SatSolverFactory sat_factory(opts_solve);
  SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
  ctx_solve.assert_formula(A[0]);
  ctx_solve.assert_formula(A[1]);
  ASSERT_EQ(ctx_solve.solve(), Result::UNSAT);
  ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
  ASSERT_EQ(ctx_solve.solve(), Result::UNSAT);
  test_get_interpolant_aux(A, C);
}

TEST_F(TestBvInterpolationSolver, interpol3)
{
  Type bv1    = d_nm.mk_bv_type(1);
  Node x      = d_nm.mk_const(bv1);
  Node y      = d_nm.mk_const(bv1);
  Node one    = d_nm.mk_value(BitVector::mk_true());
  Node zero   = d_nm.mk_value(BitVector::mk_false());
  Node bvnoty = d_nm.mk_node(Kind::BV_NOT, {y});

  // (= x (bvnot y))
  Node A0 = d_nm.mk_node(Kind::EQUAL, {x, bvnoty});
  // (= #b0 (bvnot y))
  Node A1 = d_nm.mk_node(Kind::EQUAL, {zero, bvnoty});
  // (not (and (bvult x (bvnot y)) (= (bvnot y) #b0)))
  Node C =
      d_nm.mk_node(Kind::NOT,
                   {d_nm.mk_node(Kind::AND,
                                 {d_nm.mk_node(Kind::BV_ULT, {x, bvnoty}),
                                  d_nm.mk_node(Kind::EQUAL, {bvnoty, zero})})});

  test_get_interpolant({A0, A1}, C);
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

  // (distinct s0 goal)
  Node C = d_nm.mk_node(Kind::DISTINCT, {s0, goal});

  test_get_interpolant({A0, A1, A2}, C);
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
  // (= x (_ bv0 6))
  Node C = d_nm.mk_node(Kind::EQUAL, {x, d_nm.mk_value(BitVector::mk_zero(6))});

  test_get_interpolant({A0, A1}, C);
}

TEST_F(TestBvInterpolationSolver, interpol6)
{
  Type bv4  = d_nm.mk_bv_type(4);
  Node x    = d_nm.mk_const(bv4, "x");
  Node y    = d_nm.mk_const(bv4, "y");
  Node z    = d_nm.mk_const(bv4, "z");
  Node zero = d_nm.mk_value(BitVector::mk_zero(4));
  Node one  = d_nm.mk_value(BitVector::mk_one(4));
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
  // (not
  //   (and
  //     (distinct z (_ bv0 1024))
  //     (= (bvand z (bvsub z (_ bv1 1024))) (_ bv0 1024))))
  Node C = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::DISTINCT, {z, zero}),
           d_nm.mk_node(
               Kind::EQUAL,
               {d_nm.mk_node(Kind::BV_AND,
                             {z, d_nm.mk_node(Kind::BV_SUB, {z, one})}),
                zero})})});

  test_get_interpolant({A0, A1, A2, A3}, C);
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
  // (not (bvugt c b))
  Node C = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::BV_UGT, {c, b})});

  test_get_interpolant({A0, A1}, C);
}

}  // namespace bzla::test
