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
  constexpr static bool s_test_internal   = true;
  constexpr static bool s_test_cadicraig  = true;
  constexpr static bool s_all_pp_rw       = true;

  void SetUp() override
  {
    d_options.bv_solver.set_str("bitblast");
    d_options.produce_interpolants.set(true);
    d_options.dbg_check_interpolant.set(true);
    d_options.log_level.set(0);
    d_options.tmp_interpol_use_cadicraig.set(false);
    d_options.interpolation_auto_label.set(false);
  }

  void test_get_interpolant(const std::vector<Node>& A, const Node& C)
  {
    // check if (and A (not C)) is unsat
    option::Options opts_solve;
    sat::SatSolverFactory sat_factory(opts_solve);
    SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
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
    if (s_test_internal)
    {
      test_get_interpolant_aux(A, C, true);
    }
    if (s_test_cadicraig)
    {
      test_get_interpolant_aux(A, C, false);
    }
  }

  void test_get_interpolant_aux(const std::vector<Node>& A,
                                const Node& C,
                                bool internal)
  {
    if (d_options.log_level())
    {
      std::cout << std::endl
                << ">>>>> get interpolant with "
                << (internal ? "INTERNAL" : "CaDiCraig") << std::endl;
    }
    // get interpolant
    test_get_interpolant_aux(
        true, d_options.rewrite_level.dflt(), A, C, internal);

    if (s_all_pp_rw)
    {
      // get_interpolant when preprocessing is disabled
      test_get_interpolant_aux(
          false, d_options.rewrite_level.dflt(), A, C, internal);
      // get_interpolant when rewriting is disabled
      test_get_interpolant_aux(true, 0, A, C, internal);
      // get_interpolant when preprocessing and rewriting is disabled
      test_get_interpolant_aux(false, 0, A, C, internal);
    }
  }

  void test_get_interpolant_aux(bool pp,
                                uint64_t rwl,
                                const std::vector<Node>& A,
                                const Node& C,
                                bool internal)
  {
    if (d_options.log_level())
    {
      std::cout << std::endl
                << ">> rewrite level: " << rwl
                << "  pp: " << (pp ? "enabled" : "disabled") << std::endl;
    }
    d_options.preprocess.set(pp);
    d_options.rewrite_level.set(rwl);
    d_options.tmp_interpol_use_cadicraig.set(!internal);
    sat::SatSolverFactory sat_factory(d_options);
    SolvingContext ctx(d_nm, d_options, sat_factory);
    for (const auto& a : A)
    {
      ctx.assert_formula(a);
    }
    Node interpolant = ctx.get_interpolant(C);
    ASSERT_FALSE(interpolant.is_null());
  }

  option::Options d_options;
  NodeManager d_nm;
};

// test with other SAT solver
// error tests with prop solver, solve, unsat cores, value

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
  ASSERT_DEATH(ctx.get_interpolant(d_nm.mk_const(d_nm.mk_bool_type())),
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
      ctx.get_interpolant(d_nm.mk_const(d_nm.mk_bool_type())));
}

TEST_F(TestBvInterpolationSolver, preprop)
{
  option::Options options;
  options.bv_solver.set_str("preprop");
  options.produce_interpolants.set(true);
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ASSERT_NO_FATAL_FAILURE(
      ctx.get_interpolant(d_nm.mk_const(d_nm.mk_bool_type())));
}

TEST_F(TestBvInterpolationSolver, bool_conj)
{
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ASSERT_DEATH(ctx.get_interpolant(d_nm.mk_const(d_nm.mk_bv_type(8))),
               "is_bool");
}

TEST_F(TestBvInterpolationSolver, not_unsat1)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node C = x;
  // check if (and A (not C)) is unsat
  {
    option::Options opts_solve;
    sat::SatSolverFactory sat_factory(opts_solve);
    SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
    ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
    ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  }
  // (and A (not C)) not unsat
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ASSERT_EQ(ctx.get_interpolant(C), Node());
}

TEST_F(TestBvInterpolationSolver, not_unsat2)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node A = d_nm.mk_node(Kind::NOT, {x});
  Node C = x;
  // check if (and A (not C)) is unsat
  {
    option::Options opts_solve;
    sat::SatSolverFactory sat_factory(opts_solve);
    SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
    ctx_solve.assert_formula(A);
    ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
    ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  }
  // (and A (not C)) not unsat
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(A);
  ASSERT_EQ(ctx.get_interpolant(C), Node());
}

TEST_F(TestBvInterpolationSolver, not_unsat3)
{
  Node x = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node A = x;
  Node C = d_nm.mk_node(Kind::NOT, {x});
  // check if (and A (not C)) is unsat
  {
    option::Options opts_solve;
    sat::SatSolverFactory sat_factory(opts_solve);
    SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
    ctx_solve.assert_formula(A);
    ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
    ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  }
  // (and A (not C)) not unsat
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(A);
  ASSERT_EQ(ctx.get_interpolant(C), Node());
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
  Node C = d_nm.mk_node(Kind::BV_UGE, {x, y});
  // check if (and A (not C)) is unsat
  {
    option::Options opts_solve;
    sat::SatSolverFactory sat_factory(opts_solve);
    SolvingContext ctx_solve = SolvingContext(d_nm, opts_solve, sat_factory);
    ctx_solve.assert_formula(A);
    ctx_solve.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
    ASSERT_EQ(ctx_solve.solve(), Result::SAT);
  }
  // (and A (not C)) not unsat
  sat::SatSolverFactory sat_factory(d_options);
  SolvingContext ctx(d_nm, d_options, sat_factory);
  ctx.assert_formula(A);
  ASSERT_EQ(ctx.get_interpolant(C), Node());
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

TEST_F(TestBvInterpolationSolver, interpol8)
{
  Type bv16 = d_nm.mk_bv_type(16);
  Node x    = d_nm.mk_const(bv16, "x");
  Node y    = d_nm.mk_const(bv16, "y");
  Node zero = d_nm.mk_value(BitVector::mk_zero(16));
  Node one  = d_nm.mk_value(BitVector::mk_one(16));
  Node two  = d_nm.mk_value(BitVector::from_ui(16, 2));
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
  // (distinct (_ bv0 16) (bvadd x (_ bv1 16)))
  Node C = d_nm.mk_node(Kind::DISTINCT,
                        {zero, d_nm.mk_node(Kind::BV_ADD, {x, one})});

  test_get_interpolant({A0, A1}, C);
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
  // (bvult
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
  Node C = d_nm.mk_node(
      Kind::BV_ULT,
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

  test_get_interpolant({A0}, C);
}

TEST_F(TestBvInterpolationSolver, interpol10)
{
  Type bv4   = d_nm.mk_bv_type(4);
  Node x     = d_nm.mk_const(bv4, "x");
  Node s     = d_nm.mk_const(bv4, "s");
  Node t     = d_nm.mk_const(bv4, "t");
  Node val_x = d_nm.mk_value(BitVector::from_ui(4, 3));
  Node val_s = d_nm.mk_value(BitVector::from_ui(4, 2));
  Node val_t = d_nm.mk_value(BitVector::from_ui(4, 6));
  Node A0 =
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND,
                                 {
                                     d_nm.mk_node(Kind::EQUAL, {x, val_x}),
                                     d_nm.mk_node(Kind::EQUAL, {s, val_s}),
                                 }),
                    d_nm.mk_node(Kind::EQUAL, {t, val_t})});
  Node C = d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_MUL, {x, s}), t});
  test_get_interpolant({A0}, C);
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
  // Node A0 = d_nm.mk_node(Kind::OR, {or0, or1});
  // Node A0 = or0;
  Node C = d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_MUL, {x, s}), t});
  test_get_interpolant({A0}, C);
}

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
  Node C  = d_nm.mk_node(Kind::EQUAL, {a4, a5});

  test_get_interpolant({A0, A1, A2}, C);
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
  // (assert (= (select a #b0) #b0))
  Node A0 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {a, zero}), zero});
  // (assert (= (select b #b0) #b0))
  Node A1 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {b, zero}), zero});
  // (assert (distinct a b))
  Node A2 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  // (assert (= (select a #b1) #b0))
  Node C0 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {a, one}), zero});
  // (assert (= (select b #b1) #b0))
  Node C1 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::SELECT, {b, one}), zero});

  Node C = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::AND, {C0, C1})});

  test_get_interpolant({A0, A1, A2}, C);
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
  //(assert (! (= (select a (_ bv1 3)) (select b (_ bv1 3))) :named a0))
  Node A0 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, one}),
                          d_nm.mk_node(Kind::SELECT, {b, one})});
  //(assert (! (= (select a (_ bv3 3)) (select b (_ bv3 3))) :named a1))
  Node A1 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, three}),
                          d_nm.mk_node(Kind::SELECT, {b, three})});
  //(assert (! (= (select a (_ bv5 3)) (select b (_ bv5 3))) :named a2))
  Node A2 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, five}),
                          d_nm.mk_node(Kind::SELECT, {b, five})});
  //(assert (! (= (select a (_ bv7 3)) (select b (_ bv7 3))) :named a3))
  Node A3 = d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::SELECT, {a, seven}),
                          d_nm.mk_node(Kind::SELECT, {b, seven})});
  //(assert (! (not (= a b)) :named a4))
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
  Node C  = d_nm.mk_node(Kind::NOT,
                         {utils::mk_nary(d_nm, Kind::AND, {C0, C1, C2, C3})});
  option::Options options;
  sat::SatSolverFactory sat_factory(options);
  SolvingContext ctx = SolvingContext(d_nm, options, sat_factory);
  ctx.assert_formula(A0);
  ctx.assert_formula(A1);
  ctx.assert_formula(A2);
  ctx.assert_formula(A3);
  ctx.assert_formula(A4);
  ctx.assert_formula(d_nm.mk_node(Kind::NOT, {C}));
  assert(ctx.solve() == Result::UNSAT);
  test_get_interpolant({A0, A1, A2, A3, A4}, C);
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

  // (assert (distinct a b))
  Node A0 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  // (assert (distinct (select h a) (select hh a)))
  Node A1 = d_nm.mk_node(Kind::DISTINCT,
                         {d_nm.mk_node(Kind::SELECT, {h, a}),
                          d_nm.mk_node(Kind::SELECT, {hh, a})});
  // (assert (distinct (select h b) (select hh b)))
  Node C = d_nm.mk_node(Kind::EQUAL,
                        {d_nm.mk_node(Kind::SELECT, {h, b}),
                         d_nm.mk_node(Kind::SELECT, {hh, b})});
  test_get_interpolant({A0, A1}, C);
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

  // (assert (= hh (store h i e)))
  Node A =
      d_nm.mk_node(Kind::EQUAL, {hh, d_nm.mk_node(Kind::STORE, {h, i, e})});
  // (assert (distinct a b))
  Node B0 = d_nm.mk_node(Kind::DISTINCT, {a, b});
  // (assert (distinct (select h a) (select hh a)))
  Node B1 = d_nm.mk_node(Kind::DISTINCT,
                         {d_nm.mk_node(Kind::SELECT, {h, a}),
                          d_nm.mk_node(Kind::SELECT, {hh, a})});
  // (assert (distinct (select h b) (select hh b)))
  Node B2 = d_nm.mk_node(Kind::DISTINCT,
                         {d_nm.mk_node(Kind::SELECT, {h, b}),
                          d_nm.mk_node(Kind::SELECT, {hh, b})});
  Node C =
      d_nm.mk_node(Kind::NOT, {utils::mk_nary(d_nm, Kind::AND, {B0, B1, B2})});
  test_get_interpolant({A}, C);
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
  // (assert (not (fp.isNaN b)))
  Node A0 = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NAN, {b})});
  // (assert (not (fp.isNegative b)))
  Node A1 = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NEG, {b})});
  // (assert (fp.isPositive b))
  Node A2 = d_nm.mk_node(Kind::FP_IS_POS, {b});
  // (assert (and (fp.leq a a) (not (fp.lt a a))))
  Node A3 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::FP_LEQ, {a, a}),
       d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_LT, {a, a})})});
  // (assert (and
  //           (fp.geq (fp.sqrt RNE a) (fp.roundToIntegral RNE b))
  //           (not (fp.gt (fp.add RNA a a) b))))
  Node A4 = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::FP_GEQ,
                    {d_nm.mk_node(Kind::FP_SQRT, {rne, a}),
                     d_nm.mk_node(Kind::FP_RTI, {rne, b})}),
       d_nm.mk_node(
           Kind::NOT,
           {d_nm.mk_node(Kind::FP_GT,
                         {d_nm.mk_node(Kind::FP_ADD, {rna, a, a}), b})})});
  // (assert (fp.geq (fp.add RTN a b) (fp.sub RTN a b)))
  Node A5 = d_nm.mk_node(Kind::FP_GEQ,
                         {d_nm.mk_node(Kind::FP_ADD, {rtn, a, b}),
                          d_nm.mk_node(Kind::FP_SUB, {rtn, a, b})});
  // (assert (fp.leq (fp.mul RTP a (_ +zero 5 11)) (_ -zero 5 11)))
  Node A6 = d_nm.mk_node(
      Kind::FP_LEQ,
      {d_nm.mk_node(Kind::FP_MUL, {rtp, a, fpposzero}), fpnegzero});
  // (assert (fp.isNaN (fp.div RTP a (_ +zero 5 11))))
  Node A7 = d_nm.mk_node(Kind::FP_IS_NAN,
                         {d_nm.mk_node(Kind::FP_DIV, {rtp, a, fpposzero})});
  // (assert (= (fp.add rm (fp.mul RTZ a b) a) (fp.fma RTZ a b (fp.rem a b))))
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

  Node C = d_nm.mk_node(
      Kind::NOT, {utils::mk_nary(d_nm, Kind::AND, {C0, C1, C2, C3, C4, C5})});

  test_get_interpolant({A0, A1, A2, A3, A4, A5, A6, A7, A8}, C);
}

TEST_F(TestBvInterpolationSolver, interpol_quant1)
{
  Type btype = d_nm.mk_bool_type();
  Node x     = d_nm.mk_var(btype, "x");
  Node y     = d_nm.mk_var(btype, "y");
  Node z     = d_nm.mk_var(d_nm.mk_bv_type(2), "z");
  // (assert (exists ((x Bool) (y Bool)) (not (and x y))))
  Node A = d_nm.mk_node(
      Kind::EXISTS,
      {x,
       d_nm.mk_node(
           Kind::EXISTS,
           {y, d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::AND, {x, y})})})});
  // (assert (exists ((z (_ BitVec 2))) (= (bvmul z #b10) #b11)))
  Node C = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EXISTS,
          {z,
           d_nm.mk_node(
               Kind::EQUAL,
               {d_nm.mk_node(Kind::BV_MUL,
                             {z, d_nm.mk_value(BitVector::from_ui(2, 2))}),
                d_nm.mk_value(BitVector::from_ui(2, 3))})})});
  test_get_interpolant({A}, C);
}

TEST_F(TestBvInterpolationSolver, interpol_quant2)
{
  Type bv32 = d_nm.mk_bv_type(32);
  Node c    = d_nm.mk_const(bv32, "c");
  Node c_   = d_nm.mk_const(bv32, "c_");
  Node m    = d_nm.mk_const(bv32, "m");
  Node mm   = d_nm.mk_var(bv32, "mm");

  // (assert (and (bvsle c_ (_ bv4 32)) (bvsle m (_ bv0 32))))
  Node A = d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::BV_SLE,
                    {c_, d_nm.mk_value(BitVector::from_ui(32, 4))}),
       d_nm.mk_node(Kind::BV_SLE, {m, d_nm.mk_value(BitVector::mk_zero(32))})});
  // (assert (or
  //    false
  //    (forall ((m (_ BitVec 32)))
  //      (and (bvsle c_ (bvmul m (_ bv2 32)))
  //           (bvsle m (_ bv1 32))
  //           (bvsle m c)))))
  Node C = d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
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
                     d_nm.mk_node(Kind::BV_SLE, {mm, c})})})})});
  test_get_interpolant({A}, C);
}
}  // namespace bzla::test
